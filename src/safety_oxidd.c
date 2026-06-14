// safety_oxidd.c — in-process safety-game solver on OxiDD BDDs.
//
// Replaces the AbsSynthe subprocess solve step (`run_abssynthe_game`): compile
// the `Aig` game's cones into BDDs, run the controllable-predecessor (`cpre`)
// safety fixpoint, and extract a Skolem strategy back into an `Aig`.  See
// `architecture.md` §4.  Only built when the OxiDD feature is enabled.
//
// Conventions (matching the game encoders in main_tlsfcompose.c):
//   * env moves first / Mealy: cpre(Z)(s) = ∀u ∃c [ ¬bad ∧ Z[s := next] ];
//   * inputs whose name starts with `controllable_` are the controllable (c)
//     moves, the rest are uncontrollable (u);
//   * output `bad` is the unsafe predicate; latches are state, reset 0/1;
//   * realizable iff the greatest fixpoint W holds at the latch reset cube.
//
// Memory: OxiDD operations do not take ownership of their `oxidd_bdd_t`
// arguments and return a *new* reference; every returned handle must be
// `oxidd_bdd_unref`'d (unref is a no-op on the invalid/NULL handle).  On
// out-of-memory an operation returns an invalid handle (`_p == NULL`) rather
// than aborting, so we check validity before the FFI calls that would panic on
// it (`eval`/`valid`/`satisfiable`) and otherwise degrade to a sound caller
// fallback.  Shared BDD helpers (memo, lit/cube builders, bdd2aig) live in
// oxidd_common.c.

#include "tlsf/safety_oxidd.h"

#include "tlsf/oxidd_common.h"

#include <stdlib.h>

// Per-call BDD manager sizing.  Clusters are small post-decomposition; a game
// that overflows this returns invalid handles and the caller falls back to
// ltlsynt (sound).  Single worker thread: the games are tiny and the thread
// pool would only add per-call overhead (parallelism across clusters is a
// later, separate lever).
#define OXIDD_INNER_CAP (1u << 18)
#define OXIDD_CACHE_CAP (1u << 18)

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

Aig *solve_safety_oxidd(Aig *game, int *unreal) {
  *unreal = 0;
  if (!game)
    return nullptr;

  uint32_t nin = aig_num_inputs(game);
  uint32_t nlat = aig_num_latches(game);
  uint32_t nand = aig_num_ands(game);

  // Highest AIG variable, to size the literal -> BDD map.
  uint32_t maxvar = 0;
  for (uint32_t i = 0; i < nin; i++) {
    uint32_t lit;
    aig_input_name(game, i, &lit);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  for (uint32_t i = 0; i < nlat; i++) {
    uint32_t cur;
    aig_latch_at(game, i, &cur, nullptr, nullptr);
    if (cur / 2 > maxvar)
      maxvar = cur / 2;
  }
  for (uint32_t i = 0; i < nand; i++) {
    uint32_t lhs;
    aig_and_at(game, i, &lhs, nullptr, nullptr);
    if (lhs / 2 > maxvar)
      maxvar = lhs / 2;
  }

  Aig *strat = nullptr;
  Bdd *var_bdd = calloc(maxvar + 1, sizeof *var_bdd); // AIG var -> BDD
  Bdd *next_bdd = nlat ? calloc(nlat, sizeof *next_bdd) : nullptr;
  Bdd *strat_f = nullptr; // Skolem function per controllable
  uint32_t *var2lit = calloc((size_t)nin + nlat, sizeof *var2lit);
  uint32_t *lat_lit = nlat ? calloc(nlat, sizeof *lat_lit) : nullptr;
  uint32_t *cvars =
      nin ? calloc(nin, sizeof *cvars) : nullptr; // controllable var idx
  uint32_t *uvars =
      nin ? calloc(nin, sizeof *uvars) : nullptr; // uncontrollable var idx
  uint32_t *cinput =
      nin ? calloc(nin, sizeof *cinput) : nullptr; // controllable input index
  if (!var_bdd || (nlat && !next_bdd) || !var2lit ||
      (nin && (!cvars || !uvars))) {
    free(var_bdd);
    free(next_bdd);
    free(var2lit);
    free(lat_lit);
    free(cvars);
    free(uvars);
    free(cinput);
    aig_free(game);
    return nullptr;
  }

  oxidd_bdd_manager_t m =
      oxidd_bdd_manager_new(OXIDD_INNER_CAP, OXIDD_CACHE_CAP, 1);
  oxidd_bdd_manager_add_vars(m, nin + nlat);

  Bdd bad = {0}, notbad = {0}, Z = {0}, M = {0}, ctrl_cube = {0},
      unc_cube = {0};
  oxidd_bdd_substitution_t *sub_lat = nullptr;
  uint32_t ncv = 0, nuv = 0;
  bool ok = true;

  // Variables: input p -> bdd var p; latch j -> bdd var nin+j.
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *name = aig_input_name(game, p, &lit);
    var_bdd[lit / 2] = oxidd_bdd_var(m, p);
    if (is_controllable(name)) {
      cvars[ncv] = p;
      cinput[ncv] = p;
      ncv++;
    } else {
      uvars[nuv++] = p;
    }
  }
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur;
    aig_latch_at(game, j, &cur, nullptr, nullptr);
    var_bdd[cur / 2] = oxidd_bdd_var(m, nin + j);
  }

  // And-gates in construction (topological) order.
  for (uint32_t i = 0; i < nand && ok; i++) {
    uint32_t lhs, r0, r1;
    aig_and_at(game, i, &lhs, &r0, &r1);
    Bdd a = lit_to_bdd(m, var_bdd, r0);
    Bdd b = lit_to_bdd(m, var_bdd, r1);
    Bdd c = oxidd_bdd_and(a, b);
    oxidd_bdd_unref(a);
    oxidd_bdd_unref(b);
    var_bdd[lhs / 2] = c;
    if (bdd_invalid(c))
      ok = false;
  }

  // bad and the latch next-functions.
  if (ok) {
    uint32_t badlit = aig_output_lit(game, "bad");
    bad = (badlit == UINT32_MAX) ? oxidd_bdd_false(m)
                                 : lit_to_bdd(m, var_bdd, badlit);
    notbad = oxidd_bdd_not(bad);
    if (bdd_invalid(notbad))
      ok = false;
  }
  for (uint32_t j = 0; j < nlat && ok; j++) {
    uint32_t next;
    aig_latch_at(game, j, nullptr, &next, nullptr);
    next_bdd[j] = lit_to_bdd(m, var_bdd, next);
    if (bdd_invalid(next_bdd[j]))
      ok = false;
  }

  // Latch substitution s_j := next_j, reused for the fixpoint and for W[next].
  if (ok) {
    sub_lat = oxidd_bdd_substitution_new(nlat);
    for (uint32_t j = 0; j < nlat; j++)
      oxidd_bdd_substitution_add_pair(sub_lat, nin + j, next_bdd[j]);
    ctrl_cube = cube_of(m, cvars, ncv);
    unc_cube = cube_of(m, uvars, nuv);
    if (!sub_lat || bdd_invalid(ctrl_cube) || bdd_invalid(unc_cube))
      ok = false;
  }

  // Greatest fixpoint W = νZ. ∀u ∃c [ ¬bad ∧ Z[s := next] ], from Z₀ = ⊤.
  if (ok) {
    Z = oxidd_bdd_true(m);
    for (;;) {
      Bdd img = oxidd_bdd_substitute(Z, sub_lat);
      Bdd t = oxidd_bdd_and(notbad, img);
      Bdd ec = oxidd_bdd_exists(t, ctrl_cube);
      Bdd au = oxidd_bdd_forall(ec, unc_cube);
      oxidd_bdd_unref(img);
      oxidd_bdd_unref(t);
      oxidd_bdd_unref(ec);
      if (bdd_invalid(au)) {
        oxidd_bdd_unref(au);
        ok = false;
        break;
      }
      bool converged = bdd_eq(au, Z);
      oxidd_bdd_unref(Z);
      Z = au;
      if (converged)
        break;
    }
  }

  // Realizable iff W holds at the latch reset cube (W is over state vars only).
  if (ok) {
    oxidd_var_no_bool_pair_t *args =
        nlat ? calloc(nlat, sizeof *args) : nullptr;
    for (uint32_t j = 0; j < nlat; j++) {
      uint32_t reset;
      aig_latch_at(game, j, nullptr, nullptr, &reset);
      args[j].var = nin + j;
      args[j].val = reset != 0;
    }
    bool realizable = oxidd_bdd_eval(Z, args, nlat);
    free(args);
    if (!realizable) {
      *unreal = 1;
      ok = false; // not an error: caller trusts UNREALIZABLE / falls back
    }
  }

  // Strategy: M = ¬bad ∧ W[s := next]; sequentially Skolemise each controllable
  // c_k as f_k(state, u) = ∃(later controllables) M|_{c_k = 1}, choosing c_k =
  // 1 wherever a safe completion remains, then substituting c_k := f_k into M.
  if (ok && !*unreal) {
    Bdd wnext = oxidd_bdd_substitute(Z, sub_lat);
    M = oxidd_bdd_and(notbad, wnext);
    oxidd_bdd_unref(wnext);
    strat_f = ncv ? calloc(ncv, sizeof *strat_f) : nullptr;
    Bdd R = oxidd_bdd_ref(M);
    for (uint32_t k = 0; k < ncv && ok; k++) {
      Bdd pos = oxidd_bdd_var(m, cvars[k]);
      Bdd rk1 = oxidd_bdd_restrict(R, pos); // R|_{c_k = 1}
      Bdd rem = cube_of(m, cvars + k + 1, ncv - k - 1);
      Bdd fk = oxidd_bdd_exists(rk1, rem); // over (state, u)
      oxidd_bdd_unref(pos);
      oxidd_bdd_unref(rk1);
      oxidd_bdd_unref(rem);
      if (bdd_invalid(fk)) {
        oxidd_bdd_unref(fk);
        ok = false;
        break;
      }
      strat_f[k] = fk;
      oxidd_bdd_substitution_t *s1 = oxidd_bdd_substitution_new(1);
      oxidd_bdd_substitution_add_pair(s1, cvars[k], fk);
      Bdd rnew = oxidd_bdd_substitute(R, s1);
      oxidd_bdd_substitution_free(s1);
      oxidd_bdd_unref(R);
      R = rnew;
      if (bdd_invalid(R))
        ok = false;
    }
    oxidd_bdd_unref(R);
  }

  // Build the strategy AIG: uncontrollable inputs, the game's latches as
  // memory, each controllable driven by an output `controllable_<sig>`.
  if (ok && !*unreal) {
    strat = aig_new();
    for (uint32_t v = 0; v < nin + nlat; v++)
      var2lit[v] = UINT32_MAX;
    for (uint32_t p = 0; p < nin; p++) {
      uint32_t lit;
      const char *name = aig_input_name(game, p, &lit);
      if (!is_controllable(name))
        var2lit[p] = aig_input(strat, name); // controllables stay UINT32_MAX
    }
    for (uint32_t j = 0; j < nlat; j++) {
      uint32_t reset;
      aig_latch_at(game, j, nullptr, nullptr, &reset);
      lat_lit[j] = aig_latch(strat, AIG_FALSE, reset);
      var2lit[nin + j] = lat_lit[j];
    }

    Bdd2Aig ctx = {strat, var2lit, {0}, false};

    // Controllable outputs.
    for (uint32_t k = 0; k < ncv; k++) {
      uint32_t lit;
      const char *name = aig_input_name(game, cinput[k], &lit);
      uint32_t out = bdd2aig(&ctx, strat_f[k]);
      aig_set_output(strat, name, out);
    }
    // Latch next-functions, with the controllables substituted by their f_k.
    oxidd_bdd_substitution_t *sc =
        ncv ? oxidd_bdd_substitution_new(ncv) : nullptr;
    for (uint32_t k = 0; k < ncv; k++)
      oxidd_bdd_substitution_add_pair(sc, cvars[k], strat_f[k]);
    for (uint32_t j = 0; j < nlat && !ctx.error; j++) {
      Bdd na = ncv ? oxidd_bdd_substitute(next_bdd[j], sc)
                   : oxidd_bdd_ref(next_bdd[j]);
      if (bdd_invalid(na)) {
        oxidd_bdd_unref(na);
        ctx.error = true;
        break;
      }
      uint32_t nl = bdd2aig(&ctx, na);
      oxidd_bdd_unref(na);
      aig_set_latch_next(strat, lat_lit[j], nl);
    }
    if (sc)
      oxidd_bdd_substitution_free(sc);
    memo_free(&ctx.memo);
    if (ctx.error) {
      aig_free(strat);
      strat = nullptr;
    }
  }

  // Cleanup.
  if (strat_f)
    for (uint32_t k = 0; k < ncv; k++)
      oxidd_bdd_unref(strat_f[k]);
  for (uint32_t j = 0; j < nlat; j++)
    oxidd_bdd_unref(next_bdd[j]);
  for (uint32_t v = 0; v <= maxvar; v++)
    oxidd_bdd_unref(var_bdd[v]);
  oxidd_bdd_unref(bad);
  oxidd_bdd_unref(notbad);
  oxidd_bdd_unref(Z);
  oxidd_bdd_unref(M);
  oxidd_bdd_unref(ctrl_cube);
  oxidd_bdd_unref(unc_cube);
  if (sub_lat)
    oxidd_bdd_substitution_free(sub_lat);
  oxidd_bdd_manager_unref(m);

  free(var_bdd);
  free(next_bdd);
  free(strat_f);
  free(var2lit);
  free(lat_lit);
  free(cvars);
  free(uvars);
  free(cinput);
  aig_free(game);
  return strat;
}
