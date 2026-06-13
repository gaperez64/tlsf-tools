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
// fallback.

#include "tlsf/safety_oxidd.h"

#include <oxidd/capi.h>

#include <stdlib.h>
#include <string.h>

#define CONTROLLABLE_PREFIX "controllable_"

// Per-call BDD manager sizing.  Clusters are small post-decomposition; a game
// that overflows this returns invalid handles and the caller falls back to
// ltlsynt (sound).  Single worker thread: the games are tiny and the thread
// pool would only add per-call overhead (parallelism across clusters is a
// later, separate lever).
#define OXIDD_INNER_CAP (1u << 18)
#define OXIDD_CACHE_CAP (1u << 18)

typedef oxidd_bdd_t Bdd;

static inline bool bdd_invalid(Bdd f) { return f._p == NULL; }

static bool is_controllable(const char *name) {
  return strncmp(name, CONTROLLABLE_PREFIX, strlen(CONTROLLABLE_PREFIX)) == 0;
}

// ---------------------------------------------------------------------------
// BDD node -> AIG memo (open-addressing hash on the 16-byte handle identity;
// equal BDD functions share a node, so the handle bytes are a canonical key).
// ---------------------------------------------------------------------------

typedef struct {
  Bdd *keys;
  uint32_t *lits;
  bool *used;
  size_t cap, n;
} Memo;

static uint64_t memo_hash(Bdd k) {
  const unsigned char *p = (const unsigned char *)&k;
  uint64_t h = 1469598103934665603ull;
  for (size_t i = 0; i < sizeof k; i++) {
    h ^= p[i];
    h *= 1099511628211ull;
  }
  return h;
}

static bool memo_grow(Memo *t, size_t cap) {
  Bdd *keys = calloc(cap, sizeof *keys);
  uint32_t *lits = calloc(cap, sizeof *lits);
  bool *used = calloc(cap, sizeof *used);
  if (!keys || !lits || !used) {
    free(keys);
    free(lits);
    free(used);
    return false;
  }
  for (size_t i = 0; i < t->cap; i++) {
    if (!t->used[i])
      continue;
    size_t j = memo_hash(t->keys[i]) & (cap - 1);
    while (used[j])
      j = (j + 1) & (cap - 1);
    keys[j] = t->keys[i];
    lits[j] = t->lits[i];
    used[j] = true;
  }
  free(t->keys);
  free(t->lits);
  free(t->used);
  t->keys = keys;
  t->lits = lits;
  t->used = used;
  t->cap = cap;
  return true;
}

// Returns true and sets *lit if `k` is memoised; otherwise returns false.
static bool memo_get(const Memo *t, Bdd k, uint32_t *lit) {
  if (t->cap == 0)
    return false;
  size_t j = memo_hash(k) & (t->cap - 1);
  while (t->used[j]) {
    if (memcmp(&t->keys[j], &k, sizeof k) == 0) {
      *lit = t->lits[j];
      return true;
    }
    j = (j + 1) & (t->cap - 1);
  }
  return false;
}

static bool memo_put(Memo *t, Bdd k, uint32_t lit) {
  if (t->n * 10 >= t->cap * 7) // grow at load factor 0.7
    if (!memo_grow(t, t->cap ? t->cap * 2 : 64))
      return false;
  size_t j = memo_hash(k) & (t->cap - 1);
  while (t->used[j]) {
    if (memcmp(&t->keys[j], &k, sizeof k) == 0) {
      t->lits[j] = lit;
      return true;
    }
    j = (j + 1) & (t->cap - 1);
  }
  t->keys[j] = k;
  t->lits[j] = lit;
  t->used[j] = true;
  t->n++;
  return true;
}

static void memo_free(Memo *t) {
  free(t->keys);
  free(t->lits);
  free(t->used);
  *t = (Memo){0};
}

// ---------------------------------------------------------------------------
// Small BDD helpers
// ---------------------------------------------------------------------------

// BDD for AIG literal `lit` (a new reference): 0/1 are the constants, otherwise
// the stored var-BDD `var_bdd[lit/2]`, complemented when `lit` is odd.
static Bdd lit_to_bdd(oxidd_bdd_manager_t m, const Bdd *var_bdd, uint32_t lit) {
  if (lit == AIG_FALSE)
    return oxidd_bdd_false(m);
  if (lit == AIG_TRUE)
    return oxidd_bdd_true(m);
  Bdd base = var_bdd[lit / 2];
  return (lit & 1u) ? oxidd_bdd_not(base) : oxidd_bdd_ref(base);
}

// Conjunction of the variables `vars[0..n)` as a cube BDD (⊤ when n == 0).
static Bdd cube_of(oxidd_bdd_manager_t m, const uint32_t *vars, uint32_t n) {
  Bdd cube = oxidd_bdd_true(m);
  for (uint32_t i = 0; i < n; i++) {
    Bdd v = oxidd_bdd_var(m, vars[i]);
    Bdd nx = oxidd_bdd_and(cube, v);
    oxidd_bdd_unref(cube);
    oxidd_bdd_unref(v);
    cube = nx;
  }
  return cube;
}

// True iff `a` and `b` are the same Boolean function.
static bool bdd_eq(Bdd a, Bdd b) {
  Bdd e = oxidd_bdd_equiv(a, b);
  if (bdd_invalid(e)) {
    oxidd_bdd_unref(e);
    return false;
  }
  bool r = oxidd_bdd_valid(e);
  oxidd_bdd_unref(e);
  return r;
}

// ---------------------------------------------------------------------------
// BDD -> AIG (memoised ite expansion over the strategy AIG)
// ---------------------------------------------------------------------------

typedef struct {
  Aig *strat;
  const uint32_t *var2lit; // bdd var index -> strat AIG lit (UINT32_MAX = none)
  Memo memo;
  bool error;
} Bdd2Aig;

static uint32_t bdd2aig(Bdd2Aig *ctx, Bdd f) {
  if (ctx->error)
    return AIG_FALSE;
  if (oxidd_bdd_node_level(f) == (oxidd_level_no_t)-1) // terminal
    return oxidd_bdd_satisfiable(f) ? AIG_TRUE : AIG_FALSE;
  uint32_t cached;
  if (memo_get(&ctx->memo, f, &cached))
    return cached;
  oxidd_var_no_t v = oxidd_bdd_node_var(f);
  uint32_t vlit = ctx->var2lit[v];
  if (vlit ==
      UINT32_MAX) { // a variable that must not appear (e.g. controllable)
    ctx->error = true;
    return AIG_FALSE;
  }
  Bdd t = oxidd_bdd_cofactor_true(f);
  Bdd e = oxidd_bdd_cofactor_false(f);
  uint32_t at = bdd2aig(ctx, t);
  uint32_t ae = bdd2aig(ctx, e);
  oxidd_bdd_unref(t);
  oxidd_bdd_unref(e);
  uint32_t hi = aig_and(ctx->strat, vlit, at);
  uint32_t lo = aig_and(ctx->strat, aig_not(vlit), ae);
  uint32_t res = aig_or(ctx->strat, hi, lo);
  if (!memo_put(&ctx->memo, f, res))
    ctx->error = true;
  return res;
}

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
