// safety_oxidd.c — in-process safety-game solver on OxiDD BDDs.
//
// Replaces the AbsSynthe subprocess solve step (`run_abssynthe_game`): compile
// the `Aig` game's cones into BDDs, run the controllable-predecessor (`cpre`)
// safety fixpoint, and extract a Skolem strategy back into an `Aig`.  See
// CLAUDE.md (OxiDD section).  Only built when the OxiDD feature is enabled.
//
// Conventions (matching the game encoders in tlsfcompose):
//   * env moves first / Mealy: cpre(Z)(s) = ∀u ∃c [ ¬bad ∧ Z[s := next] ];
//   * inputs whose name starts with `controllable_` are the controllable (c)
//     moves, the rest are uncontrollable (u);
//   * the unsafe predicate is selected by the resolved game profile
//     (legacy output 0 or typed bad-property OR); latches are state, reset 0/1;
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

#include "oxidd_common.h"

#include <stdio.h>
#include <stdlib.h>

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

static bool fill_initial_assignment(const Aig *game,
                                    oxidd_var_no_bool_pair_t *args,
                                    uint32_t nlat, uint32_t var_base,
                                    uint32_t nin) {
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t reset;
    uint32_t cur;
    aig_latch_at(game, j, &cur, nullptr, &reset);
    if (reset != 0 && reset != 1)
      return false;
    args[j].var = var_base + nin + j;
    args[j].val = reset != 0;
  }
  return true;
}

static bool demand_updates(OxiddRun *run, const Aig *game, uint32_t base,
                           uint32_t maxvar, Bdd *next, const bool *needed,
                           oxidd_bdd_substitution_t **sub) {
  uint32_t ni = aig_num_inputs(game), nl = aig_num_latches(game);
  uint32_t missing = 0;
  for (uint32_t j = 0; j < nl; j++)
    if ((!needed || needed[j]) && bdd_invalid(next[j]))
      missing++;
  if (!missing)
    return true;
  uint32_t *lits = calloc(missing, sizeof *lits);
  Bdd *roots = calloc(missing, sizeof *roots);
  Bdd *map = calloc((size_t)maxvar + 1, sizeof *map);
  bool ok = lits && roots && map;
  if (ok) {
    uint32_t k = 0;
    for (uint32_t j = 0; j < nl; j++)
      if ((!needed || needed[j]) && bdd_invalid(next[j]))
        aig_latch_at(game, j, NULL, &lits[k++], NULL);
    for (uint32_t i = 0; i < ni; i++) {
      uint32_t lit;
      aig_input_name(game, i, &lit);
      map[lit / 2] = oxidd_run_var(run, base + i);
    }
    for (uint32_t j = 0; j < nl; j++) {
      uint32_t lit;
      aig_latch_at(game, j, &lit, NULL, NULL);
      map[lit / 2] = oxidd_run_var(run, base + ni + j);
    }
    ok = oxidd_build_roots(run, game, map, maxvar, lits, roots, missing);
    if (ok) {
      k = 0;
      for (uint32_t j = 0; j < nl; j++)
        if ((!needed || needed[j]) && bdd_invalid(next[j])) {
          next[j] = roots[k];
          roots[k++] = (Bdd){0};
        }
      // Never mutate a used substitution. Publish a new complete generation.
      oxidd_bdd_substitution_t *fresh = oxidd_bdd_substitution_new(nl);
      if (!fresh)
        ok = false;
      else {
        uint32_t built = 0;
        for (uint32_t j = 0; j < nl; j++)
          if (!bdd_invalid(next[j])) {
            oxidd_bdd_substitution_add_pair(fresh, base + ni + j, next[j]);
            built++;
          }
        if (*sub)
          oxidd_bdd_substitution_free(*sub);
        *sub = fresh;
        oxidd_trace(
            run->options, run->phase, "demand_updates",
            ",\"new_updates\":%u,\"built_updates\":%u,\"total_updates\":%u",
            missing, built, nl);
      }
    }
  }
  if (roots)
    for (uint32_t j = 0; j < missing; j++)
      oxidd_bdd_unref(roots[j]);
  oxidd_release_var_map(map, maxvar);
  free(map);
  free(roots);
  free(lits);
  return ok;
}

static Aig *solve_safety_impl(Aig *game, int *unreal, bool *winning,
                              const OxiddSolveOptions *user_opts) {
  OxiddSolveOptions defaults = oxidd_solve_options_default();
  const OxiddSolveOptions *opts = user_opts ? user_opts : &defaults;
  *unreal = 0;
  if (opts->failure)
    *opts->failure = (OxiddFailure){0};
  if (!game)
    return nullptr;

  uint32_t nin = aig_num_inputs(game);
  uint32_t nlat = aig_num_latches(game);
  uint32_t nand = aig_num_ands(game);

  // Highest AIG variable, to size the literal -> BDD map.
  uint32_t maxvar = oxidd_max_aig_var(game);

  // Manager: reuse the session manager when active (amortises allocation cost
  // across clusters); otherwise right-size a fresh per-cluster manager.
  uint32_t nvars_local = nin + nlat;
  bool own_mgr = (oxidd_session_get()._p == NULL);
  oxidd_bdd_manager_t m;
  uint32_t var_base; // offset so this cluster's vars don't alias earlier ones
  size_t node_cap = 0, cache_cap = 0;
  OxiddResolvedOrder order = {0};
  if (own_mgr) {
    if (!oxidd_resolve_var_order(game, opts, 0, &order)) {
      aig_free(game);
      return nullptr;
    }
    node_cap = opts->node_cap ? opts->node_cap
                              : oxidd_default_capacity(nvars_local, 6);
    cache_cap = opts->cache_cap ? opts->cache_cap
                                : oxidd_default_capacity(nvars_local, 6);
    oxidd_trace(opts, "manager_create", "begin",
                ",\"node_cap\":%zu,\"cache_cap\":%zu,\"vars\":%u", node_cap,
                cache_cap, nvars_local);
    m = oxidd_bdd_manager_new(node_cap, cache_cap, 1);
    oxidd_bdd_manager_add_vars(m, nvars_local);
    var_base = 0;
    if (!oxidd_apply_var_order(m, var_base, opts, &order)) {
      oxidd_resolved_order_free(&order);
      oxidd_bdd_manager_unref(m);
      aig_free(game);
      return nullptr;
    }
    oxidd_resolved_order_free(&order);
  } else {
    if (!oxidd_var_order_is_default(opts)) {
      oxidd_record_failure(opts, OXIDD_FAILURE_CONFIGURATION, "manager_create",
                           "session_nondefault_order", 0, 0);
      aig_free(game);
      return nullptr;
    }
    m = oxidd_session_get();
    if (!oxidd_session_config(opts, &node_cap, &cache_cap)) {
      oxidd_record_failure(opts, OXIDD_FAILURE_CONFIGURATION, "manager_create",
                           "session_capacity_mismatch", 0, 0);
      oxidd_trace(opts, "manager_create", "failure",
                  ",\"reason\":\"session_capacity_mismatch\"");
      aig_free(game);
      return nullptr;
    }
    var_base = oxidd_session_alloc_vars(nvars_local);
  }

  if (var_base == UINT32_MAX) {
    aig_free(game);
    return nullptr;
  }
  OxiddRun run_state;
  OxiddRun *run = &run_state;
  oxidd_run_init(run, m, opts, node_cap, cache_cap);
  Aig *strat = nullptr;
  Bdd *var_bdd = calloc(maxvar + 1, sizeof *var_bdd); // AIG var -> BDD
  Bdd *next_bdd = nlat ? calloc(nlat, sizeof *next_bdd) : nullptr;
  Bdd *strat_f = nullptr; // Skolem function per controllable
  uint32_t *var2lit = calloc((size_t)nvars_local, sizeof *var2lit);
  uint32_t *lat_lit = nlat ? calloc(nlat, sizeof *lat_lit) : nullptr;
  uint32_t *cvars =
      nin ? calloc(nin, sizeof *cvars) : nullptr; // controllable var idx
  uint32_t *uvars =
      nin ? calloc(nin, sizeof *uvars) : nullptr; // uncontrollable var idx
  uint32_t *cinput =
      nin ? calloc(nin, sizeof *cinput) : nullptr; // controllable input index
  if (!var_bdd || (nlat && !next_bdd) || !var2lit || (nlat && !lat_lit) ||
      (nin && (!cvars || !uvars || !cinput))) {
    oxidd_record_failure(opts, OXIDD_FAILURE_HOST, "construction", "calloc", 0,
                         0);
    free(var_bdd);
    free(next_bdd);
    free(var2lit);
    free(lat_lit);
    free(cvars);
    free(uvars);
    free(cinput);
    if (own_mgr)
      oxidd_bdd_manager_unref(m);
    aig_free(game);
    return nullptr;
  }
  oxidd_trace(opts, "input", "game",
              ",\"inputs\":%u,\"latches\":%u,\"ands\":%u,"
              "\"outputs\":%u,\"bad\":%u,\"constraints\":%u",
              nin, nlat, nand, aig_num_outputs(game), aig_num_bad(game),
              aig_num_constraints(game));

  Bdd bad = {0}, notbad = {0}, Z = {0}, M = {0}, ctrl_cube = {0},
      unc_cube = {0};
  oxidd_bdd_substitution_t *sub_lat = nullptr;
  uint32_t ncv = 0, nuv = 0;
  bool ok = true;

  // Variables: input p -> bdd var (var_base+p); latch j -> bdd var
  // (var_base+nin+j).
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *name = aig_input_name(game, p, &lit);
    var_bdd[lit / 2] = oxidd_run_var(run, var_base + p);
    if (is_controllable(name)) {
      cvars[ncv] = var_base + p;
      cinput[ncv] = p;
      ncv++;
    } else {
      uvars[nuv++] = var_base + p;
    }
  }
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur;
    aig_latch_at(game, j, &cur, nullptr, nullptr);
    var_bdd[cur / 2] = oxidd_run_var(run, var_base + nin + j);
  }

  oxidd_phase(run, "construction");
  ok = oxidd_build_game(run, game, var_bdd, maxvar, &bad, next_bdd, NULL, NULL);
  if (ok) {
    notbad = oxidd_run_not(run, bad);
    ok = !bdd_invalid(notbad);
  }
  oxidd_bdd_unref(bad);
  bad = (Bdd){0};

  // Latch substitution s_j := next_j, reused for the fixpoint and for W[next].
  if (ok) {
    sub_lat = oxidd_bdd_substitution_new(nlat);
    if (!sub_lat) {
      ok = false;
    } else {
      if (!opts->demand_transitions)
        for (uint32_t j = 0; j < nlat; j++)
          oxidd_bdd_substitution_add_pair(sub_lat, var_base + nin + j,
                                          next_bdd[j]);
      ctrl_cube = oxidd_run_cube(run, cvars, ncv);
      unc_cube = oxidd_run_cube(run, uvars, nuv);
      if (bdd_invalid(ctrl_cube) || bdd_invalid(unc_cube))
        ok = false;
    }
  }
  if (ok) {
    oxidd_release_var_map(var_bdd, maxvar);
    free(var_bdd);
    var_bdd = nullptr;
    oxidd_phase(run, "root_release");
  }

  // Greatest fixpoint W = νZ. ∀u ∃c [ ¬bad ∧ Z[s := next] ], from Z₀ = ⊤.
  if (ok) {
    oxidd_phase(run, "fixpoint");
    Z = oxidd_bdd_true(m);
    oxidd_var_no_bool_pair_t *init_args =
        nlat ? calloc(nlat, sizeof *init_args) : nullptr;
    if (nlat && !init_args)
      ok = false;
    if (ok && !fill_initial_assignment(game, init_args, nlat, var_base, nin))
      ok = false;
    uint32_t iteration = 0;
    for (;;) {
      if (!ok)
        break;
      run->index = ++iteration;
      if (opts->demand_transitions) {
        oxidd_phase(run, "support");
        bool *needed = nlat ? calloc(nlat, sizeof *needed) : nullptr;
        ok = (!nlat || needed) &&
             oxidd_state_support(Z, var_base + nin, nlat, needed);
        if (ok) {
          oxidd_phase(run, "demand_updates");
          ok = demand_updates(run, game, var_base, maxvar, next_bdd, needed,
                              &sub_lat);
        }
        free(needed);
        if (!ok)
          break;
        oxidd_phase(run, "fixpoint");
        run->index = iteration;
      }
      Bdd img = oxidd_run_substitute(run, Z, sub_lat);
      Bdd ec = oxidd_run_apply_exists(run, OXIDD_BOOLEAN_OPERATOR_AND, notbad,
                                      img, ctrl_cube);
      Bdd au = oxidd_run_forall(run, ec, unc_cube);
      oxidd_bdd_unref(img);
      oxidd_bdd_unref(ec);
      if (bdd_invalid(au)) {
        oxidd_bdd_unref(au);
        ok = false;
        break;
      }
      bool converged = bdd_eq(au, Z);
      oxidd_bdd_unref(Z);
      Z = au;
      if (!oxidd_bdd_eval(Z, init_args, nlat)) {
        *unreal = 1;
        ok = false;
        oxidd_trace(opts, "fixpoint", "verdict",
                    ",\"verdict\":\"unrealizable\","
                    "\"verdict_reason\":\"initial_state_excluded\"");
        break;
      }
      oxidd_pressure_gc_checkpoint(run);
      if (converged)
        break;
    }
    free(init_args);
  }

  if (ok) {
    *winning = true;
    oxidd_trace(opts, "fixpoint", "verdict", ",\"verdict\":\"realizable\"");
    if (opts->realizability_only)
      goto cleanup;
  }

  // Strategy: M = ¬bad ∧ W[s := next]; sequentially Skolemise each controllable
  // c_k as f_k(state, u) = ∃(later controllables) M|_{c_k = 1}, choosing c_k =
  // 1 wherever a safe completion remains, then substituting c_k := f_k into M.
  if (ok && !*unreal) {
    oxidd_phase(run, "strategy_relation");
    Bdd wnext = oxidd_run_substitute(run, Z, sub_lat);
    M = oxidd_run_and(run, notbad, wnext);
    oxidd_bdd_unref(wnext);
    oxidd_bdd_substitution_free(sub_lat);
    sub_lat = nullptr;
    oxidd_bdd_unref(Z);
    Z = (Bdd){0};
    oxidd_bdd_unref(notbad);
    notbad = (Bdd){0};
    oxidd_bdd_unref(ctrl_cube);
    ctrl_cube = (Bdd){0};
    oxidd_bdd_unref(unc_cube);
    unc_cube = (Bdd){0};
    strat_f = ncv ? calloc(ncv, sizeof *strat_f) : nullptr;
    if (ncv && !strat_f)
      ok = false;
    oxidd_phase(run, "skolem");
    Bdd R = M;
    M = (Bdd){0};
    if (bdd_invalid(R))
      ok = false;
    for (uint32_t k = 0; k < ncv && ok; k++) {
      run->index = k;
      Bdd pos = oxidd_run_var(run, cvars[k]);
      Bdd rk1 = oxidd_run_restrict(run, R, pos); // R|_{c_k = 1}
      Bdd rem = oxidd_run_cube(run, cvars + k + 1, ncv - k - 1);
      Bdd fk = oxidd_run_exists(run, rk1, rem); // over (state, u)
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
      if (!s1) {
        ok = false;
        break;
      }
      oxidd_bdd_substitution_add_pair(s1, cvars[k], fk);
      Bdd rnew = oxidd_run_substitute(run, R, s1);
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
  if (ok && opts->demand_transitions) {
    oxidd_phase(run, "strategy_updates");
    ok = demand_updates(run, game, var_base, maxvar, next_bdd, NULL, &sub_lat);
    if (sub_lat)
      oxidd_bdd_substitution_free(sub_lat);
    sub_lat = nullptr;
  }
  if (ok && !*unreal) {
    oxidd_phase(run, "conversion");
    strat = aig_new();
    for (uint32_t v = 0; v < nin + nlat; v++)
      var2lit[v] = UINT32_MAX;
    for (uint32_t p = 0; p < nin; p++) {
      uint32_t lit;
      const char *name = aig_input_name(game, p, &lit);
      if (!is_controllable(name))
        var2lit[p] = aig_input(
            strat, oxidd_input_name_or_synthetic(name, p, (char[32]){0}));
      // controllables stay UINT32_MAX
    }
    for (uint32_t j = 0; j < nlat; j++) {
      uint32_t reset;
      aig_latch_at(game, j, nullptr, nullptr, &reset);
      lat_lit[j] = aig_latch(strat, AIG_FALSE, reset);
      var2lit[nin + j] = lat_lit[j];
    }

    // Controllable outputs.
    bool convert_error = false;
    for (uint32_t k = 0; k < ncv; k++) {
      uint32_t lit;
      const char *name = aig_input_name(game, cinput[k], &lit);
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars_local,
                     {0},   false,   nullptr,  0};
      uint32_t out = bdd2aig_root(&ctx, strat_f[k]);
      convert_error = convert_error || ctx.error;
      aig_set_output(strat, name, out);
    }
    // Latch next-functions, with the controllables substituted by their f_k.
    oxidd_bdd_substitution_t *sc =
        ncv ? oxidd_bdd_substitution_new(ncv) : nullptr;
    if (ncv && !sc)
      convert_error = true;
    for (uint32_t k = 0; k < ncv && !convert_error; k++)
      oxidd_bdd_substitution_add_pair(sc, cvars[k], strat_f[k]);
    for (uint32_t j = 0; j < nlat && !convert_error; j++) {
      run->index = j;
      Bdd na = ncv ? oxidd_run_substitute(run, next_bdd[j], sc)
                   : oxidd_bdd_ref(next_bdd[j]);
      if (bdd_invalid(na)) {
        oxidd_bdd_unref(na);
        convert_error = true;
        break;
      }
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars_local,
                     {0},   false,   nullptr,  0};
      uint32_t nl = bdd2aig_root(&ctx, na);
      convert_error = convert_error || ctx.error;
      oxidd_bdd_unref(na);
      aig_set_latch_next(strat, lat_lit[j], nl);
    }
    if (sc)
      oxidd_bdd_substitution_free(sc);
    if (convert_error) {
      oxidd_record_failure(opts, OXIDD_FAILURE_CONVERSION, "conversion",
                           "bdd2aig_or_substitution", run->operations,
                           run->index);
      aig_free(strat);
      strat = nullptr;
    }
  }

  // Cleanup.
cleanup:
  if (strat_f)
    for (uint32_t k = 0; k < ncv; k++)
      oxidd_bdd_unref(strat_f[k]);
  for (uint32_t j = 0; j < nlat; j++)
    oxidd_bdd_unref(next_bdd[j]);
  oxidd_release_var_map(var_bdd, maxvar);
  oxidd_bdd_unref(bad);
  oxidd_bdd_unref(notbad);
  oxidd_bdd_unref(Z);
  oxidd_bdd_unref(M);
  oxidd_bdd_unref(ctrl_cube);
  oxidd_bdd_unref(unc_cube);
  if (sub_lat)
    oxidd_bdd_substitution_free(sub_lat);
  if (!strat && !*unreal && !(opts->realizability_only && *winning))
    oxidd_record_failure(opts, OXIDD_FAILURE_HOST, run->phase,
                         "host_allocation_or_invalid_input", run->operations,
                         run->index);
  oxidd_run_finish(run);
  if (own_mgr)
    oxidd_bdd_manager_unref(m);
  else
    oxidd_session_gc(); // reclaim dead nodes for next cluster

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

OxiddSolveResult solve_safety_oxidd_result(Aig *game,
                                           const OxiddSolveOptions *user_opts) {
  OxiddSolveResult result = {0};
  OxiddSolveOptions opts =
      user_opts ? *user_opts : oxidd_solve_options_default();
  opts.failure = &result.failure;
  int unreal = 0;
  bool winning = false;
  result.strategy = solve_safety_impl(game, &unreal, &winning, &opts);
  result.status = (result.strategy || (opts.realizability_only && winning))
                      ? OXIDD_SOLVE_REALIZABLE
                  : unreal ? OXIDD_SOLVE_UNREALIZABLE
                           : OXIDD_SOLVE_ERROR;
  if (user_opts && user_opts->failure)
    *user_opts->failure = result.failure;
  return result;
}

Aig *solve_safety_oxidd_ex(Aig *game, int *unreal,
                           const OxiddSolveOptions *opts) {
  if (opts && opts->realizability_only) {
    *unreal = 0;
    if (opts->failure)
      *opts->failure = (OxiddFailure){0};
    oxidd_record_failure(opts, OXIDD_FAILURE_CONFIGURATION, "configuration",
                         "verdict_only_requires_typed_result", 0, 0);
    aig_free(game);
    return nullptr;
  }
  bool winning = false;
  return solve_safety_impl(game, unreal, &winning, opts);
}

Aig *solve_safety_oxidd(Aig *game, int *unreal) {
  OxiddSolveOptions opts = oxidd_solve_options_default();
  opts.safety_objective = OXIDD_SAFETY_OBJECTIVE_OUTPUT;
  opts.safety_output_index = 0;
  return solve_safety_oxidd_ex(game, unreal, &opts);
}
