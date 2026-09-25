// compose_oxidd.c — exact in-process OxiDD cluster solving for tlsfcompose.
//
// This file deliberately contains no external-solver fallback.  It is used by
// `tlsfcompose --output-dir` to pre-solve residual clusters that the local
// OxiDD encodings can handle exactly; anything else remains an emitted
// cluster.k.ltl for the wrapper/backend to solve.

#include "compose_route.h"

#include "tlsf/gr1_oxidd.h"
#include "tlsf/safety_oxidd.h"

static bool strategy_has_outputs(Aig *g, ConstraintCover *cov,
                                 const bool *seen) {
  aig_remove_output(g, "bad");
  aig_strip_output_prefix(g, AIG_CONTROLLABLE_PREFIX);
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    if (!aig_has_output(g, ap_table_name(&cov->aps, a)))
      return false;
  }
  return true;
}

static Aig *solve_safety_game(ConstraintCover *cov, const bool *seen, Aig *game,
                              int *unreal) {
  if (!game)
    return nullptr;
  Aig *strat = solve_safety_oxidd(game, unreal);
  if (strat && !strategy_has_outputs(strat, cov, seen)) {
    aig_free(strat);
    strat = nullptr;
  }
  return strat;
}

static Aig *solve_gr1_game(ConstraintCover *cov, const bool *seen, Aig *game,
                           int *unreal) {
  if (!game)
    return nullptr;
  Aig *strat = solve_gr1_oxidd(game, unreal);
  if (strat && !strategy_has_outputs(strat, cov, seen)) {
    aig_free(strat);
    strat = nullptr;
  }
  return strat;
}

bool compose_route_can_presolve_oxidd(const ComposeRoute *route) {
  if (!route || !route->uses_oxidd || route->over_approx)
    return false;
  return true;
}

static bool compose_route_unreal_trusted(const ComposeRoute *route) {
  if (!route || !route->uses_oxidd)
    return false;
  if (route->over_approx)
    return true;
  if (route->kind == ROUTE_BOUNDED_EXPERIMENTAL)
    return false;
  if (route->kind == ROUTE_DIRECT_SAFETY && wr_has_bare_wr(route->root))
    return false;
  if (route->kind == ROUTE_GR1)
    return false;
  return route->exact;
}

Aig *compose_route_try_oxidd(const ComposeRoute *route, ConstraintCover *cov,
                             const bool *seen, int *unreal,
                             bool *trusted_unreal, const char **backend_label) {
  if (unreal)
    *unreal = 0;
  if (trusted_unreal)
    *trusted_unreal = false;
  if (backend_label)
    *backend_label = route && route->label ? route->label : "OxiDD";
  if (!route || !route->uses_oxidd)
    return nullptr;

  int local_unreal = 0;
  Aig *sub = nullptr;
  switch (route->kind) {
  case ROUTE_DIRECT_SAFETY:
    sub = solve_safety_game(cov, seen, build_aig_game(cov, seen, route->root),
                            &local_unreal);
    break;
  case ROUTE_STRICT_SAFETY:
    if (route->strict_env_init) {
      sub = solve_safety_game(
          cov, seen,
          build_aig_tlsf_strict_safety_game(
              cov, seen, route->strict_env_init, route->strict_env_require,
              route->strict_sys_init, route->strict_sys_assert),
          &local_unreal);
    } else {
      sub = solve_safety_game(cov, seen,
                              build_aig_strict_safety_game(cov, seen,
                                                           route->strict_sys,
                                                           route->strict_env),
                              &local_unreal);
    }
    break;
  case ROUTE_RESPONSE_MONITOR_GR1:
  case ROUTE_EVENTUAL_MONITOR_GR1:
  case ROUTE_UNTIL_MONITOR_GR1:
  case ROUTE_GR1:
    sub = solve_gr1_game(cov, seen, build_aig_gr1_game(cov, seen, &route->gr1),
                         &local_unreal);
    break;
  default:
    break;
  }

  if (unreal)
    *unreal = local_unreal;
  if (trusted_unreal)
    *trusted_unreal = local_unreal && compose_route_unreal_trusted(route);
  if (sub && !compose_route_can_presolve_oxidd(route)) {
    aig_free(sub);
    sub = nullptr;
  }
  return sub;
}
