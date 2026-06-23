#include "compose_route.h"

bool compose_route_select(TlsfSpec *spec, const Node *root, bool finite,
                          uint32_t bound_k, ComposeRoute *out) {
  if (!out)
    return false;

  ClusterShape shape = cluster_shape(spec, root);
  *out = (ComposeRoute){
      .kind = ROUTE_LTLSYNT,
      .uses_oxidd = false,
      .exact = true,
      .label = "ltlsynt fallback",
      .shape = shape,
      .root = root,
  };

  bool use_direct = aig_eligible(root, finite);
  if (use_direct) {
    out->kind = ROUTE_DIRECT_SAFETY;
    out->uses_oxidd = true;
    out->label = "OxiDD";
    return true;
  }

  const Node *strict_sys = nullptr, *strict_env = nullptr;
  bool use_strict = !finite && shape.gr_level == 0 && !shape.has_liveness &&
                    aig_strict_safety_parts(root, &strict_sys, &strict_env);
  if (use_strict) {
    out->kind = ROUTE_STRICT_SAFETY;
    out->uses_oxidd = true;
    out->label = "OxiDD";
    out->strict_sys = strict_sys;
    out->strict_env = strict_env;
    return true;
  }

  bool use_wr = !finite && !shape.has_liveness && wr_structural_supported(root);
  if (use_wr) {
    out->kind = ROUTE_WR_SAFETY;
    out->uses_oxidd = true;
    out->label = "OxiDD (W/R safety)";
    return true;
  }

  if (bound_k != 0 && !finite &&
      (shape.has_liveness || shape.has_weak_until || shape.has_release)) {
    Node *br = bound_liveness(spec->arena, root, bound_k, true);
    if (aig_eligible(br, finite)) {
      out->kind = ROUTE_BOUNDED_EXPERIMENTAL;
      out->uses_oxidd = true;
      out->exact = false;
      out->label = "OxiDD (bounded)";
      out->bounded_root = br;
      return true;
    }
  }

  Gr1Parts gp = {0};
  if (!finite && aig_response_monitor_parts(spec->arena, root, &gp)) {
    out->kind = ROUTE_RESPONSE_MONITOR_GR1;
    out->uses_oxidd = true;
    out->label = "OxiDD (response monitor)";
    out->gr1 = gp;
    return true;
  }

  gp = (Gr1Parts){0};
  if (!finite && aig_eventual_monitor_parts(spec, root, &gp)) {
    out->kind = ROUTE_EVENTUAL_MONITOR_GR1;
    out->uses_oxidd = true;
    out->label = "OxiDD (eventual monitor)";
    out->gr1 = gp;
    return true;
  }

  gp = (Gr1Parts){0};
  if (!finite && aig_until_monitor_parts(spec, root, &gp)) {
    out->kind = ROUTE_UNTIL_MONITOR_GR1;
    out->uses_oxidd = true;
    out->label = "OxiDD (until monitor)";
    out->gr1 = gp;
    return true;
  }

  gp = (Gr1Parts){0};
  if (!finite && aig_gr1_parts(spec->arena, root, &gp)) {
    out->kind = ROUTE_GR1;
    out->uses_oxidd = true;
    out->label = "OxiDD (GR(1))";
    out->gr1 = gp;
    return true;
  }

  GrkParts grk = {0};
  if (!finite && aig_grk_parts(spec->arena, root, &grk)) {
    out->kind = ROUTE_GRK_STREETT;
    out->uses_oxidd = true;
    // The per-pair PPS Streett solver is a sound-in-practice but provably
    // non-exact fixpoint (Streett game solving is coNP-complete; this fixpoint
    // is polynomial), so mark the route inexact: its controller should be
    // covered by the self-verification gate (--verify) for a hard guarantee.
    out->exact = false;
    out->label = "OxiDD (Streett)";
    out->grk = grk;
  }
  return true;
}

Aig *compose_route_solve(const ComposeRoute *route, const char *ltlsynt_prog,
                         ConstraintCover *cov, const bool *seen, LtlFormat fmt,
                         bool finite, int *unreal, bool *used_oxidd,
                         const char **backend_label) {
  int local_unreal = 0;
  bool use_oxidd = route->uses_oxidd;
  const char *backend = route->label ? route->label : "ltlsynt fallback";
  const Node *root = route->root;
  Aig *sub = nullptr;

  switch (route->kind) {
  case ROUTE_DIRECT_SAFETY:
    sub = solve_safety_game(cov, seen, build_aig_game(cov, seen, root),
                            &local_unreal);
    // Formulas with bare top-level W/R (not inside G) use release-latch
    // monitors compiled at lag=depth.  When depth>0 (G X conjuncts in the
    // same formula) the lag interaction can spuriously over-constrain the
    // game.  Fall back to ltlsynt on UNREALIZABLE in that case; for pure
    // G-only formulas (no bare W/R) the encoding is exact and UNREALIZABLE
    // can be trusted.
    if (!sub && (!local_unreal || wr_has_bare_wr(root))) {
      local_unreal = 0;
      use_oxidd = false;
      backend = "ltlsynt fallback (safety miss)";
      sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                                &local_unreal);
    }
    break;

  case ROUTE_STRICT_SAFETY:
    sub =
        solve_safety_game(cov, seen,
                          build_aig_strict_safety_game(
                              cov, seen, route->strict_sys, route->strict_env),
                          &local_unreal);
    if (!sub && !local_unreal) {
      use_oxidd = false;
      backend = "ltlsynt fallback (strict safety miss)";
      sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                                &local_unreal);
    }
    break;

  case ROUTE_WR_SAFETY:
    sub = solve_safety_game(cov, seen, build_aig_wr_game(cov, seen, root),
                            &local_unreal);
    if (!sub) {
      // Fall back on both encoding errors (unreal=0) and UNREALIZABLE verdicts
      // (unreal=1): complex pattern interaction can produce over-constrained
      // games that are spuriously unrealizable.  ltlsynt is authoritative.
      local_unreal = 0;
      use_oxidd = false;
      backend = "ltlsynt fallback (W/R miss)";
      sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                                &local_unreal);
    }
    break;

  case ROUTE_BOUNDED_EXPERIMENTAL:
    sub = solve_safety_game(cov, seen,
                            build_aig_game(cov, seen, route->bounded_root),
                            &local_unreal);
    if (!sub) {
      // Bounded miss (unrealizable at this k, or no strategy): the unbounded
      // game may still be realizable, so fall back instead of failing.
      local_unreal = 0;
      use_oxidd = false;
      backend = "ltlsynt fallback (bounded miss)";
      sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                                &local_unreal);
    }
    break;

  case ROUTE_GR1:
    sub = solve_gr1_game(cov, seen, build_aig_gr1_game(cov, seen, &route->gr1),
                         &local_unreal);
    if (!sub) {
      // The GR(1) recognizer may over-constrain; defer to ltlsynt rather than
      // risk a false UNREALIZABLE.
      local_unreal = 0;
      use_oxidd = false;
      backend = "ltlsynt fallback (GR(1) miss)";
      sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                                &local_unreal);
    }
    break;

  case ROUTE_GRK_STREETT:
    // The full symbolic Streett solver computes the winning region; its
    // finite-memory strategy extraction is staged (returns nullptr meanwhile).
    sub = solve_grk_game(cov, seen, build_aig_grk_game(cov, seen, &route->grk),
                         &local_unreal);
    if (!sub) {
      // Sound sufficient strategy: if the system can satisfy every guarantee
      // `G F g_k` unconditionally (a generalized-Büchi game over all goals,
      // with no fairness escape), that strategy wins the Streett condition
      // outright (each implication's consequent holds).  Reuse the proven GR(1)
      // solver.
      Gr1Parts gb = {0};
      gb.env_init = route->grk.env_init;
      gb.sys_init = route->grk.sys_init;
      gb.safety_assume = route->grk.safety_assume;
      gb.safety_gua = route->grk.safety_gua;
      gb.nfairness = 0;
      gb.njustice = 0;
      for (uint32_t k = 0; k < route->grk.npairs; k++)
        for (uint32_t j = 0;
             j < route->grk.pairs[k].njustice && gb.njustice < GR1_MAX_JUSTICE;
             j++)
          gb.justice[gb.njustice++] = route->grk.pairs[k].justice[j];
      gb.nweak = route->grk.nweak;
      for (uint32_t w = 0; w < route->grk.nweak && w < GR1_MAX_WEAK; w++)
        gb.weak[w] = route->grk.weak[w];
      local_unreal = 0;
      sub = solve_gr1_game(cov, seen, build_aig_gr1_game(cov, seen, &gb),
                           &local_unreal);
      if (sub)
        backend = "OxiDD (Streett via gen-Büchi)";
    }
    if (!sub) {
      // Assumption-dependent Streett (or recognizer over-constraint): defer to
      // ltlsynt (sound: self-verification + authoritative oracle).
      local_unreal = 0;
      use_oxidd = false;
      backend = "ltlsynt fallback (Streett miss)";
      sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                                &local_unreal);
    }
    break;

  case ROUTE_RESPONSE_MONITOR_GR1:
  case ROUTE_EVENTUAL_MONITOR_GR1:
  case ROUTE_UNTIL_MONITOR_GR1:
    sub = solve_gr1_game(cov, seen, build_aig_gr1_game(cov, seen, &route->gr1),
                         &local_unreal);
    if (!sub) {
      // These monitors are exact for recognized fragments, but still fall back
      // on any solver/build miss until this path has broad coverage.
      local_unreal = 0;
      use_oxidd = false;
      backend = route->kind == ROUTE_RESPONSE_MONITOR_GR1
                    ? "ltlsynt fallback (response monitor miss)"
                : route->kind == ROUTE_EVENTUAL_MONITOR_GR1
                    ? "ltlsynt fallback (eventual monitor miss)"
                    : "ltlsynt fallback (until monitor miss)";
      sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                                &local_unreal);
    }
    break;

  case ROUTE_OUTPUT_FREE_LTLSYNT:
  case ROUTE_LTLSYNT:
  default:
    use_oxidd = false;
    sub = run_ltlsynt_cluster(ltlsynt_prog, cov, seen, root, fmt, finite,
                              &local_unreal);
    break;
  }

  if (unreal)
    *unreal = local_unreal;
  if (used_oxidd)
    *used_oxidd = use_oxidd;
  if (backend_label)
    *backend_label = backend;
  return sub;
}
