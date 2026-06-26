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
    // OVER-approximation: the W/R game encoding is not exact — it can WEAKEN
    // the spec and so produce a wrong controller (false-REAL, e.g. box/evasion/
    // follow).  Mark it so its REALIZABLE verdict is verified, never trusted
    // blind (see the over-approx re-validation in main_tlsfcompose.c).
    out->exact = false;
    out->over_approx = true;
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
  }
  return true;
}
