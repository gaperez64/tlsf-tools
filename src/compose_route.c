#include "compose_route.h"

static Node *true_if_absent(Arena *a, Node *n) { return n ? n : node_true(a); }

static bool
strict_sections_safety_parts(TlsfSpec *spec, const SectionPatternView *view,
                             const Node **env_init, const Node **env_require,
                             const Node **sys_init, const Node **sys_assert) {
  if (!view || !semantics_is_strict(spec->info.semantics))
    return false;
  if (!section_pattern_role_empty(view, TLSF_ROLE_ASSUME) ||
      !section_pattern_role_empty(view, TLSF_ROLE_GUARANTEE))
    return false;

  Arena *a = spec->arena;
  const Node *ei =
      true_if_absent(a, section_pattern_conj(view, TLSF_ROLE_INITIALLY));
  const Node *er =
      true_if_absent(a, section_pattern_conj(view, TLSF_ROLE_REQUIRE));
  const Node *si =
      true_if_absent(a, section_pattern_conj(view, TLSF_ROLE_PRESET));
  const Node *sa =
      true_if_absent(a, section_pattern_conj(view, TLSF_ROLE_ASSERT));
  if (!aig_initial_ok(ei) || !aig_initial_ok(si) || !aig_body_ok(er) ||
      !aig_body_ok(sa))
    return false;

  *env_init = ei;
  *env_require = er;
  *sys_init = si;
  *sys_assert = sa;
  return true;
}

bool compose_route_select_sections(TlsfSpec *spec, const Node *root,
                                   const SectionPatternView *view, bool finite,
                                   uint32_t bound_k, ComposeRoute *out) {
  if (!out)
    return false;

  ClusterShape shape = cluster_shape(spec, root);
  if (view)
    shape.gr_level = section_pattern_gr_level(view);
  *out = (ComposeRoute){
      .kind = ROUTE_LTLSYNT,
      .uses_oxidd = false,
      .exact = true,
      .label = "ltlsynt fallback",
      .shape = shape,
      .root = root,
  };

  const Node *strict_env_init = nullptr, *strict_env_require = nullptr;
  const Node *strict_sys_init = nullptr, *strict_sys_assert = nullptr;
  bool use_section_strict =
      !finite && shape.gr_level == 0 && !shape.has_liveness &&
      strict_sections_safety_parts(spec, view, &strict_env_init,
                                   &strict_env_require, &strict_sys_init,
                                   &strict_sys_assert);
  if (use_section_strict) {
    out->kind = ROUTE_STRICT_SAFETY;
    out->uses_oxidd = true;
    out->label = "OxiDD";
    out->strict_env_init = strict_env_init;
    out->strict_env_require = strict_env_require;
    out->strict_sys_init = strict_sys_init;
    out->strict_sys_assert = strict_sys_assert;
    return true;
  }

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

bool compose_route_select(TlsfSpec *spec, const Node *root, bool finite,
                          uint32_t bound_k, ComposeRoute *out) {
  return compose_route_select_sections(spec, root, nullptr, finite, bound_k,
                                       out);
}
