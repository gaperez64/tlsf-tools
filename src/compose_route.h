#ifndef TLSF_COMPOSE_ROUTE_H
#define TLSF_COMPOSE_ROUTE_H

#include "compose_internal.h"

#include "tlsf/section_pattern.h"

typedef enum {
  ROUTE_OUTPUT_FREE_LTLSYNT,
  ROUTE_DIRECT_SAFETY,
  ROUTE_STRICT_SAFETY,
  ROUTE_WR_SAFETY,
  ROUTE_BOUNDED_EXPERIMENTAL,
  ROUTE_RESPONSE_MONITOR_GR1,
  ROUTE_EVENTUAL_MONITOR_GR1,
  ROUTE_UNTIL_MONITOR_GR1,
  ROUTE_GR1,
  ROUTE_LTLSYNT,
} ComposeRouteKind;

typedef struct {
  ComposeRouteKind kind;
  bool uses_oxidd;
  bool exact;
  bool over_approx; ///< the encoding can WEAKEN the spec (over-approximation):
                    ///< its REALIZABLE verdict is not trustworthy.  Set for W/R
                    ///< safety diagnostics.
  const char *label;
  const char *reason_override;
  ClusterShape shape;
  const Node *root;
  const Node *bounded_root;
  const Node *strict_sys;
  const Node *strict_env;
  const Node *strict_env_init;
  const Node *strict_env_require;
  const Node *strict_sys_init;
  const Node *strict_sys_assert;
  Gr1Parts gr1;
} ComposeRoute;

bool compose_route_select(TlsfSpec *spec, const Node *root, bool finite,
                          uint32_t bound_k, ComposeRoute *out);
bool compose_route_select_sections(TlsfSpec *spec, const Node *root,
                                   const SectionPatternView *view, bool finite,
                                   uint32_t bound_k, ComposeRoute *out);
bool compose_route_can_presolve_oxidd(const ComposeRoute *route);
[[nodiscard]] Aig *compose_route_try_oxidd(const ComposeRoute *route,
                                           ConstraintCover *cov,
                                           const bool *seen, int *unreal,
                                           bool *trusted_unreal,
                                           const char **backend_label);

#endif // TLSF_COMPOSE_ROUTE_H
