#ifndef TLSF_COMPOSE_ROUTE_H
#define TLSF_COMPOSE_ROUTE_H

#include "tlsf/compose_internal.h"

typedef enum {
  ROUTE_OUTPUT_FREE_LTLSYNT,
  ROUTE_DIRECT_SAFETY,
  ROUTE_STRICT_SAFETY,
  ROUTE_WR_SAFETY,
  ROUTE_BOUNDED_EXPERIMENTAL,
  ROUTE_GR1,
  ROUTE_LTLSYNT,
} ComposeRouteKind;

typedef struct {
  ComposeRouteKind kind;
  bool uses_oxidd;
  bool exact;
  const char *label;
  ClusterShape shape;
  const Node *root;
  const Node *bounded_root;
  const Node *strict_sys;
  const Node *strict_env;
  Gr1Parts gr1;
} ComposeRoute;

bool compose_route_select(TlsfSpec *spec, const Node *root, bool finite,
                          uint32_t bound_k, ComposeRoute *out);

[[nodiscard]] Aig *compose_route_solve(const ComposeRoute *route,
                                       const char *ltlsynt_prog,
                                       ConstraintCover *cov,
                                       const bool *seen, LtlFormat fmt,
                                       bool finite, int *unreal,
                                       bool *used_oxidd,
                                       const char **backend_label);

#endif // TLSF_COMPOSE_ROUTE_H
