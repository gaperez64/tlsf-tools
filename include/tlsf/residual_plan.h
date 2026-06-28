#ifndef TLSF_RESIDUAL_PLAN_H
#define TLSF_RESIDUAL_PLAN_H

#include "tlsf/cover.h"
#include "tlsf/section_pattern.h"
#include "tlsf/templates.h"

#include <stdbool.h>
#include <stdint.h>

typedef struct {
  const Node **rf; // length nconstraints; NULL means skipped/discharged
  uint32_t *key;   // length nconstraints
  uint32_t *keys;  // length nclusters
  uint32_t nconstraints;
  uint32_t nclusters;
  uint32_t ap_count;
} ResidualPlan;

typedef struct {
  bool skip_local_aiger;
  bool simplify_weak;
} ResidualPlanOptions;

[[nodiscard]] ResidualPlan *
residual_plan_build(TlsfSpec *spec, ConstraintCover *cov, const Csnf *csnf,
                    const CsnfComposition *comp, ResidualPlanOptions opts);
void residual_plan_free(ResidualPlan *p);

[[nodiscard]] Node *residual_plan_build_cluster(TlsfSpec *spec,
                                                ConstraintCover *cov,
                                                const ResidualPlan *p,
                                                uint32_t cluster_key, bool all,
                                                bool prune, bool *seen);

bool residual_plan_build_cluster_view(TlsfSpec *spec, ConstraintCover *cov,
                                      const ResidualPlan *p,
                                      uint32_t cluster_key, bool all,
                                      bool prune, bool *seen,
                                      SectionPatternView *view);

#endif // TLSF_RESIDUAL_PLAN_H
