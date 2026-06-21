#include "tlsf/residual_plan.h"

#include "tlsf/residual.h"
#include "tlsf/rewrite.h"

#include <stdlib.h>

ResidualPlan *residual_plan_build(TlsfSpec *spec, ConstraintCover *cov,
                                  const Csnf *csnf,
                                  const CsnfComposition *comp,
                                  ResidualPlanOptions opts) {
  uint32_t n = cov->count;
  ResidualPlan *p = calloc(1, sizeof(*p));
  if (!p)
    return nullptr;
  p->nconstraints = n;
  p->ap_count = cov->aps.count;

  p->rf = calloc(n ? n : 1, sizeof(Node *));
  p->key = malloc((n ? n : 1) * sizeof(uint32_t));
  if (!p->rf || !p->key)
    goto fail;

  for (uint32_t i = 0; i < n; i++) {
    if (comp->elim_constraint[i])
      continue;
    if (opts.skip_local_aiger &&
        csnf_constraint_has_local_aiger(csnf, comp, i))
      continue;
    const Node *f =
        residual_apply_elims(spec->arena, cov->items[i].formula, comp, cov);
    if (opts.simplify_weak)
      f = apply_rewrites(spec->arena, (Node *)f, RW_SIMPLIFY_WEAK);
    if (f->kind != NODE_TRUE)
      p->rf[i] = f;
  }

  p->nclusters = residual_cluster_keys(cov, p->rf, n, p->key, &p->keys);
  if (!p->keys)
    goto fail;
  return p;

fail:
  residual_plan_free(p);
  return nullptr;
}

void residual_plan_free(ResidualPlan *p) {
  if (!p)
    return;
  free(p->rf);
  free(p->key);
  free(p->keys);
  free(p);
}

Node *residual_plan_build_cluster(TlsfSpec *spec, ConstraintCover *cov,
                                  const ResidualPlan *p, uint32_t cluster_key,
                                  bool all, bool prune, bool *seen) {
  return residual_build_cluster(spec, cov, p->rf, p->key, cluster_key, all,
                                prune, p->nconstraints, seen);
}
