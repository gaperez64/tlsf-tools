#include "residual_plan.h"

#include "residual.h"
#include "rewrite.h"

#include <stdlib.h>

ResidualPlan *residual_plan_build(TlsfSpec *spec, ConstraintCover *cov,
                                  const Csnf *csnf, const CsnfComposition *comp,
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
    if (opts.skip_local_aiger && csnf_constraint_has_local_aiger(csnf, comp, i))
      continue;
    const Node *f =
        residual_apply_elims(spec->arena, cov->items[i].formula, comp, cov);
    if (opts.simplify_weak)
      f = apply_rewrites(
          spec->arena, (Node *)f,
          RW_SIMPLIFY_WEAK |
              (semantics_is_finite(spec->info.semantics) ? RW_FINITE : 0));
    if (!f || arena_failed(spec->arena))
      goto fail;
    if (f->kind != NODE_TRUE)
      p->rf[i] = f;
  }

  p->nclusters = residual_cluster_keys(cov, p->rf, n, p->key, &p->keys);
  if (!p->keys)
    goto fail;
  p->cluster_views = calloc(p->nclusters ? p->nclusters : 1,
                            sizeof(*p->cluster_views));
  p->cluster_view_ready = calloc(p->nclusters ? p->nclusters : 1,
                                 sizeof(*p->cluster_view_ready));
  if (!p->cluster_views || !p->cluster_view_ready) {
    free(p->cluster_views);
    free(p->cluster_view_ready);
    p->cluster_views = nullptr;
    p->cluster_view_ready = nullptr;
  }
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
  free(p->cluster_views);
  free(p->cluster_view_ready);
  free(p);
}

Node *residual_plan_build_cluster(TlsfSpec *spec, ConstraintCover *cov,
                                  const ResidualPlan *p, uint32_t cluster_key,
                                  bool all, bool prune, bool *seen) {
  SectionPatternView view;
  if (!residual_plan_build_cluster_view(spec, cov, p, cluster_key, all, prune,
                                        seen, &view))
    return nullptr;
  Node *root = section_pattern_to_ltl(&view, true, true);
  if (!root || arena_failed(spec->arena))
    return nullptr;
  if (semantics_is_finite(spec->info.semantics))
    root = apply_rewrites(spec->arena, root,
                          RW_NO_WEAK_UNTIL | RW_NO_STRONG_RELEASE);
  return arena_failed(spec->arena) ? nullptr : root;
}

bool residual_plan_build_cluster_view(TlsfSpec *spec, ConstraintCover *cov,
                                      const ResidualPlan *p,
                                      uint32_t cluster_key, bool all,
                                      bool prune, bool *seen,
                                      SectionPatternView *view) {
  if (!all && prune && p->cluster_views) {
    for (uint32_t k = 0; k < p->nclusters; k++) {
      if (p->keys[k] != cluster_key)
        continue;
      if (!p->cluster_view_ready[k]) {
        if (!residual_build_cluster_view(spec, cov, p->rf, p->key, cluster_key,
                                         false, true, p->nconstraints, seen,
                                         &p->cluster_views[k]))
          return false;
        p->cluster_view_ready[k] = true;
      }
      *view = p->cluster_views[k];
      for (uint32_t a = 0; a < p->ap_count; a++)
        seen[a] = false;
      for (uint32_t i = 0; i < view->count; i++)
        residual_collect_aps(view->entries[i].formula, cov, seen);
      return true;
    }
  }
  // Missing cache memory keeps all environment entries for this whole plan.
  return residual_build_cluster_view(spec, cov, p->rf, p->key, cluster_key, all,
                                     false, p->nconstraints, seen, view);
}
