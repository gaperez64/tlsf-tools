#include "tlsf/residual.h"

#include "tlsf/rewrite.h"

#include <stdlib.h>
#include <string.h>

static uint32_t uf_find(uint32_t *p, uint32_t x) {
  while (p[x] != x) {
    p[x] = p[p[x]];
    x = p[x];
  }
  return x;
}

const Node *residual_apply_elims(Arena *a, const Node *n,
                                 const CsnfComposition *comp,
                                 ConstraintCover *cov) {
  for (uint32_t pass = 0; pass <= comp->nelim; pass++)
    for (uint32_t k = 0; k < comp->nelim; k++)
      n = node_subst(a, n,
                     ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output),
                     comp->elim[k].value);
  return n;
}

void residual_collect_aps(const Node *n, ConstraintCover *cov, bool *seen) {
  switch (n->kind) {
  case NODE_AP: {
    int32_t i = ap_table_find(&cov->aps, n->name);
    if (i >= 0)
      seen[i] = true;
    return;
  }
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    residual_collect_aps(n->arg, cov, seen);
    return;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    residual_collect_aps(n->lhs, cov, seen);
    residual_collect_aps(n->rhs, cov, seen);
    return;
  default:
    return;
  }
}

bool residual_signal_matches(ConstraintCover *cov, uint32_t idx, uint8_t flag) {
  uint8_t f = ap_table_flags(&cov->aps, idx);
  if (f & flag)
    return true;
  return flag == AP_FLAG_INPUT && f == 0;
}

void residual_print_signals(FILE *out, ConstraintCover *cov, const bool *seen,
                            uint8_t flag) {
  bool first = true;
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !residual_signal_matches(cov, a, flag))
      continue;
    fprintf(out, "%s%s", first ? "" : ",", ap_table_name(&cov->aps, a));
    first = false;
  }
}

// True if any AP occurring in `n` is set in `set` (length cov->aps.count).
static bool residual_aps_hit(const Node *n, ConstraintCover *cov,
                             const bool *set) {
  switch (n->kind) {
  case NODE_AP: {
    int32_t i = ap_table_find(&cov->aps, n->name);
    return i >= 0 && set[i];
  }
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return residual_aps_hit(n->arg, cov, set);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return residual_aps_hit(n->lhs, cov, set) ||
           residual_aps_hit(n->rhs, cov, set);
  default:
    return false;
  }
}

// Finer clustering: decide which residual constraints to attach to cluster
// `kk`. The cluster's own constraints (`key==kk`) are always kept; the global
// (input-only) assumption pool (`key==UINT32_MAX`) is pruned to those
// *relevant* to the cluster — a transitive cone of influence over shared
// signals.  Assumptions over disjoint signals may be dropped exactly: the
// environment's behavior on those signals cannot help win or lose this cluster,
// while every reached assumption is retained regardless of safety/liveness
// class.  Fills `include` (length n); returns false on OOM, in which case the
// caller keeps the old (include-all-global) behavior.
static bool cluster_assumption_mask(ConstraintCover *cov, const Node **rf,
                                    const uint32_t *key, uint32_t kk,
                                    uint32_t n, bool *include) {
  uint32_t A = cov->aps.count;
  bool *gsig = calloc(A ? A : 1, sizeof(bool));
  bool *reached = calloc(n ? n : 1, sizeof(bool));
  if (!gsig || !reached) {
    free(gsig);
    free(reached);
    return false;
  }
  // Cluster core: every key==kk constraint stays; seed the cone with its
  // signals.
  for (uint32_t i = 0; i < n; i++) {
    include[i] = false;
    if (!rf[i] || key[i] != kk)
      continue;
    include[i] = true;
    reached[i] = true;
    residual_collect_aps(rf[i], cov, gsig);
  }
  // Transitive cone of influence over the global assumption pool.  A reached
  // assumption grows the cone and is attached regardless of class.
  bool changed = true;
  while (changed) {
    changed = false;
    for (uint32_t i = 0; i < n; i++) {
      if (reached[i] || !rf[i] || key[i] != UINT32_MAX)
        continue;
      if (!residual_aps_hit(rf[i], cov, gsig))
        continue;
      reached[i] = true;
      changed = true;
      residual_collect_aps(rf[i], cov, gsig);
      include[i] = true;
    }
  }
  free(gsig);
  free(reached);
  return true;
}

bool residual_build_cluster_view(TlsfSpec *spec, ConstraintCover *cov,
                                 const Node **rf, const uint32_t *key,
                                 uint32_t kk, bool all, bool prune, uint32_t n,
                                 bool *seen, SectionPatternView *view) {
  section_pattern_init(view, spec->arena, spec);
  memset(seen, 0, cov->aps.count ? cov->aps.count : 1);
  // Finer clustering prunes the global assumption pool per cluster.  Skip it
  // under strict semantics: there the assumption/guarantee `W` structure drives
  // the (AbsSynthe strict-safety) encoding, and dropping assumptions reshapes
  // the formula into a nested-`G` form the backend does not recognize.
  bool *include = nullptr;
  if (!all && prune && !semantics_is_strict(spec->info.semantics)) {
    include = malloc((n ? n : 1) * sizeof(bool));
    if (include && !cluster_assumption_mask(cov, rf, key, kk, n, include)) {
      free(include);
      include =
          nullptr; // OOM: fall back to the old include-all-global behavior
    }
  }
  for (uint32_t i = 0; i < n; i++) {
    if (!rf[i])
      continue;
    bool inc;
    if (all)
      inc = true;
    else if (include)
      inc = include[i];
    else if (!prune)
      // Output-free realizability check: the key==kk guarantees plus *every*
      // assumption (not just key==UINT32_MAX ones).  A coupling assumption like
      // G(grant -> X req) mentions an output, so residual_cluster_keys keys it
      // to that output's cluster, not to UINT32_MAX; it must still be present
      // (with grant declared controllable) for the input-only guarantee to be
      // judged realizable.
      inc = key[i] == kk || cov->items[i].assumption_side;
    else
      inc = key[i] == kk || key[i] == UINT32_MAX; // OOM fallback (prune path)
    if (!inc)
      continue;
    residual_collect_aps(rf[i], cov, seen);
    if (!section_pattern_add_classified(view, cov->items[i].role,
                                        (Node *)rf[i])) {
      free(include);
      return false;
    }
  }
  free(include);
  return true;
}

Node *residual_build_cluster(TlsfSpec *spec, ConstraintCover *cov,
                             const Node **rf, const uint32_t *key, uint32_t kk,
                             bool all, bool prune, uint32_t n, bool *seen) {
  SectionPatternView view;
  if (!residual_build_cluster_view(spec, cov, rf, key, kk, all, prune, n, seen,
                                   &view))
    return nullptr;
  Node *root = section_pattern_to_ltl(&view, true, true);
  if (semantics_is_finite(spec->info.semantics))
    root = apply_rewrites(spec->arena, root,
                          RW_NO_WEAK_UNTIL | RW_NO_STRONG_RELEASE);
  return root;
}

uint32_t residual_cluster_keys(ConstraintCover *cov, const Node **rf,
                               uint32_t n, uint32_t *key, uint32_t **keys_out) {
  uint32_t A = cov->aps.count;
  uint32_t *parent = malloc((A ? A : 1) * sizeof(uint32_t));
  bool *seen = calloc(A ? A : 1, sizeof(bool));
  uint32_t *keys = malloc((n + 1) * sizeof(uint32_t));
  if (!parent || !seen || !keys) {
    free(parent);
    free(seen);
    free(keys);
    *keys_out = nullptr;
    return 0;
  }
  for (uint32_t a = 0; a < A; a++)
    parent[a] = a;

  bool output_dependent_assumption = false;
  // Union outputs that co-occur in one constraint.
  for (uint32_t i = 0; i < n; i++) {
    if (!rf[i])
      continue;
    memset(seen, 0, A);
    residual_collect_aps(rf[i], cov, seen);
    int64_t first = -1;
    for (uint32_t a = 0; a < A; a++) {
      if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
        continue;
      if (cov->items[i].assumption_side)
        output_dependent_assumption = true;
      if (first < 0)
        first = (int64_t)a;
      else {
        uint32_t ra = uf_find(parent, a), rb = uf_find(parent, (uint32_t)first);
        if (ra != rb)
          parent[ra] = rb;
      }
    }
  }

  int64_t collapse_root = -1;
  if (output_dependent_assumption) {
    // An assumption mentioning outputs couples the residual games through the
    // antecedent.  If we left the guarantee clusters independent, each cluster
    // would either drop that assumption or synthesize with another cluster's
    // output treated as locally controllable.  Both are unsound, so collapse
    // all output components and attach input-only guarantees to that component.
    for (uint32_t a = 0; a < A; a++)
      if (ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT) {
        if (collapse_root < 0)
          collapse_root = (int64_t)a;
        else {
          uint32_t ra = uf_find(parent, a);
          uint32_t rb = uf_find(parent, (uint32_t)collapse_root);
          if (ra != rb)
            parent[ra] = rb;
        }
      }
  }

  // Per-constraint key: output component, sentinel A for an input-only system
  // obligation, or UINT32_MAX for global environment / skipped.
  for (uint32_t i = 0; i < n; i++) {
    key[i] = UINT32_MAX;
    if (!rf[i])
      continue;
    if (cov->items[i].assumption_side)
      continue;
    memset(seen, 0, A);
    residual_collect_aps(rf[i], cov, seen);
    int64_t first = -1;
    for (uint32_t a = 0; a < A; a++)
      if (seen[a] && (ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT)) {
        first = (int64_t)a;
        break;
      }
    if (first >= 0)
      key[i] = uf_find(parent, (uint32_t)first);
    else if (collapse_root >= 0)
      // If an assumption constrains outputs, independent clusters no longer
      // have a local assumption environment.  Keep input-only guarantees in
      // the same conservative residual cluster instead of checking them with
      // those outputs treated as freshly controllable.
      key[i] = uf_find(parent, (uint32_t)collapse_root);
    else if (!cov->items[i].assumption_side)
      key[i] = A;
  }
  // Distinct non-global keys.
  uint32_t K = 0;
  for (uint32_t i = 0; i < n; i++) {
    if (key[i] == UINT32_MAX)
      continue;
    bool dup = false;
    for (uint32_t j = 0; j < K; j++)
      if (keys[j] == key[i])
        dup = true;
    if (!dup)
      keys[K++] = key[i];
  }
  free(parent);
  free(seen);
  *keys_out = keys;
  return K;
}
