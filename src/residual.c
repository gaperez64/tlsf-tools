#include "tlsf/residual.h"

#include "tlsf/classify.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/rewrite.h"

#include <stdlib.h>
#include <string.h>

// Map a constraint Role to its destination section list in the spec.
static FormulaList *role_list(TlsfSpec *spec, Role role) {
  switch (role) {
  case TLSF_ROLE_INITIALLY:
    return &spec->initially;
  case TLSF_ROLE_PRESET:
    return &spec->preset;
  case TLSF_ROLE_REQUIRE:
    return &spec->require;
  case TLSF_ROLE_ASSERT:
    return &spec->assert_;
  case TLSF_ROLE_ASSUME:
    return &spec->assume;
  case TLSF_ROLE_GUARANTEE:
  default:
    return &spec->guarantee;
  }
}

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

void residual_print_signals(FILE *out, ConstraintCover *cov, const bool *seen,
                            uint8_t flag) {
  bool first = true;
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & flag))
      continue;
    fprintf(out, "%s%s", first ? "" : ",", ap_table_name(&cov->aps, a));
    first = false;
  }
}

Node *residual_build_cluster(TlsfSpec *spec, ConstraintCover *cov,
                             const Node **rf, const uint32_t *key, uint32_t kk,
                             bool all, uint32_t n, bool *seen) {
  spec->initially.count = spec->require.count = spec->assume.count = 0;
  spec->preset.count = spec->assert_.count = spec->guarantee.count = 0;
  memset(seen, 0, cov->aps.count ? cov->aps.count : 1);
  for (uint32_t i = 0; i < n; i++) {
    if (!rf[i] || !(all || key[i] == kk || key[i] == UINT32_MAX))
      continue;
    residual_collect_aps(rf[i], cov, seen);
    (void)formula_list_push(spec, role_list(spec, cov->items[i].role),
                            (Node *)rf[i]);
  }
  ClassifiedSpec *cs = classify_spec(spec);
  if (!cs)
    return nullptr;
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
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
      if (first < 0)
        first = (int64_t)a;
      else {
        uint32_t ra = uf_find(parent, a), rb = uf_find(parent, (uint32_t)first);
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
