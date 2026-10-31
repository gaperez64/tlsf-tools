#include "residual.h"

#include "rewrite.h"
#include "env_witness.h"

#include <assert.h>

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

// Close the cluster core transitively over the global environment pool. Only
// input-only, disjoint entries are candidates for D. Output-dependent entries
// are seeded into K, including when the conservative one-game fallback applies.
static bool cluster_assumption_mask(TlsfSpec *spec, ConstraintCover *cov,
                                    const Node **rf, const uint32_t *key,
                                    uint32_t kk, uint32_t n, bool *include) {
  uint32_t A = cov->aps.count;
  bool *kept = calloc(A ? A : 1, sizeof(bool));
  bool *atoms = calloc(A ? A : 1, sizeof(bool));
  Arena *scratch = arena_new(4096);
  if (!kept || !atoms || !scratch) {
    free(kept);
    free(atoms);
    arena_free(scratch);
    return false;
  }
  bool ok = false;
  SectionPatternView dropped;
  section_pattern_init(&dropped, scratch, spec);
  for (uint32_t i = 0; i < n; i++) {
    include[i] = false;
    if (!rf[i] || (key[i] != kk && key[i] != UINT32_MAX))
      continue;
    memset(atoms, 0, A);
    residual_collect_aps(rf[i], cov, atoms);
    bool input_only = true;
    for (uint32_t a = 0; a < A; a++)
      if (atoms[a] && !residual_signal_matches(cov, a, AP_FLAG_INPUT))
        input_only = false;
    if (key[i] == kk || !cov->items[i].assumption_side || !input_only) {
      include[i] = true;
      residual_collect_aps(rf[i], cov, kept);
    }
  }
  bool changed = true;
  while (changed) {
    changed = false;
    for (uint32_t i = 0; i < n; i++) {
      if (!rf[i] || include[i] || key[i] != UINT32_MAX ||
          !residual_aps_hit(rf[i], cov, kept))
        continue;
      include[i] = true;
      changed = true;
      residual_collect_aps(rf[i], cov, kept);
    }
  }
  for (uint32_t i = 0; i < n; i++) {
    if (!rf[i] || include[i] || key[i] != UINT32_MAX)
      continue;
    Role r = cov->items[i].role;
    bool environment = r == TLSF_ROLE_INITIALLY || r == TLSF_ROLE_REQUIRE ||
                       r == TLSF_ROLE_ASSUME;
    assert(environment && cov->items[i].assumption_side);
    if (!environment || !cov->items[i].assumption_side)
      goto done;
    memset(atoms, 0, A);
    residual_collect_aps(rf[i], cov, atoms);
    for (uint32_t a = 0; a < A; a++) {
      if (!atoms[a])
        continue;
      bool independent =
          residual_signal_matches(cov, a, AP_FLAG_INPUT) && !kept[a];
      assert(independent); // Prunable.inputs and Prunable.disjoint
      if (!independent)
        goto done;
    }
    if (!section_pattern_add(&dropped, r, (Node *)rf[i], FCLASS_SAFETY))
      goto done;
  }
  // Empty D needs no solver; uncertainty always falls back to keeping D.
  ok =
      !dropped.count || env_witness_search(&dropped, ENV_WITNESS_WORK_BUDGET) ==
                            ENV_WITNESS_SATISFIABLE;
done:
  arena_free(scratch);
  free(atoms);
  free(kept);
  return ok;
}

bool residual_build_cluster_view(TlsfSpec *spec, ConstraintCover *cov,
                                 const Node **rf, const uint32_t *key,
                                 uint32_t kk, bool all, bool prune, uint32_t n,
                                 bool *seen, SectionPatternView *view) {
  section_pattern_init(view, spec->arena, spec);
  memset(seen, 0, cov->aps.count ? cov->aps.count : 1);
  bool *include = nullptr;
  // prune_realizable covers infinite input-first Mealy games, with both
  // ordinary and strict section objectives. No finite or Moore claim is used.
  if (!all && prune && !semantics_is_finite(spec->info.semantics) &&
      !semantics_is_moore(spec->info.semantics) &&
      spec->info.target == TARGET_MEALY) {
    include = malloc((n ? n : 1) * sizeof(bool));
    if (include &&
        !cluster_assumption_mask(spec, cov, rf, key, kk, n, include)) {
      free(include);
      include = nullptr;
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
      inc = key[i] == kk || key[i] == UINT32_MAX;
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
  if (!root || arena_failed(spec->arena))
    return nullptr;
  if (semantics_is_finite(spec->info.semantics))
    root = apply_rewrites(spec->arena, root,
                          RW_NO_WEAK_UNTIL | RW_NO_STRONG_RELEASE);
  return arena_failed(spec->arena) ? nullptr : root;
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
  if (output_dependent_assumption ||
      semantics_is_finite(cov->spec->info.semantics)) {
    // An assumption mentioning outputs couples the residual games through the
    // antecedent.  If we left the guarantee clusters independent, each cluster
    // would either drop that assumption or synthesize with another cluster's
    // output treated as locally controllable.  Both are unsound, so collapse
    // all output components and attach input-only guarantees to that component.
    // Finite-word controllers also share the choice of where the word ends.
    // proofs/TlsfProofs/Cluster.lean (clusters_realizable) covers infinite
    // words only; proofs/TlsfProofs/Examples.lean (finite_split_fails) shows
    // why finite residuals must likewise stay in one cluster.
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
      // Keep input-only guarantees in the same cluster when assumptions
      // constrain outputs or finite semantics couples the choice of ending.
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
