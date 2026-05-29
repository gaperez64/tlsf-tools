#include "tlsf/classify.h"

#include <assert.h>

// ---------------------------------------------------------------------------
// Single-formula classification
// ---------------------------------------------------------------------------

// Returns true if the subtree rooted at n contains any liveness modality
// (NODE_F, NODE_U, NODE_M).  In NNF, these are the only liveness indicators.
static bool has_liveness(const Node *n) {
  if (!n)
    return false;

  switch (n->kind) {
  // Liveness modalities
  case NODE_F:
  case NODE_U:
  case NODE_M:
    return true;

  // Safety-compatible temporal operators: recurse.
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_G:
    return has_liveness(n->arg);

  case NODE_R:
  case NODE_W:
    return has_liveness(n->lhs) || has_liveness(n->rhs);

  // Boolean: recurse.
  case NODE_NOT:
    // In NNF, NOT only wraps APs.  But be defensive and recurse anyway.
    return has_liveness(n->arg);

  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return has_liveness(n->lhs) || has_liveness(n->rhs);

  // Leaves: never liveness.
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
  case NODE_INT:
    return false;

  // High-level nodes: should not appear after expand()+to_nnf().
  default:
    assert(false && "classify: unexpected high-level node (run expand first)");
    return false;
  }
}

FormulaClass classify_formula(const Node *n) {
  return has_liveness(n) ? FCLASS_LIVENESS : FCLASS_SAFETY;
}

// ---------------------------------------------------------------------------
// Spec-level classification
// ---------------------------------------------------------------------------

static bool fill_classified(TlsfSpec *spec, FormulaList *src,
                             ClassifiedFormula **out, uint32_t *count) {
  if (src->count == 0) {
    *out = nullptr;
    *count = 0;
    return true;
  }

  ClassifiedFormula *arr =
      ARENA_ALLOC_N(spec->arena, ClassifiedFormula, src->count);
  if (!arr)
    return false;

  for (uint32_t i = 0; i < src->count; i++) {
    arr[i].formula = src->formulas[i];
    arr[i].cls = classify_formula(src->formulas[i]);
  }

  *out = arr;
  *count = src->count;
  return true;
}

ClassifiedSpec *classify_spec(TlsfSpec *spec) {
  assert(spec);

  ClassifiedSpec *cs = ARENA_ALLOC(spec->arena, ClassifiedSpec);
  if (!cs)
    return nullptr;

  if (!fill_classified(spec, &spec->guarantee, &cs->guarantees,
                        &cs->guarantee_count))
    return nullptr;

  if (!fill_classified(spec, &spec->assert_, &cs->asserts,
                        &cs->assert_count))
    return nullptr;

  // Environment subsections: just alias the pointer arrays.
  cs->initially = spec->initially.formulas;
  cs->initially_count = spec->initially.count;
  cs->preset = spec->preset.formulas;
  cs->preset_count = spec->preset.count;
  cs->require = spec->require.formulas;
  cs->require_count = spec->require.count;
  cs->assume = spec->assume.formulas;
  cs->assume_count = spec->assume.count;

  return cs;
}
