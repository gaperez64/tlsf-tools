#include "tlsf/gr.h"

// ---------------------------------------------------------------------------
// Boolean / transition-predicate tests
// ---------------------------------------------------------------------------

// A purely propositional (Boolean) formula: Boolean connectives over atoms,
// no temporal operators.
static bool is_prop(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return is_prop(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return is_prop(n->lhs) && is_prop(n->rhs);
  default:
    return false;
  }
}

// A transition predicate: Boolean over the current values and the next (a
// single X) values of the signals — i.e. Boolean connectives over atoms and
// X(propositional).  No deeper or other temporal nesting.
static bool is_trans(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return is_trans(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return is_trans(n->lhs) && is_trans(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    return is_prop(n->arg);
  default:
    return false;
  }
}

// ---------------------------------------------------------------------------
// Conjunct classification
// ---------------------------------------------------------------------------

typedef enum { GR_INIT, GR_SAFETY, GR_JUSTICE, GR_OTHER } GrClass;

// Classify a general formula (ASSUME / GUARANTEE, and INITIALLY/PRESET which
// must be purely initial).
static GrClass classify_general(const Node *n) {
  if (is_prop(n))
    return GR_INIT;
  if (n->kind == NODE_G) {
    const Node *a = n->arg;
    if (a->kind == NODE_F && is_trans(a->arg))
      return GR_JUSTICE; // G F b
    if (a->kind == NODE_G)
      return classify_general(a); // G G ... — collapse
    if (is_trans(a))
      return GR_SAFETY; // G b
  }
  return GR_OTHER;
}

// Classify an invariant-section formula (REQUIRE / ASSERT): the formula f
// stands for G f.
static GrClass classify_invariant(const Node *f) {
  if (is_trans(f))
    return GR_SAFETY; // G(transition)
  if (f->kind == NODE_F && is_trans(f->arg))
    return GR_JUSTICE; // G F b
  if (f->kind == NODE_G)
    return classify_general(f); // G f with f already temporal
  return GR_OTHER;
}

// Initial-section formula (INITIALLY / PRESET): must be propositional.
static GrClass classify_initial(const Node *f) {
  return is_prop(f) ? GR_INIT : GR_OTHER;
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

// Classify a formula, flattening a top-level conjunction into its conjuncts
// (a section formula may be a single `G a && G b && ...`).  Returns false if
// any conjunct is outside the GR fragment; otherwise sets *has_justice when a
// justice conjunct is present.
static bool check_formula(const Node *n, GrClass (*classify)(const Node *),
                          bool *has_justice) {
  if (n->kind == NODE_AND)
    return check_formula(n->lhs, classify, has_justice) &&
           check_formula(n->rhs, classify, has_justice);
  GrClass c = classify(n);
  if (c == GR_OTHER)
    return false;
  if (c == GR_JUSTICE)
    *has_justice = true;
  return true;
}

int gr_level(const TlsfSpec *spec) {
  bool has_justice = false;

  struct {
    const FormulaList *list;
    GrClass (*classify)(const Node *);
  } groups[] = {
      {&spec->initially, classify_initial},
      {&spec->preset, classify_initial},
      {&spec->require, classify_invariant},
      {&spec->assert_, classify_invariant},
      {&spec->assume, classify_general},
      {&spec->guarantee, classify_general},
  };

  for (size_t g = 0; g < sizeof groups / sizeof groups[0]; g++) {
    const FormulaList *l = groups[g].list;
    for (uint32_t i = 0; i < l->count; i++)
      if (!check_formula(l->formulas[i], groups[g].classify, &has_justice))
        return -1;
  }

  return has_justice ? 1 : 0;
}
