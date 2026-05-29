#include "tlsf/print_ltlxba.h"

#include <assert.h>

// ---------------------------------------------------------------------------
// Formula printer
// ---------------------------------------------------------------------------
// All output is fully parenthesised.  This avoids any precedence questions
// and makes the output unambiguous for downstream tools.

void print_ltlxba_formula(FILE *out, const Node *n) {
  assert(n);

  switch (n->kind) {
  case NODE_TRUE:
    fprintf(out, "true");
    return;
  case NODE_FALSE:
    fprintf(out, "false");
    return;
  case NODE_AP:
    // AP names are already interned identifiers; print directly.
    fprintf(out, "%s", n->name);
    return;

  // Boolean connectives
  case NODE_NOT:
    fprintf(out, "(!"); print_ltlxba_formula(out, n->arg); fprintf(out, ")");
    return;
  case NODE_AND:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " && ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_OR:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " || ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_IMPL:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " -> ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_EQUIV:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " <-> ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;

  // Temporal: unary
  case NODE_X:
    fprintf(out, "(X "); print_ltlxba_formula(out, n->arg); fprintf(out, ")");
    return;
  case NODE_X_STRONG:
    // ltlxba does not have a standard strong-next symbol; emit X for compat.
    // TODO: check if spot accepts X[!] and emit that instead when targeting spot.
    fprintf(out, "(X "); print_ltlxba_formula(out, n->arg); fprintf(out, ")");
    return;
  case NODE_F:
    fprintf(out, "(F "); print_ltlxba_formula(out, n->arg); fprintf(out, ")");
    return;
  case NODE_G:
    fprintf(out, "(G "); print_ltlxba_formula(out, n->arg); fprintf(out, ")");
    return;

  // Temporal: binary
  case NODE_U:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " U ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_R:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " R ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_W:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " W ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_M:
    fprintf(out, "(");
    print_ltlxba_formula(out, n->lhs);
    fprintf(out, " M ");
    print_ltlxba_formula(out, n->rhs);
    fprintf(out, ")");
    return;

  // These should not appear in expanded+NNF formulas.
  default:
    assert(false && "print_ltlxba: unexpected node kind");
    return;
  }
}

void print_ltlxba_list(FILE *out, Node *const *formulas, uint32_t count) {
  if (count == 0) {
    fprintf(out, "true");
    return;
  }
  if (count == 1) {
    print_ltlxba_formula(out, formulas[0]);
    return;
  }
  fprintf(out, "(");
  for (uint32_t i = 0; i < count; i++) {
    if (i > 0)
      fprintf(out, " && ");
    print_ltlxba_formula(out, formulas[i]);
  }
  fprintf(out, ")");
}

// ---------------------------------------------------------------------------
// Spec-level output
// ---------------------------------------------------------------------------

void print_ltlxba_spec(FILE *out, const TlsfSpec *spec,
                        const ClassifiedSpec *cs, PrintMode mode) {
  (void)spec; // reserved for future use (e.g. signal list comments)

  // Collect guarantee formulas according to mode.
  // Strategy: print  (assumptions) -> (guarantees)
  // if there are no assumptions, print guarantees only.

  // --- collect guarantee nodes ---
  // We need a temporary list; use a fixed-size stack array for small specs,
  // then fall back.  Since we don't have a scratch allocator here, build
  // a simple inline conjunction via recursive calls.

  // Determine which guarantee formulas to include.
  bool print_safety_g = (mode == PRINT_ALL || mode == PRINT_SAFETY);
  bool print_liveness_g = (mode == PRINT_ALL || mode == PRINT_LIVENESS);

  uint32_t g_count = 0;
  for (uint32_t i = 0; i < cs->guarantee_count; i++) {
    FormulaClass cls = cs->guarantees[i].cls;
    if ((cls == FCLASS_SAFETY && print_safety_g) ||
        (cls == FCLASS_LIVENESS && print_liveness_g))
      g_count++;
  }

  // Print:  (assumptions) -> (guarantees)
  // Assumptions = initially ∧ require ∧ assume
  uint32_t a_count = cs->initially_count + cs->require_count + cs->assume_count;

  bool need_impl = (a_count > 0) && (g_count > 0);

  if (need_impl)
    fprintf(out, "(");

  // Assumptions side
  if (a_count > 0) {
    fprintf(out, "(");
    bool first = true;
    for (uint32_t i = 0; i < cs->initially_count; i++) {
      if (!first) fprintf(out, " && ");
      print_ltlxba_formula(out, cs->initially[i]);
      first = false;
    }
    for (uint32_t i = 0; i < cs->require_count; i++) {
      if (!first) fprintf(out, " && ");
      print_ltlxba_formula(out, cs->require[i]);
      first = false;
    }
    for (uint32_t i = 0; i < cs->assume_count; i++) {
      if (!first) fprintf(out, " && ");
      print_ltlxba_formula(out, cs->assume[i]);
      first = false;
    }
    fprintf(out, ")");
    if (need_impl)
      fprintf(out, " -> ");
  }

  // Guarantees side
  if (g_count == 0) {
    fprintf(out, "true");
  } else {
    fprintf(out, "(");
    bool first = true;
    for (uint32_t i = 0; i < cs->guarantee_count; i++) {
      FormulaClass cls = cs->guarantees[i].cls;
      if (!((cls == FCLASS_SAFETY && print_safety_g) ||
            (cls == FCLASS_LIVENESS && print_liveness_g)))
        continue;
      if (!first)
        fprintf(out, " && ");
      print_ltlxba_formula(out, cs->guarantees[i].formula);
      first = false;
    }
    fprintf(out, ")");
  }

  if (need_impl)
    fprintf(out, ")");

  fprintf(out, "\n");
}
