#include "tlsf/print_ltlxba.h"

#include <assert.h>

// ---------------------------------------------------------------------------
// Operator precedence (matches spot / ltl2ba and the TLSF arXiv papers).
//
// Binding strength, tightest first:
//   5  unary:  !  X  F  G   (and X[!])
//   4  binary temporal:  U  R  W  M
//   3  &&
//   2  ||
//   1  ->  <->
// Atoms have "infinite" precedence and never need parentheses.
//
// Associativity: && and || are left-associative; U/R/W/M and ->/<-> are
// right-associative (so `a -> b -> c` is `a -> (b -> c)`).
//
// In the precedence-aware (default) mode a subformula is parenthesised only
// when its operator binds more loosely than the position it sits in.  In full
// mode every compound subformula is parenthesised.
// ---------------------------------------------------------------------------

#define PREC_ATOM 100

static int prec_of(const Node *n) {
  switch (n->kind) {
  case NODE_IMPL:
  case NODE_EQUIV:
    return 1;
  case NODE_OR:
    return 2;
  case NODE_AND:
    return 3;
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return 4;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return 5;
  default:
    return PREC_ATOM;
  }
}

// Forward declaration.
static void emit(FILE *out, const Node *n, int min_prec, bool full);

// Print a unary operator `op` applied to `arg`.  Unary operators are
// right-associative, so the operand is emitted at the operator's own level.
static void emit_unary(FILE *out, const char *op, const Node *arg, bool full) {
  fprintf(out, "%s", op);
  emit(out, arg, 5, full);
}

// Print a binary operator.  `lassoc` selects left- vs right-associativity.
static void emit_binary(FILE *out, const Node *n, const char *op, int prec,
                        bool lassoc, bool full) {
  // left-assoc:  left at `prec`,   right at `prec+1`
  // right-assoc: left at `prec+1`, right at `prec`
  int left_min = lassoc ? prec : prec + 1;
  int right_min = lassoc ? prec + 1 : prec;
  emit(out, n->lhs, left_min, full);
  fprintf(out, "%s", op);
  emit(out, n->rhs, right_min, full);
}

static void emit(FILE *out, const Node *n, int min_prec, bool full) {
  assert(n);

  int p = prec_of(n);
  // Atoms (p == PREC_ATOM) are never wrapped.
  bool paren = (p < PREC_ATOM) && (full || p < min_prec);

  if (paren)
    fputc('(', out);

  switch (n->kind) {
  case NODE_TRUE:  fprintf(out, "true");  break;
  case NODE_FALSE: fprintf(out, "false"); break;
  case NODE_AP:    fprintf(out, "%s", n->name); break;

  case NODE_NOT:      emit_unary(out, "!", n->arg, full); break;
  case NODE_X:        emit_unary(out, "X ", n->arg, full); break;
  // ltlxba has no portable strong-next symbol; emit X for compatibility.
  case NODE_X_STRONG: emit_unary(out, "X ", n->arg, full); break;
  case NODE_F:        emit_unary(out, "F ", n->arg, full); break;
  case NODE_G:        emit_unary(out, "G ", n->arg, full); break;

  case NODE_AND:   emit_binary(out, n, " && ",  3, true,  full); break;
  case NODE_OR:    emit_binary(out, n, " || ",  2, true,  full); break;
  case NODE_IMPL:  emit_binary(out, n, " -> ",  1, false, full); break;
  case NODE_EQUIV: emit_binary(out, n, " <-> ", 1, false, full); break;
  case NODE_U:     emit_binary(out, n, " U ",   4, false, full); break;
  case NODE_R:     emit_binary(out, n, " R ",   4, false, full); break;
  case NODE_W:     emit_binary(out, n, " W ",   4, false, full); break;
  case NODE_M:     emit_binary(out, n, " M ",   4, false, full); break;

  default:
    assert(false && "print_ltlxba: unexpected node kind");
  }

  if (paren)
    fputc(')', out);
}

// ---------------------------------------------------------------------------
// Public formula entry points
// ---------------------------------------------------------------------------

void print_ltlxba_formula(FILE *out, const Node *n, bool full_parens) {
  emit(out, n, 1, full_parens);
}

void print_ltlxba_list(FILE *out, Node *const *formulas, uint32_t count,
                       bool full_parens) {
  if (count == 0) {
    fprintf(out, "true");
    return;
  }
  if (count == 1) {
    emit(out, formulas[0], 1, full_parens);
    return;
  }
  // Conjunction (prec 3); wrap when full, otherwise leave bare at top level.
  if (full_parens)
    fputc('(', out);
  for (uint32_t i = 0; i < count; i++) {
    if (i > 0)
      fprintf(out, " && ");
    emit(out, formulas[i], 4, full_parens); // operand of &&
  }
  if (full_parens)
    fputc(')', out);
}

// ---------------------------------------------------------------------------
// Spec-level output
// ---------------------------------------------------------------------------

// Emit a conjunction of `count` formulas, as it should appear in a position
// requiring precedence `min_prec`.  Prints "true" for the empty conjunction.
static void emit_conjunction(FILE *out, const Node *const *parts,
                             uint32_t count, int min_prec, bool full) {
  if (count == 0) {
    fprintf(out, "true");
    return;
  }
  if (count == 1) {
    emit(out, parts[0], min_prec, full);
    return;
  }
  // The conjunction node has precedence 3; parenthesise if the position binds
  // tighter than &&, or in full mode.
  bool paren = full || (3 < min_prec);
  if (paren)
    fputc('(', out);
  for (uint32_t i = 0; i < count; i++) {
    if (i > 0)
      fprintf(out, " && ");
    emit(out, parts[i], 4, full); // operand of &&
  }
  if (paren)
    fputc(')', out);
}

void print_ltlxba_spec(FILE *out, const TlsfSpec *spec,
                       const ClassifiedSpec *cs, PrintMode mode,
                       bool full_parens) {
  (void)spec; // reserved for future use (e.g. signal list comments)

  bool print_safety_g = (mode == PRINT_ALL || mode == PRINT_SAFETY);
  bool print_liveness_g = (mode == PRINT_ALL || mode == PRINT_LIVENESS);

  // --- Collect the selected guarantee formulas into a small array. ---
  const Node **gbuf = nullptr;
  uint32_t g_count = 0;
  if (cs->guarantee_count > 0) {
    gbuf = ARENA_ALLOC_N(spec->arena, const Node *, cs->guarantee_count);
    for (uint32_t i = 0; i < cs->guarantee_count; i++) {
      FormulaClass cls = cs->guarantees[i].cls;
      if ((cls == FCLASS_SAFETY && print_safety_g) ||
          (cls == FCLASS_LIVENESS && print_liveness_g))
        gbuf[g_count++] = cs->guarantees[i].formula;
    }
  }

  // --- Collect the assumption formulas (initially ∧ require ∧ assume). ---
  uint32_t a_count = cs->initially_count + cs->require_count + cs->assume_count;
  const Node **abuf = nullptr;
  if (a_count > 0) {
    abuf = ARENA_ALLOC_N(spec->arena, const Node *, a_count);
    uint32_t k = 0;
    for (uint32_t i = 0; i < cs->initially_count; i++)
      abuf[k++] = cs->initially[i];
    for (uint32_t i = 0; i < cs->require_count; i++)
      abuf[k++] = cs->require[i];
    for (uint32_t i = 0; i < cs->assume_count; i++)
      abuf[k++] = cs->assume[i];
  }

  bool need_impl = (a_count > 0) && (g_count > 0);

  if (need_impl) {
    // (assumptions) -> (guarantees).  '->' is right-associative at prec 1:
    // the left side sits at prec 2, the right side at prec 1.
    if (full_parens)
      fputc('(', out);
    emit_conjunction(out, abuf, a_count, 2, full_parens);
    fprintf(out, " -> ");
    emit_conjunction(out, gbuf, g_count, 1, full_parens);
    if (full_parens)
      fputc(')', out);
  } else if (a_count > 0) {
    // Assumptions only.
    emit_conjunction(out, abuf, a_count, 1, full_parens);
  } else {
    // Guarantees only (or empty → "true").
    emit_conjunction(out, gbuf, g_count, 1, full_parens);
  }

  fprintf(out, "\n");
}
