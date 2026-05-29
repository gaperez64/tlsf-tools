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

// Fold formulas into a conjunction; returns nullptr for the empty set
// (meaning "absent", so it drops out of the surrounding structure).
static Node *conj_of(Arena *a, Node *const *xs, uint32_t n) {
  if (n == 0)
    return nullptr;
  Node *acc = xs[0];
  for (uint32_t i = 1; i < n; i++)
    acc = node_and(a, acc, xs[i]);
  return acc;
}

static Node *and_opt(Arena *a, Node *x, Node *y) {
  if (!x)
    return y;
  if (!y)
    return x;
  return node_and(a, x, y);
}

// Build the TLSF specification formula (arXiv semantics):
//
//   (INITIALLY ∧ G REQUIRE ∧ ASSUME)  →  (PRESET ∧ G ASSERT ∧ GUARANTEE)
//
// Each section is the conjunction of its formulas; empty sections drop out,
// and a trivial antecedent collapses to just the consequent.  REQUIRE and
// ASSERT (invariants) are wrapped in G.  The safety/liveness mode selects
// which guarantees appear, and (for liveness) drops the safety-only system
// sections PRESET and ASSERT.
void print_ltlxba_spec(FILE *out, const TlsfSpec *spec,
                       const ClassifiedSpec *cs, PrintMode mode,
                       bool full_parens) {
  Arena *a = spec->arena;
  bool want_safety = (mode == PRINT_ALL || mode == PRINT_SAFETY);
  bool want_liveness = (mode == PRINT_ALL || mode == PRINT_LIVENESS);

  // Environment antecedent: INITIALLY ∧ G(REQUIRE) ∧ ASSUME.
  Node *e_init = conj_of(a, cs->initially, cs->initially_count);
  Node *e_req = conj_of(a, cs->require, cs->require_count);
  if (e_req)
    e_req = node_g(a, e_req);
  Node *e_asu = conj_of(a, cs->assume, cs->assume_count);
  Node *e = and_opt(a, and_opt(a, e_init, e_req), e_asu);

  // System consequent: PRESET ∧ G(ASSERT) ∧ (selected) GUARANTEE.
  Node *s_pre = want_safety ? conj_of(a, cs->preset, cs->preset_count) : nullptr;

  Node *s_asr = nullptr;
  if (want_safety && cs->assert_count > 0) {
    Node **ab = ARENA_ALLOC_N(a, Node *, cs->assert_count);
    for (uint32_t i = 0; i < cs->assert_count; i++)
      ab[i] = cs->asserts[i].formula;
    s_asr = node_g(a, conj_of(a, ab, cs->assert_count));
  }

  Node *s_gua = nullptr;
  if (cs->guarantee_count > 0) {
    Node **gb = ARENA_ALLOC_N(a, Node *, cs->guarantee_count);
    uint32_t gn = 0;
    for (uint32_t i = 0; i < cs->guarantee_count; i++) {
      FormulaClass cls = cs->guarantees[i].cls;
      if ((cls == FCLASS_SAFETY && want_safety) ||
          (cls == FCLASS_LIVENESS && want_liveness))
        gb[gn++] = cs->guarantees[i].formula;
    }
    s_gua = conj_of(a, gb, gn);
  }

  Node *s = and_opt(a, and_opt(a, s_pre, s_asr), s_gua);

  // Assemble:  no consequent → true;  no antecedent → S;  else E → S.
  Node *root;
  if (!s)
    root = node_true(a);
  else if (!e)
    root = s;
  else
    root = node_impl(a, e, s);

  emit(out, root, 1, full_parens);
  fprintf(out, "\n");
}
