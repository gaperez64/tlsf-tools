#include "tlsf/print_ltlxba.h"

#include <assert.h>
#include <ctype.h>

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
//
// The precedence and parenthesisation logic is dialect-independent; only the
// operator spellings differ (see LtlSyntax below).
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

// ---------------------------------------------------------------------------
// Dialect spelling tables
// ---------------------------------------------------------------------------

typedef struct LtlSyntax {
  const char *t_true, *t_false;
  // Unary (spelling includes any required trailing separator).
  const char *op_not, *op_x, *op_xstrong_inf, *op_xstrong_fin, *op_f, *op_g;
  // Binary boolean / temporal (spelling includes surrounding spaces).
  const char *op_and, *op_or, *op_impl, *op_equiv;
  const char *op_u, *op_r, *op_w, *op_m;
  // Atom renderer (handles any escaping the dialect needs).
  void (*emit_atom)(FILE *out, const char *name);
} LtlSyntax;

static void atom_plain(FILE *out, const char *name) {
  fprintf(out, "%s", name);
}

// ltlsynt / ltl2ba read uppercase letters as operators, so atoms are lowercased
// for the ltlxba dialect on request (as `syfco -f ltlxba` does).
static void atom_lower(FILE *out, const char *name) {
  for (const char *p = name; *p; p++)
    fputc(tolower((unsigned char)*p), out);
}

// LaTeX math: wrap in \mathit{} and escape underscores; primes pass through.
static void atom_latex(FILE *out, const char *name) {
  fputs("\\mathit{", out);
  for (const char *p = name; *p; p++) {
    if (*p == '_')
      fputs("\\_", out);
    else
      fputc(*p, out);
  }
  fputc('}', out);
}

// ltl2ba / spot ASCII (the historical default).
static const LtlSyntax SYNTAX_LTLXBA = {
    .t_true = "true",
    .t_false = "false",
    .op_not = "!",
    .op_x = "X ",
    .op_xstrong_inf = "X ",
    .op_xstrong_fin = "X[!] ",
    .op_f = "F ",
    .op_g = "G ",
    .op_and = " && ",
    .op_or = " || ",
    .op_impl = " -> ",
    .op_equiv = " <-> ",
    .op_u = " U ",
    .op_r = " R ",
    .op_w = " W ",
    .op_m = " M ",
    .emit_atom = atom_plain,
};

// Pure-LTL ASCII, matching `syfco -f ltl` (keeps W/R/M unrewritten).
// Currently identical to ltlxba; kept distinct so the two can diverge (e.g.
// should ltlxba ever rewrite W for classic ltl2ba).
static const LtlSyntax SYNTAX_LTL = {
    .t_true = "true",
    .t_false = "false",
    .op_not = "!",
    .op_x = "X ",
    .op_xstrong_inf = "X ",
    .op_xstrong_fin = "X[!] ",
    .op_f = "F ",
    .op_g = "G ",
    .op_and = " && ",
    .op_or = " || ",
    .op_impl = " -> ",
    .op_equiv = " <-> ",
    .op_u = " U ",
    .op_r = " R ",
    .op_w = " W ",
    .op_m = " M ",
    .emit_atom = atom_plain,
};

// LaTeX math symbols.
static const LtlSyntax SYNTAX_LATEX = {
    .t_true = "\\top",
    .t_false = "\\bot",
    .op_not = "\\lnot ",
    .op_x = "\\mathsf{X} ",
    .op_xstrong_inf = "\\mathsf{X} ",
    .op_xstrong_fin = "\\mathsf{X}_{!} ",
    .op_f = "\\mathsf{F} ",
    .op_g = "\\mathsf{G} ",
    .op_and = " \\land ",
    .op_or = " \\lor ",
    .op_impl = " \\rightarrow ",
    .op_equiv = " \\leftrightarrow ",
    .op_u = " \\mathbin{\\mathsf{U}} ",
    .op_r = " \\mathbin{\\mathsf{R}} ",
    .op_w = " \\mathbin{\\mathsf{W}} ",
    .op_m = " \\mathbin{\\mathsf{M}} ",
    .emit_atom = atom_latex,
};

static const LtlSyntax *syntax_for(LtlFormat fmt) {
  switch (fmt) {
  case LTL_FMT_LTL:
    return &SYNTAX_LTL;
  case LTL_FMT_LATEX:
    return &SYNTAX_LATEX;
  case LTL_FMT_LTLXBA:
  default:
    return &SYNTAX_LTLXBA;
  }
}

// ---------------------------------------------------------------------------
// Emitter
// ---------------------------------------------------------------------------

// Forward declaration.
static void emit(FILE *out, const Node *n, int min_prec, bool full, bool finite,
                 const LtlSyntax *s);

// Print a unary operator `op` applied to `arg`.  Unary operators are
// right-associative, so the operand is emitted at the operator's own level.
static void emit_unary(FILE *out, const char *op, const Node *arg, bool full,
                       bool finite, const LtlSyntax *s) {
  fprintf(out, "%s", op);
  emit(out, arg, 5, full, finite, s);
}

// Print a binary operator.  `lassoc` selects left- vs right-associativity.
static void emit_binary(FILE *out, const Node *n, const char *op, int prec,
                        bool lassoc, bool full, bool finite,
                        const LtlSyntax *s) {
  // left-assoc:  left at `prec`,   right at `prec+1`
  // right-assoc: left at `prec+1`, right at `prec`
  int left_min = lassoc ? prec : prec + 1;
  int right_min = lassoc ? prec + 1 : prec;
  emit(out, n->lhs, left_min, full, finite, s);
  fprintf(out, "%s", op);
  emit(out, n->rhs, right_min, full, finite, s);
}

// `finite` selects finite-word (LTLf) rendering: the strong next X[!] is kept
// distinct from the weak next X (they coincide on infinite words, so for
// infinite semantics both print as X).
static void emit(FILE *out, const Node *n, int min_prec, bool full, bool finite,
                 const LtlSyntax *s) {
  assert(n);

  int p = prec_of(n);
  // Atoms (p == PREC_ATOM) are never wrapped.
  bool paren = (p < PREC_ATOM) && (full || p < min_prec);

  if (paren)
    fputc('(', out);

  switch (n->kind) {
  case NODE_TRUE:
    fprintf(out, "%s", s->t_true);
    break;
  case NODE_FALSE:
    fprintf(out, "%s", s->t_false);
    break;
  case NODE_AP:
    s->emit_atom(out, n->name);
    break;

  case NODE_NOT:
    emit_unary(out, s->op_not, n->arg, full, finite, s);
    break;
  case NODE_X:
    emit_unary(out, s->op_x, n->arg, full, finite, s);
    break;
  // Strong next: X[!] under finite-word semantics, plain X otherwise (the two
  // agree on infinite words).
  case NODE_X_STRONG:
    emit_unary(out, finite ? s->op_xstrong_fin : s->op_xstrong_inf, n->arg,
               full, finite, s);
    break;
  case NODE_F:
    emit_unary(out, s->op_f, n->arg, full, finite, s);
    break;
  case NODE_G:
    emit_unary(out, s->op_g, n->arg, full, finite, s);
    break;

  case NODE_AND:
    emit_binary(out, n, s->op_and, 3, true, full, finite, s);
    break;
  case NODE_OR:
    emit_binary(out, n, s->op_or, 2, true, full, finite, s);
    break;
  case NODE_IMPL:
    emit_binary(out, n, s->op_impl, 1, false, full, finite, s);
    break;
  case NODE_EQUIV:
    emit_binary(out, n, s->op_equiv, 1, false, full, finite, s);
    break;
  case NODE_U:
    emit_binary(out, n, s->op_u, 4, false, full, finite, s);
    break;
  case NODE_R:
    emit_binary(out, n, s->op_r, 4, false, full, finite, s);
    break;
  case NODE_W:
    emit_binary(out, n, s->op_w, 4, false, full, finite, s);
    break;
  case NODE_M:
    emit_binary(out, n, s->op_m, 4, false, full, finite, s);
    break;

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
  emit(out, n, 1, full_parens, /*finite=*/false, &SYNTAX_LTLXBA);
}

void print_ltlxba_list(FILE *out, Node *const *formulas, uint32_t count,
                       bool full_parens) {
  if (count == 0) {
    fprintf(out, "true");
    return;
  }
  if (count == 1) {
    emit(out, formulas[0], 1, full_parens, /*finite=*/false, &SYNTAX_LTLXBA);
    return;
  }
  // Conjunction (prec 3); wrap when full, otherwise leave bare at top level.
  if (full_parens)
    fputc('(', out);
  for (uint32_t i = 0; i < count; i++) {
    if (i > 0)
      fprintf(out, " && ");
    // operand of &&
    emit(out, formulas[i], 4, full_parens, /*finite=*/false, &SYNTAX_LTLXBA);
  }
  if (full_parens)
    fputc(')', out);
}

void print_ltl(FILE *out, const Node *root, LtlFormat fmt, bool full_parens,
               bool finite, bool lower_atoms) {
  LtlSyntax s = *syntax_for(fmt);
  if (lower_atoms)
    s.emit_atom = atom_lower;
  emit(out, root, 1, full_parens, finite, &s);
  fprintf(out, "\n");
}

// ---------------------------------------------------------------------------
// Spec-level formula assembly
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

// Conjunction of the guarantee-section formulas whose class is selected.
static Node *guarantees_of(Arena *a, const ClassifiedSpec *cs, bool safety,
                           bool liveness) {
  if (cs->guarantee_count == 0)
    return nullptr;
  Node **gb = ARENA_ALLOC_N(a, Node *, cs->guarantee_count);
  uint32_t gn = 0;
  for (uint32_t i = 0; i < cs->guarantee_count; i++) {
    FormulaClass cls = cs->guarantees[i].cls;
    if ((cls == FCLASS_SAFETY && safety) ||
        (cls == FCLASS_LIVENESS && liveness))
      gb[gn++] = cs->guarantees[i].formula;
  }
  return conj_of(a, gb, gn);
}

// Conjunction of ASSERT formulas, or nullptr if there are none.
static Node *assert_conj(Arena *a, const ClassifiedSpec *cs) {
  if (cs->assert_count == 0)
    return nullptr;
  Node **ab = ARENA_ALLOC_N(a, Node *, cs->assert_count);
  for (uint32_t i = 0; i < cs->assert_count; i++)
    ab[i] = cs->asserts[i].formula;
  return conj_of(a, ab, cs->assert_count);
}

// G(conj of ASSERT formulas), or nullptr if there are none.
static Node *assert_inv(Arena *a, const ClassifiedSpec *cs) {
  Node *asserts = assert_conj(a, cs);
  return asserts ? node_g(a, asserts) : nullptr;
}

// Build the TLSF specification formula.
//
// Standard (non-strict) semantics — the TLSF default (matches syfco):
//   INITIALLY → ( PRESET ∧ ( (G REQUIRE ∧ ASSUME) → (G ASSERT ∧ GUARANTEE) ) )
//
// Strict semantics — TLSF §3.2:
//   INITIALLY → ( PRESET ∧ (ASSERT W ¬REQUIRE) ∧
//                 ( (G REQUIRE ∧ ASSUME) → GUARANTEE ) )
// The weak-until is over the raw ASSERT/REQUIRE invariants; PRESET is a plain
// step-0 conjunct.  If there is no REQUIRE, ¬REQUIRE is false and the
// weak-until collapses to G ASSERT.
//
// Each section is the conjunction of its formulas; empty parts drop out and
// trivial implications collapse.  The safety/liveness mode selects which
// guarantees appear (and, for liveness, drops the safety-only sections).
//
// Strict-vs-non-strict follows the (possibly overridden) SEMANTICS field.  To
// relax a strict spec to the plain E -> S formula, overwrite the semantics to a
// non-strict one.
Node *build_spec_formula(const TlsfSpec *spec, const ClassifiedSpec *cs,
                         PrintMode mode) {
  Arena *a = spec->arena;
  bool strict = semantics_is_strict(spec->info.semantics);
  bool want_safety = (mode == PRINT_ALL || mode == PRINT_SAFETY);
  bool want_liveness = (mode == PRINT_ALL || mode == PRINT_LIVENESS);

  // Environment antecedent pieces.  REQUIRE is used both raw (strict W) and
  // G-wrapped (assumption antecedent).
  Node *e_init = conj_of(a, cs->initially, cs->initially_count);
  Node *req_raw = conj_of(a, cs->require, cs->require_count);
  Node *e_req = req_raw ? node_g(a, req_raw) : nullptr;
  Node *a_live = conj_of(a, cs->assume, cs->assume_count);
  Node *s_pre = conj_of(a, cs->preset, cs->preset_count);

  Node *root;
  if (strict) {
    // Safety: ASSERT W ¬REQUIRE, dropped if there are no ASSERT invariants.
    Node *safety_part = nullptr;
    Node *assert_raw = want_safety ? assert_conj(a, cs) : nullptr;
    if (want_safety && assert_raw)
      safety_part = req_raw ? node_w(a, assert_raw, node_not(a, req_raw))
                            : node_g(a, assert_raw);

    // Guarantees: (G REQUIRE ∧ ASSUME) → GUARANTEE.
    Node *env = and_opt(a, e_req, a_live);
    Node *g_gua = guarantees_of(a, cs, want_safety, want_liveness);
    Node *gua_part = g_gua ? (env ? node_impl(a, env, g_gua) : g_gua) : nullptr;

    Node *sys_safety = and_opt(a, want_safety ? s_pre : nullptr, safety_part);
    Node *body = and_opt(a, sys_safety, gua_part);
    if (body)
      root = e_init ? node_impl(a, e_init, body) : body;
    else
      root = node_true(a);
  } else {
    // Non-strict (the TLSF section semantics, as implemented by syfco):
    //   INITIALLY → ( PRESET ∧ ( (G REQUIRE ∧ ASSUME) → (G ASSERT ∧ GUARANTEE)
    //   ) )
    // INITIALLY is the outer guard and PRESET sits *outside* the
    // assumption→guarantee implication, so the system's PRESET/initial
    // obligations stand even on inputs where the environment violates an
    // assumption.  (Lumping INITIALLY into the antecedent and PRESET into the
    // consequent — `(I ∧ G R ∧ As) → (P ∧ G A ∧ Gu)` — drops that obligation
    // and is *not* equivalent.)
    Node *env = and_opt(a, e_req, a_live); // G REQUIRE ∧ ASSUME (no INITIALLY)
    Node *g_assert = want_safety ? assert_inv(a, cs) : nullptr; // G ASSERT
    Node *g_gua = guarantees_of(a, cs, want_safety, want_liveness);
    Node *sys = and_opt(a, g_assert, g_gua); // G ASSERT ∧ GUARANTEE
    Node *inner = sys ? (env ? node_impl(a, env, sys) : sys) : nullptr;
    Node *body = and_opt(a, want_safety ? s_pre : nullptr, inner); // PRESET ∧ …
    if (e_init)
      root = body ? node_impl(a, e_init, body) : node_true(a);
    else
      root = body ? body : node_true(a);
  }
  return root;
}

void print_ltlxba_spec(FILE *out, const TlsfSpec *spec,
                       const ClassifiedSpec *cs, PrintMode mode,
                       bool full_parens) {
  Node *root = build_spec_formula(spec, cs, mode);
  bool finite = semantics_is_finite(spec->info.semantics);
  print_ltl(out, root, LTL_FMT_LTLXBA, full_parens, finite,
            /*lower_atoms=*/false);
}
