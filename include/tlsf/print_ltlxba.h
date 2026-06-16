#ifndef TLSF_PRINT_LTLXBA_H
#define TLSF_PRINT_LTLXBA_H

/// print_ltlxba.h — print LTL formulas in the ltlxba format.
///
/// ltlxba is the format expected by ltl2ba, spot (--formula), and similar
/// tools.  Operators:
///   !φ   &&   ||   ->   <->
///   X φ  F φ  G φ  φ U ψ  φ R ψ  φ W ψ  φ M ψ
///
/// By default output uses the minimal parentheses required by the operator
/// precedence shared by spot/ltl2ba and the TLSF arXiv papers (tightest
/// first):  unary (! X F G) > U R W M > && > || > -> <->.  Passing
/// full_parens=true parenthesises every compound subformula instead.

#include "tlsf/ast.h"
#include "tlsf/classify.h"
#include "tlsf/spec.h"
#include <stdbool.h>
#include <stdio.h>

/// Output dialect for LTL formulas.  All three share the same precedence and
/// parenthesisation logic; they differ only in operator spelling.
///   LTL_FMT_LTLXBA : ltl2ba / spot ASCII (default)
///   LTL_FMT_LTL    : pure-LTL ASCII, matching `syfco -f ltl`
///   LTL_FMT_LATEX  : LaTeX math (e.g. \land, \mathsf{G}, ...)
typedef enum LtlFormat {
  LTL_FMT_LTLXBA,
  LTL_FMT_LTL,
  LTL_FMT_LATEX,
} LtlFormat;

/// Mode selects which guarantees the assembled spec formula includes:
///   PRINT_ALL      : all formulas conjoined (default)
///   PRINT_SAFETY   : safety guarantees only
///   PRINT_LIVENESS : liveness guarantees only
typedef enum PrintMode {
  PRINT_ALL,
  PRINT_SAFETY,
  PRINT_LIVENESS,
} PrintMode;

/// Print a single formula to `out` in ltlxba format.
void print_ltlxba_formula(FILE *out, const Node *n, bool full_parens);

/// Print a conjunction of all formulas in `list` to `out`.
/// Prints "true" for an empty list.
void print_ltlxba_list(FILE *out, Node *const *formulas, uint32_t count,
                       bool full_parens);

/// Assemble the single LTL formula defined by the (classified) spec, applying
/// the strict / non-strict, safety/liveness and finite-word structure.  The
/// returned node is allocated in `spec->arena`; never nullptr (an empty spec
/// yields node_true).  This is the formula that downstream transforms and
/// printers operate on.
[[nodiscard]] Node *build_spec_formula(const TlsfSpec *spec,
                                       const ClassifiedSpec *cs,
                                       PrintMode mode);

/// Print a single (already-assembled) formula in the given dialect, followed by
/// a newline.  `full_parens` fully parenthesises; `finite` selects finite-word
/// rendering of the strong next (X[!]).  `lower_atoms` lowercases atom names --
/// spot/ltl2ba treat uppercase letters as operators, so the ltlxba dialect
/// needs this to be consumable by ltlsynt (matching `syfco -f ltlxba`).
void print_ltl(FILE *out, const Node *root, LtlFormat fmt, bool full_parens,
               bool finite, bool lower_atoms);

/// Convenience: assemble the spec formula (ltlxba dialect) and print it.
/// Retained for callers that do not apply transforms.
void print_ltlxba_spec(FILE *out, const TlsfSpec *spec,
                       const ClassifiedSpec *cs, PrintMode mode,
                       bool full_parens);

#endif // TLSF_PRINT_LTLXBA_H
