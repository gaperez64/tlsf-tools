#ifndef TLSF_PRINT_LTLXBA_H
#define TLSF_PRINT_LTLXBA_H

/// print_ltlxba.h — print LTL formulas in the ltlxba format.
///
/// ltlxba is the format expected by ltl2ba, ASCII LTL consumers, and similar
/// tools.  Operators:
///   !φ   &&   ||   ->   <->
///   X φ  F φ  G φ  φ U ψ  φ R ψ  φ W ψ  φ M ψ
///
/// By default output uses the minimal parentheses required by the operator
/// precedence shared by ASCII LTL and the TLSF arXiv papers (tightest
/// first):  unary (! X F G) > U R W M > && > || > -> <->.  Passing
/// full_parens=true parenthesises every compound subformula instead.

#include "tlsf/ast.h"
#include "classify.h"
#include "tlsf/spec.h"
#include <stdbool.h>
#include <stdio.h>

/// Output dialect for LTL formulas.  All three share the same precedence and
/// parenthesisation logic; they differ only in operator spelling.
///   LTL_FMT_LTLXBA : ASCII LTL (default)
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

/// Assemble the single LTL formula defined by the (classified) spec, applying
/// the strict / non-strict, safety/liveness and finite-word structure.  The
/// returned node is allocated in `spec->arena`; nullptr on failure (an empty
/// spec yields node_true). This is the formula that downstream transforms and
/// printers operate on.
[[nodiscard]] Node *build_spec_formula(const TlsfSpec *spec,
                                       const ClassifiedSpec *cs,
                                       PrintMode mode);

/// Print a single (already-assembled) formula in the given dialect, followed by
/// a newline.  `full_parens` fully parenthesises; `finite` selects finite-word
/// rendering of the strong next (X[!]).  `lower_atoms` lowercases atom names --
/// an optional compatibility convention for classic ltl2ba/SyFCo workflows.
/// The quoted dialect accepts case-preserving TLSF identifiers.
[[nodiscard]] bool print_ltl(FILE *out, const Node *root, LtlFormat fmt,
                             bool full_parens, bool finite, bool lower_atoms);

/// Print LTL input with quoted atoms, preserving names such as Grant (which
/// a classic unquoted parser otherwise reads as G rant). Includes a trailing
/// newline.
[[nodiscard]] bool print_quoted_ltl(FILE *out, const Node *root, bool finite,
                                    bool lower_atoms);

#endif // TLSF_PRINT_LTLXBA_H
