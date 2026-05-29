#ifndef TLSF_PRINT_LTLXBA_H
#define TLSF_PRINT_LTLXBA_H

/// print_ltlxba.h — print LTL formulas in the ltlxba format.
///
/// ltlxba is the format expected by ltl2ba, spot (--formula), and similar
/// tools.  Operators:
///   !φ   &&   ||   ->   <->
///   X φ  F φ  G φ  φ U ψ  φ R ψ  φ W ψ  φ M ψ
///
/// Output is fully parenthesised to avoid any ambiguity.

#include "tlsf/ast.h"
#include "tlsf/classify.h"
#include "tlsf/spec.h"
#include <stdio.h>

/// Print a single formula to `out` in ltlxba format.
void print_ltlxba_formula(FILE *out, const Node *n);

/// Print a conjunction of all formulas in `list` to `out`.
/// Prints "true" for an empty list.
void print_ltlxba_list(FILE *out, Node *const *formulas, uint32_t count);

/// Print the full combined output (assumptions → guarantees, conjoined)
/// in the style expected by synthesis front-ends.
///
/// Mode selects which formulas to emit:
///   PRINT_ALL      : all formulas conjoined (default)
///   PRINT_SAFETY   : safety guarantees only
///   PRINT_LIVENESS : liveness guarantees only
typedef enum PrintMode {
  PRINT_ALL,
  PRINT_SAFETY,
  PRINT_LIVENESS,
} PrintMode;

void print_ltlxba_spec(FILE *out, const TlsfSpec *spec,
                        const ClassifiedSpec *cs, PrintMode mode);

#endif // TLSF_PRINT_LTLXBA_H
