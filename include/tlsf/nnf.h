#ifndef TLSF_NNF_H
#define TLSF_NNF_H

/// nnf.h — negation normal form transform.
///
/// to_nnf() rewrites a formula so that:
///   - NOT only appears directly before atomic propositions (NODE_AP,
///     NODE_TRUE, NODE_FALSE).
///   - IMPL and EQUIV are eliminated.
///   - Dual operators replace NOT-wrapped modalities:
///       ¬(φ U ψ) → (¬φ) R (¬ψ)
///       ¬(φ W ψ) → (¬φ) M (¬ψ)
///       ¬(G φ)   → F (¬φ)
///       ¬(F φ)   → G (¬φ)
///       ¬(X φ)   → X (¬φ)   [X commutes with negation]
///
/// The transform allocates new nodes from the arena; the original nodes
/// are not modified (they remain reachable from the arena but unreferenced).
/// Returns nullptr on OOM.

#include "tlsf/arena.h"
#include "tlsf/ast.h"

/// Convert `n` to negation normal form.
/// `polarity` is true for positive context, false for negative.
/// Callers should pass polarity=true for a top-level formula.
[[nodiscard]] Node *to_nnf(Arena *a, Node *n, bool polarity);

#endif // TLSF_NNF_H
