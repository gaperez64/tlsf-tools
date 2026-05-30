#include "tlsf/nnf.h"

#include <assert.h>

// to_nnf is a single recursive descent.
// polarity=true  means the formula appears under an even number of negations.
// polarity=false means it appears under an odd number (effectively negated).

Node *to_nnf(Arena *a, Node *n, bool polarity) {
  assert(n);

  switch (n->kind) {

  // -------------------------------------------------------------------------
  // Atoms: apply negation directly if polarity is negative.
  // -------------------------------------------------------------------------
  case NODE_TRUE:
    return polarity ? node_true(a) : node_false(a);
  case NODE_FALSE:
    return polarity ? node_false(a) : node_true(a);
  case NODE_AP:
    if (polarity)
      return node_ap(a, n->name);
    return node_not(a, node_ap(a, n->name));

  // -------------------------------------------------------------------------
  // NOT: flip polarity, recurse into argument.
  // -------------------------------------------------------------------------
  case NODE_NOT:
    return to_nnf(a, n->arg, !polarity);

  // -------------------------------------------------------------------------
  // Boolean connectives.
  // De Morgan at negative polarity:
  //   ¬(φ ∧ ψ) → ¬φ ∨ ¬ψ
  //   ¬(φ ∨ ψ) → ¬φ ∧ ¬ψ
  // -------------------------------------------------------------------------
  case NODE_AND: {
    Node *l = to_nnf(a, n->lhs, polarity);
    Node *r = to_nnf(a, n->rhs, polarity);
    return polarity ? node_and(a, l, r) : node_or(a, l, r);
  }
  case NODE_OR: {
    Node *l = to_nnf(a, n->lhs, polarity);
    Node *r = to_nnf(a, n->rhs, polarity);
    return polarity ? node_or(a, l, r) : node_and(a, l, r);
  }

  // IMPL: φ → ψ  ≡  ¬φ ∨ ψ
  case NODE_IMPL: {
    Node *l = to_nnf(a, n->lhs, !polarity); // φ negated
    Node *r = to_nnf(a, n->rhs, polarity);
    return polarity ? node_or(a, l, r) : node_and(a, l, r);
  }

  // EQUIV: φ ↔ ψ  ≡  (φ → ψ) ∧ (ψ → φ)
  // At positive polarity: (¬φ ∨ ψ) ∧ (¬ψ ∨ φ)
  // At negative polarity: negate the whole thing → (φ ∧ ¬ψ) ∨ (ψ ∧ ¬φ)
  case NODE_EQUIV: {
    Node *phi_pos = to_nnf(a, n->lhs, true);
    Node *phi_neg = to_nnf(a, n->lhs, false);
    Node *psi_pos = to_nnf(a, n->rhs, true);
    Node *psi_neg = to_nnf(a, n->rhs, false);
    if (polarity) {
      // (¬φ ∨ ψ) ∧ (¬ψ ∨ φ)
      return node_and(a, node_or(a, phi_neg, psi_pos),
                      node_or(a, psi_neg, phi_pos));
    } else {
      // (φ ∧ ¬ψ) ∨ (ψ ∧ ¬φ)
      return node_or(a, node_and(a, phi_pos, psi_neg),
                     node_and(a, psi_pos, phi_neg));
    }
  }

  // -------------------------------------------------------------------------
  // Temporal: unary
  // X commutes with negation: ¬(Xφ) = X(¬φ)
  // ¬(Gφ) = F(¬φ),  ¬(Fφ) = G(¬φ)
  // -------------------------------------------------------------------------
  case NODE_X: {
    Node *arg = to_nnf(a, n->arg, polarity);
    return node_x(a, arg);
  }
  case NODE_X_STRONG: {
    // Strong next: ¬(X[!]φ) = X(¬φ) — strong next becomes weak under neg.
    // For simplicity we keep X_STRONG regardless of polarity here; a
    // separate pass can handle LTLf-specific rules.
    Node *arg = to_nnf(a, n->arg, polarity);
    return polarity ? node_x_strong(a, arg) : node_x(a, arg);
  }
  case NODE_G: {
    Node *arg = to_nnf(a, n->arg, polarity);
    return polarity ? node_g(a, arg) : node_f(a, arg);
  }
  case NODE_F: {
    Node *arg = to_nnf(a, n->arg, polarity);
    return polarity ? node_f(a, arg) : node_g(a, arg);
  }

  // -------------------------------------------------------------------------
  // Temporal: binary
  // ¬(φ U ψ) = (¬φ) R (¬ψ)
  // ¬(φ R ψ) = (¬φ) U (¬ψ)
  // ¬(φ W ψ) = (¬φ) M (¬ψ)
  // ¬(φ M ψ) = (¬φ) W (¬ψ)
  // -------------------------------------------------------------------------
  case NODE_U: {
    Node *l = to_nnf(a, n->lhs, polarity);
    Node *r = to_nnf(a, n->rhs, polarity);
    return polarity ? node_u(a, l, r) : node_r(a, l, r);
  }
  case NODE_R: {
    Node *l = to_nnf(a, n->lhs, polarity);
    Node *r = to_nnf(a, n->rhs, polarity);
    return polarity ? node_r(a, l, r) : node_u(a, l, r);
  }
  case NODE_W: {
    Node *l = to_nnf(a, n->lhs, polarity);
    Node *r = to_nnf(a, n->rhs, polarity);
    return polarity ? node_w(a, l, r) : node_m(a, l, r);
  }
  case NODE_M: {
    Node *l = to_nnf(a, n->lhs, polarity);
    Node *r = to_nnf(a, n->rhs, polarity);
    return polarity ? node_m(a, l, r) : node_w(a, l, r);
  }

  // -------------------------------------------------------------------------
  // High-level nodes should not reach NNF (assert away).
  // -------------------------------------------------------------------------
  case NODE_INT:
  case NODE_INT_NEG:
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD:
  case NODE_INT_VAR:
  case NODE_DEF_CALL:
  case NODE_BUS_INDEX:
  case NODE_PATTERN:
  case NODE_SET:
  case NODE_SET_ENUM:
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_KIND_COUNT:
    assert(false && "to_nnf: unexpected node kind (call expand() first)");
    return nullptr;
  }

  assert(false && "to_nnf: unhandled NodeKind");
  return nullptr;
}
