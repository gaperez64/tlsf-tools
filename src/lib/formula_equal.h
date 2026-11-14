#ifndef TLSF_FORMULA_EQUAL_H
#define TLSF_FORMULA_EQUAL_H

#include "tlsf/ast.h"

// Invariant: AP names share an intern table; kind selects the active payload.
// Rewrite compares expanded syntax; normalization also preserves resolution
// state because it runs before expansion (and NNF can reset that state).
// Source IDs, origin bindings and expanded bounded caches are not syntax.
// Indexed next is supported for normalization; other high-level nodes remain
// pointer-only. Full high-level set equality stays in expand.c.
static inline bool formula_equal(const Node *x, const Node *y,
                                 bool preserve_resolution) {
  if (x == y)
    return true;
  if (!x || !y || x->kind != y->kind)
    return false;
  switch (x->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_AP:
    return x->name == y->name &&
           (!preserve_resolution || x->resolved_signal == y->resolved_signal);
  case NODE_INT:
    return x->ival == y->ival;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return formula_equal(x->arg, y->arg, preserve_resolution);
  case NODE_NEXT_N:
    if (x->bounded.strong != y->bounded.strong)
      return false;
    [[fallthrough]];
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_R:
  case NODE_W:
  case NODE_U:
  case NODE_M:
    return formula_equal(x->lhs, y->lhs, preserve_resolution) &&
           formula_equal(x->rhs, y->rhs, preserve_resolution);
  default:
    return false; // Never read an unhandled kind's inactive union arm.
  }
}

#endif
