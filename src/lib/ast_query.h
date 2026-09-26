#ifndef TLSF_AST_QUERY_H
#define TLSF_AST_QUERY_H

/// ast_query.h — structural queries on expanded formulas, shared by the
/// recognisers, the template certifier and the liveness classifier.

#include "tlsf/apset.h"
#include "tlsf/ast.h"
#include "tlsf/cover.h"

#include <stdbool.h>
#include <stdint.h>

static inline bool ast_is_next(NodeKind k) {
  return k == NODE_X || k == NODE_X_STRONG;
}

/// True if `n` mentions any temporal operator (so it is not purely Boolean).
static inline bool ast_has_temporal(const Node *n) {
  if (!n)
    return false;
  if (node_kind_is_temporal(n->kind))
    return true;
  switch (n->kind) {
  case NODE_NOT:
    return ast_has_temporal(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return ast_has_temporal(n->lhs) || ast_has_temporal(n->rhs);
  default:
    return false;
  }
}

/// Strip a chain of X / X[!]: returns the operand, with the chain length in
/// `steps` and whether any link was strong in `strong`.
static inline const Node *ast_next_chain(const Node *n, uint32_t *steps,
                                         bool *strong) {
  *steps = 0;
  *strong = false;
  while (ast_is_next(n->kind)) {
    if (n->kind == NODE_X_STRONG)
      *strong = true;
    (*steps)++;
    n = n->arg;
  }
  return n;
}

/// True if `n` mentions an atom the cover marks as an output.
static inline bool cover_has_output_ref(const ConstraintCover *cov,
                                        const Node *n) {
  switch (n->kind) {
  case NODE_AP: {
    int32_t i = ap_table_find(&cov->aps, n->name);
    return i >= 0 && (ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT);
  }
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return cover_has_output_ref(cov, n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return cover_has_output_ref(cov, n->lhs) ||
           cover_has_output_ref(cov, n->rhs);
  default:
    return false;
  }
}

#endif // TLSF_AST_QUERY_H
