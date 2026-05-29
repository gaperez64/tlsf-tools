#include "tlsf/ast.h"

#include <assert.h>

// ---------------------------------------------------------------------------
// Internal helper
// ---------------------------------------------------------------------------

static Node *node_new(Arena *a, NodeKind k) {
  Node *n = ARENA_ALLOC(a, Node);
  if (n)
    n->kind = k;
  return n;
}

static Node *node_unary(Arena *a, NodeKind k, Node *arg) {
  assert(arg);
  Node *n = node_new(a, k);
  if (n)
    n->arg = arg;
  return n;
}

static Node *node_binary(Arena *a, NodeKind k, Node *lhs, Node *rhs) {
  assert(lhs && rhs);
  Node *n = node_new(a, k);
  if (n) {
    n->lhs = lhs;
    n->rhs = rhs;
  }
  return n;
}

// ---------------------------------------------------------------------------
// Atoms
// ---------------------------------------------------------------------------

Node *node_true(Arena *a) { return node_new(a, NODE_TRUE); }
Node *node_false(Arena *a) { return node_new(a, NODE_FALSE); }

Node *node_ap(Arena *a, const char *interned_name) {
  assert(interned_name);
  Node *n = node_new(a, NODE_AP);
  if (n)
    n->name = interned_name;
  return n;
}

Node *node_int(Arena *a, int64_t val) {
  Node *n = node_new(a, NODE_INT);
  if (n)
    n->ival = val;
  return n;
}

// ---------------------------------------------------------------------------
// Boolean connectives
// ---------------------------------------------------------------------------

Node *node_not(Arena *a, Node *arg) { return node_unary(a, NODE_NOT, arg); }
Node *node_and(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_AND, lhs, rhs);
}
Node *node_or(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_OR, lhs, rhs);
}
Node *node_impl(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_IMPL, lhs, rhs);
}
Node *node_equiv(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_EQUIV, lhs, rhs);
}

// ---------------------------------------------------------------------------
// Temporal operators
// ---------------------------------------------------------------------------

Node *node_x(Arena *a, Node *arg) { return node_unary(a, NODE_X, arg); }
Node *node_x_strong(Arena *a, Node *arg) {
  return node_unary(a, NODE_X_STRONG, arg);
}
Node *node_f(Arena *a, Node *arg) { return node_unary(a, NODE_F, arg); }
Node *node_g(Arena *a, Node *arg) { return node_unary(a, NODE_G, arg); }
Node *node_u(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_U, lhs, rhs);
}
Node *node_r(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_R, lhs, rhs);
}
Node *node_w(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_W, lhs, rhs);
}
Node *node_m(Arena *a, Node *lhs, Node *rhs) {
  return node_binary(a, NODE_M, lhs, rhs);
}
