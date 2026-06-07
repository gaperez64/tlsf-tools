#include "tlsf/rewrite.h"

#include "tlsf/nnf.h"

#include <assert.h>

// Cap on fixpoint iterations.  Reaching it is only possible if mutually
// inverse passes (e.g. push-in and pull-out of the same operator) are both
// requested; the cap guarantees termination in that ill-posed case.
#define RW_FIXPOINT_CAP 200

static bool is_true(const Node *n) { return n->kind == NODE_TRUE; }
static bool is_false(const Node *n) { return n->kind == NODE_FALSE; }

// Structural equality (atoms are interned, so names compare by pointer).
static bool node_equal(const Node *x, const Node *y) {
  if (x == y)
    return true;
  if (x->kind != y->kind)
    return false;
  switch (x->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_AP:
    return x->name == y->name;
  case NODE_INT:
    return x->ival == y->ival;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return node_equal(x->arg, y->arg);
  default: // binary connectives / temporal
    return node_equal(x->lhs, y->lhs) && node_equal(x->rhs, y->rhs);
  }
}

// ---------------------------------------------------------------------------
// Weak simplification (syfco -s0): constant folding and redundancy removal.
// Children are already simplified (this is applied bottom-up).  Every rule is
// equivalence-preserving.
// ---------------------------------------------------------------------------

static Node *simplify_weak_local(Arena *a, Node *n) {
  switch (n->kind) {
  case NODE_NOT:
    if (is_true(n->arg))
      return node_false(a);
    if (is_false(n->arg))
      return node_true(a);
    if (n->arg->kind == NODE_NOT)
      return n->arg->arg; // !!x = x
    return n;

  case NODE_AND:
    if (is_false(n->lhs) || is_false(n->rhs))
      return node_false(a);
    if (is_true(n->lhs))
      return n->rhs;
    if (is_true(n->rhs))
      return n->lhs;
    if (node_equal(n->lhs, n->rhs))
      return n->lhs;
    return n;

  case NODE_OR:
    if (is_true(n->lhs) || is_true(n->rhs))
      return node_true(a);
    if (is_false(n->lhs))
      return n->rhs;
    if (is_false(n->rhs))
      return n->lhs;
    if (node_equal(n->lhs, n->rhs))
      return n->lhs;
    return n;

  case NODE_IMPL:
    if (is_false(n->lhs) || is_true(n->rhs))
      return node_true(a);
    if (is_true(n->lhs))
      return n->rhs;
    if (is_false(n->rhs))
      return node_not(a, n->lhs);
    return n;

  case NODE_EQUIV:
    if (is_true(n->lhs))
      return n->rhs;
    if (is_true(n->rhs))
      return n->lhs;
    if (is_false(n->lhs))
      return node_not(a, n->rhs);
    if (is_false(n->rhs))
      return node_not(a, n->lhs);
    if (node_equal(n->lhs, n->rhs))
      return node_true(a);
    return n;

  case NODE_X:
    if (is_true(n->arg))
      return node_true(a);
    if (is_false(n->arg))
      return node_false(a);
    return n;

  case NODE_X_STRONG:
    // X[!] false = false; X[!] true is NOT true on finite words (the last
    // position has no successor), so it is left as is.
    if (is_false(n->arg))
      return node_false(a);
    return n;

  case NODE_F:
    if (is_true(n->arg))
      return node_true(a);
    if (is_false(n->arg))
      return node_false(a);
    if (n->arg->kind == NODE_F)
      return n->arg; // F F x = F x
    return n;

  case NODE_G:
    if (is_true(n->arg))
      return node_true(a);
    if (is_false(n->arg))
      return node_false(a);
    if (n->arg->kind == NODE_G)
      return n->arg; // G G x = G x
    return n;

  case NODE_U: // a U b
    if (is_true(n->rhs))
      return node_true(a);
    if (is_false(n->rhs))
      return node_false(a);
    if (is_false(n->lhs))
      return n->rhs; // false U b = b
    if (is_true(n->lhs))
      return node_f(a, n->rhs); // true U b = F b
    return n;

  case NODE_R: // a R b
    if (is_false(n->rhs))
      return node_false(a);
    if (is_true(n->rhs))
      return node_true(a);
    if (is_false(n->lhs))
      return node_g(a, n->rhs); // false R b = G b
    if (is_true(n->lhs))
      return n->rhs; // true R b = b
    return n;

  case NODE_W: // a W b
    if (is_true(n->lhs))
      return node_true(a); // true W b = true
    if (is_true(n->rhs))
      return node_true(a);
    if (is_false(n->lhs))
      return n->rhs; // false W b = b
    if (is_false(n->rhs))
      return node_g(a, n->lhs); // a W false = G a
    return n;

  case NODE_M: // a M b (strong release)
    if (is_false(n->rhs))
      return node_false(a); // a M false = false
    if (is_false(n->lhs))
      return node_false(a); // false M b = false
    if (is_true(n->rhs))
      return node_f(a, n->lhs); // a M true = F a
    if (is_true(n->lhs))
      return n->rhs; // true M b = b
    return n;

  default:
    return n;
  }
}

// ---------------------------------------------------------------------------
// Per-node rule application.  Children are already rewritten.  At most one
// structural rule fires per call; the driver re-traverses to a fixpoint so
// rules that expose further opportunities (e.g. R->W then W->U||G) compose.
// ---------------------------------------------------------------------------

static Node *apply_local(Arena *a, Node *n, unsigned flags) {
  // Operator replacement.
  if ((flags & RW_NO_WEAK_UNTIL) && n->kind == NODE_W)
    return node_or(a, node_u(a, n->lhs, n->rhs), node_g(a, n->lhs));
  if ((flags & RW_NO_RELEASE) && n->kind == NODE_R)
    return node_w(a, n->rhs, node_and(a, n->lhs, n->rhs));
  if ((flags & RW_NO_STRONG_RELEASE) && n->kind == NODE_M)
    return node_u(a, n->rhs, node_and(a, n->lhs, n->rhs));
  if ((flags & RW_NO_FINALLY) && n->kind == NODE_F)
    return node_u(a, node_true(a), n->arg);
  if ((flags & RW_NO_GLOBALLY) && n->kind == NODE_G)
    return node_r(a, node_false(a), n->arg);

  // Push inwards.
  if ((flags & RW_PUSH_G_IN) && n->kind == NODE_G && n->arg->kind == NODE_AND)
    return node_and(a, node_g(a, n->arg->lhs), node_g(a, n->arg->rhs));
  if ((flags & RW_PUSH_F_IN) && n->kind == NODE_F && n->arg->kind == NODE_OR)
    return node_or(a, node_f(a, n->arg->lhs), node_f(a, n->arg->rhs));
  if ((flags & RW_PUSH_X_IN) && n->kind == NODE_X &&
      (n->arg->kind == NODE_AND || n->arg->kind == NODE_OR)) {
    Node *c = n->arg;
    Node *l = node_x(a, c->lhs);
    Node *r = node_x(a, c->rhs);
    return c->kind == NODE_AND ? node_and(a, l, r) : node_or(a, l, r);
  }

  // Pull outwards.
  if ((flags & RW_PULL_G_OUT) && n->kind == NODE_AND &&
      n->lhs->kind == NODE_G && n->rhs->kind == NODE_G)
    return node_g(a, node_and(a, n->lhs->arg, n->rhs->arg));
  if ((flags & RW_PULL_F_OUT) && n->kind == NODE_OR && n->lhs->kind == NODE_F &&
      n->rhs->kind == NODE_F)
    return node_f(a, node_or(a, n->lhs->arg, n->rhs->arg));
  if ((flags & RW_PULL_X_OUT) && (n->kind == NODE_AND || n->kind == NODE_OR) &&
      n->lhs->kind == NODE_X && n->rhs->kind == NODE_X) {
    Node *inner = n->kind == NODE_AND ? node_and(a, n->lhs->arg, n->rhs->arg)
                                      : node_or(a, n->lhs->arg, n->rhs->arg);
    return node_x(a, inner);
  }

  // Weak simplification (constant folding) last, so constants introduced by
  // the replacement rules (true U a, false R a) get folded on the next pass.
  if (flags & RW_SIMPLIFY_WEAK)
    return simplify_weak_local(a, n);

  return n;
}

// Bottom-up single traversal: rewrite children, then apply the local rule.
static Node *rw_pass(Arena *a, Node *n, unsigned flags) {
  Node *t;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
  case NODE_INT:
    return n;
  case NODE_NOT:
    t = node_not(a, rw_pass(a, n->arg, flags));
    break;
  case NODE_X:
    t = node_x(a, rw_pass(a, n->arg, flags));
    break;
  case NODE_X_STRONG:
    t = node_x_strong(a, rw_pass(a, n->arg, flags));
    break;
  case NODE_F:
    t = node_f(a, rw_pass(a, n->arg, flags));
    break;
  case NODE_G:
    t = node_g(a, rw_pass(a, n->arg, flags));
    break;
  case NODE_AND:
    t = node_and(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  case NODE_OR:
    t = node_or(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  case NODE_IMPL:
    t = node_impl(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  case NODE_EQUIV:
    t = node_equiv(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  case NODE_U:
    t = node_u(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  case NODE_R:
    t = node_r(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  case NODE_W:
    t = node_w(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  case NODE_M:
    t = node_m(a, rw_pass(a, n->lhs, flags), rw_pass(a, n->rhs, flags));
    break;
  default:
    assert(false && "rewrite: unexpected high-level node");
    return n;
  }
  node_copy_bounded(t, n);
  return apply_local(a, t, flags);
}

Node *apply_rewrites(Arena *a, Node *root, unsigned flags) {
  if (flags == RW_NONE)
    return root;

  // NNF first (matches syfco -s1 ordering and eliminates ->/<->).
  if (flags & RW_NNF) {
    root = to_nnf(a, root, true);
    if (!root)
      return nullptr;
  }

  unsigned local = flags & ~(unsigned)RW_NNF;
  if (local == 0)
    return root;

  for (int it = 0; it < RW_FIXPOINT_CAP; it++) {
    Node *next = rw_pass(a, root, local);
    bool stable = node_equal(next, root);
    root = next;
    if (stable)
      break;
  }
  return root;
}

static void decomp_push(Arena *a, Node ***out, uint32_t *cap, uint32_t *cnt,
                        Node *n) {
  if (*cnt == *cap) {
    uint32_t nc = *cap ? *cap * 2 : 8;
    Node **arr = ARENA_ALLOC_N(a, Node *, nc);
    for (uint32_t i = 0; i < *cnt; i++)
      arr[i] = (*out)[i];
    *out = arr;
    *cap = nc;
  }
  (*out)[(*cnt)++] = n;
}

// Surgical, equivalence-preserving decomposition: split at top-level `&&`, and
// distribute `G`/`X` over `&&` *only along the spine* — `G(a&&b)`→`Ga,Gb`,
// `X(a&&b)`→`Xa,Xb` — never descending into F/U/R/W/M (so e.g. `F G(a&&b)` is
// left intact rather than reshaped to `F(Ga&&Gb)`).
static void decomp_append(Arena *a, Node *f, Node ***out, uint32_t *cap,
                          uint32_t *cnt) {
  if (f->kind == NODE_AND) {
    decomp_append(a, f->lhs, out, cap, cnt);
    decomp_append(a, f->rhs, out, cap, cnt);
    return;
  }
  if (f->kind == NODE_G || f->kind == NODE_X || f->kind == NODE_X_STRONG) {
    Node **sub = nullptr;
    uint32_t scap = 0, scnt = 0;
    decomp_append(a, f->arg, &sub, &scap, &scnt);
    for (uint32_t i = 0; i < scnt; i++) {
      Node *w = f->kind == NODE_G   ? node_g(a, sub[i])
                : f->kind == NODE_X ? node_x(a, sub[i])
                                    : node_x_strong(a, sub[i]);
      decomp_push(a, out, cap, cnt, w);
    }
    return;
  }
  decomp_push(a, out, cap, cnt, f);
}

uint32_t rewrite_decompose(Arena *a, Node *f, Node ***out) {
  Node **arr = nullptr;
  uint32_t cap = 0, cnt = 0;
  decomp_append(a, f, &arr, &cap, &cnt);
  *out = arr;
  return cnt;
}
