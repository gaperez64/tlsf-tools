#include "tlsf/normalize.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

static unsigned checks;

static Node *indexed(Arena *a, bool strong, int64_t count, Node *body) {
  Node *n = node_next_n(a, node_int(a, count), body);
  assert(n);
  n->bounded.strong = strong;
  return n;
}

static Node *unary(Arena *a, bool strong, Node *body) {
  return strong ? node_x_strong(a, body) : node_x(a, body);
}

// Compare the active fields independently, including strength on indexed nodes.
static void equal(const Node *actual, const Node *expected) {
  assert(actual && expected && actual->kind == expected->kind);
  if (actual == expected)
    return;
  switch (actual->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return;
  case NODE_INT:
    assert(actual->ival == expected->ival);
    return;
  case NODE_AP:
    assert(actual->name == expected->name);
    return;
  case NODE_NEXT_N:
    assert(actual->bounded.strong == expected->bounded.strong);
    equal(actual->lhs, expected->lhs);
    equal(actual->rhs, expected->rhs);
    return;
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_NOT:
  case NODE_F:
  case NODE_G:
    equal(actual->arg, expected->arg);
    return;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    equal(actual->lhs, expected->lhs);
    equal(actual->rhs, expected->rhs);
    return;
  default:
    assert(false);
  }
}

static void check(Arena *a, bool finite, Node *input, Node *expected) {
  TlsfNormOptions opts;
  tlsf_norm_options_default(&opts, TLSF_NORM_PHASE_PRE_EXPAND);
  TlsfNormPassSpec step = {.pass = TLSF_NORM_PASS_PRE_INDEXED_X, .max_iter = 1};
  opts.schedule = (TlsfNormSchedule){.items = &step, .count = 1};
  opts.finite_word = finite;
  equal(tlsf_normalize_formula(a, input, &opts, nullptr), expected);
  checks++;
}

int main(void) {
  Arena *a = arena_new(ARENA_DEFAULT_SLAB_SIZE);
  assert(a);
  Node *p = node_true(a), *k = node_ap(a, "k");
  for (unsigned finite = 0; finite < 2; finite++) {
    for (unsigned s = 0; s < 2; s++) {
      // NextStrength.branch_witnesses: zero, homogeneous counts, the last
      // representable sum, rejected overflow, and reconstruction of both
      // strengths.
      check(a, finite, indexed(a, s, 0, p), p);
      check(a, finite, indexed(a, s, 1, indexed(a, s, 2, p)),
            indexed(a, s, 3, p));
      check(a, finite, indexed(a, s, INT64_MAX - 1, indexed(a, s, 1, p)),
            indexed(a, s, INT64_MAX, p));
      Node *overflow = indexed(a, s, INT64_MAX, indexed(a, s, 1, p));
      check(a, finite, overflow, overflow);
      Node *changed = node_not(a, indexed(a, false, 0, p));
      Node *symbolic = node_next_n(a, k, changed);
      symbolic->bounded.strong = s;
      Node *expected = node_next_n(a, k, node_not(a, p));
      expected->bounded.strong = s;
      check(a, finite, symbolic, expected);
      check(a, finite, indexed(a, s, 1, changed),
            indexed(a, s, 1, node_not(a, p)));
      check(a, finite, node_x_strong(a, node_not(a, indexed(a, s, 0, p))),
            node_x_strong(a, node_not(a, p)));

      // Both zero strengths disappear before the outer branch examines its
      // child.
      for (unsigned t = 0; t < 2; t++) {
        check(a, finite, indexed(a, s, 0, indexed(a, t, 2, p)),
              indexed(a, t, 2, p));
        check(a, finite, indexed(a, s, 2, indexed(a, t, 0, p)),
              indexed(a, s, 2, p));
        check(a, finite, indexed(a, s, 1, indexed(a, t, 2, p)),
              s == t ? indexed(a, s, 3, p)
                     : indexed(a, s, 1, indexed(a, t, 2, p)));
        check(a, finite, indexed(a, s, 1, unary(a, t, p)),
              !s && !t ? indexed(a, false, 2, p)
                       : indexed(a, s, 1, unary(a, t, p)));
        check(a, finite, unary(a, s, indexed(a, t, 1, p)),
              !s && !t ? indexed(a, false, 2, p)
                       : unary(a, s, indexed(a, t, 1, p)));
      }
      check(a, finite, indexed(a, s, 1, indexed(a, s, 2, indexed(a, s, 3, p))),
            indexed(a, s, 6, p));
      check(a, finite, indexed(a, s, 1, indexed(a, s, INT64_MAX - 1, p)),
            indexed(a, s, INT64_MAX, p));
      overflow = indexed(a, s, 1, indexed(a, s, INT64_MAX, p));
      check(a, finite, overflow, overflow);
      // A changed child still cannot admit an overflowing sum.
      check(a, finite, indexed(a, s, INT64_MAX, indexed(a, s, 1, changed)),
            indexed(a, s, INT64_MAX, indexed(a, s, 1, node_not(a, p))));
      check(a, finite, indexed(a, s, -1, changed),
            indexed(a, s, -1, node_not(a, p)));
      check(a, finite, indexed(a, s, 1, indexed(a, s, -1, p)),
            indexed(a, s, 1, indexed(a, s, -1, p)));
      check(a, finite, unary(a, s, changed), unary(a, s, node_not(a, p)));
    }
    check(a, finite, indexed(a, false, INT64_MAX - 1, node_x(a, p)),
          indexed(a, false, INT64_MAX, p));
    check(a, finite, node_x(a, indexed(a, false, INT64_MAX - 1, p)),
          indexed(a, false, INT64_MAX, p));
    Node *overflow = indexed(a, false, INT64_MAX, node_x(a, p));
    check(a, finite, overflow, overflow);
    overflow = node_x(a, indexed(a, false, INT64_MAX, p));
    check(a, finite, overflow, overflow);
    check(a, finite, indexed(a, false, -1, node_x(a, p)),
          indexed(a, false, -1, node_x(a, p)));
    check(a, finite, node_x(a, indexed(a, false, -1, p)),
          node_x(a, indexed(a, false, -1, p)));

    // Recursion/reconstruction through every supported context, and C's
    // frontier.
    Node *changed = indexed(a, true, 0, p);
    check(a, finite, node_not(a, changed), node_not(a, p));
    check(a, finite, node_g(a, changed), node_g(a, p));
    check(a, finite, node_f(a, changed), node_f(a, p));
    check(a, finite, node_and(a, changed, changed), node_and(a, p, p));
    check(a, finite, node_or(a, changed, changed), node_or(a, p, p));
    check(a, finite, node_impl(a, changed, changed), node_impl(a, p, p));
    check(a, finite, node_equiv(a, changed, changed), node_equiv(a, p, p));
    Node *untouched[] = {node_u(a, changed, p), node_r(a, changed, p),
                         node_w(a, changed, p), node_m(a, changed, p)};
    for (unsigned i = 0; i < sizeof untouched / sizeof *untouched; i++)
      check(a, finite, untouched[i], untouched[i]);
  }
  assert(!arena_failed(a));
  arena_free(a);
  printf("next strength correspondence: %u checks passed\n", checks);
  return 0;
}
