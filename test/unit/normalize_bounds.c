#include "tlsf/normalize.h"

#include <assert.h>
#include <stdint.h>

static Node *normalize(Arena *a, Node *n, TlsfNormPass pass, bool finite) {
  TlsfNormOptions opts;
  tlsf_norm_options_default(&opts, TLSF_NORM_PHASE_PRE_EXPAND);
  TlsfNormPassSpec step = {.pass = pass, .max_iter = 1};
  opts.schedule = (TlsfNormSchedule){.items = &step, .count = 1};
  opts.finite_word = finite;
  return tlsf_normalize_formula(a, n, &opts, nullptr);
}

int main(void) {
  Arena *a = arena_new(ARENA_DEFAULT_SLAB_SIZE);
  assert(a);
  const int64_t extremes[] = {INT64_MIN, INT64_MAX};
  for (unsigned finite = 0; finite < 2; finite++) {
    for (unsigned bound = 0; bound < 2; bound++)
      for (unsigned flags = 0; flags < 4; flags++)
        for (unsigned all = 0; all < 2; all++) {
          Node *n = ARENA_ALLOC(a, Node);
          assert(n);
          n->kind = all ? NODE_FORALL : NODE_EXISTS;
          n->qlo = node_int(a, extremes[bound]);
          n->qhi = node_int(a, extremes[bound]);
          n->qlo_strict = flags & 1;
          n->qhi_strict = flags & 2;
          n->qbody = all ? node_false(a) : node_true(a);
          Node *result =
              normalize(a, n, TLSF_NORM_PASS_PRE_BOUNDED_BOOL, finite != 0);
          assert(flags ? result->kind == (all ? NODE_TRUE : NODE_FALSE)
                       : result == n);
        }

    Node *body = node_true(a);
    Node *max_next = node_next_n(a, node_int(a, INT64_MAX), body);
    Node *cases[] = {
        node_next_n(a, node_int(a, INT64_MAX), node_x(a, body)),
        node_x(a, max_next),
        node_next_n(a, node_int(a, 1), max_next),
        node_next_n(a, node_int(a, INT64_MAX), max_next),
    };
    for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++)
      assert(normalize(a, cases[i], TLSF_NORM_PASS_PRE_INDEXED_X,
                       finite != 0) == cases[i]);
    Node *safe = node_next_n(a, node_int(a, INT64_MAX - 1), node_x(a, body));
    Node *result =
        normalize(a, safe, TLSF_NORM_PASS_PRE_INDEXED_X, finite != 0);
    assert(result->kind == NODE_NEXT_N && result->lhs->ival == INT64_MAX &&
           result->rhs == body);
  }
  arena_free(a);
  return 0;
}
