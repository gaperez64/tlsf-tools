#include "normalize_internal.h"
#include "formula_equal.h"

#include <assert.h>

static void check(const Node *x, const Node *y, bool expected) {
  for (unsigned mode = 0; mode < 2; mode++) {
    assert(formula_equal(x, y, mode) == expected);
    assert(formula_equal(y, x, mode) == expected);
  }
}

static void totals(const TlsfNormStats *s) {
  uint64_t attempts = 0, time = 0;
  for (TlsfNormPass p = 0; p < TLSF_NORM_PASS_COUNT; p++) {
    const TlsfNormPassStats *r = &s->passes[p];
    assert(r->attempts ==
           r->fired + r->noops + r->rejected_growth + r->rejected_nodes);
    attempts += r->attempts;
    time += r->time_ns;
  }
  assert(s->iterations_total == attempts && s->time_ns == time);
}

static void equality(Arena *a) {
  Node *p = node_ap(a, "p"), *q = node_ap(a, "q");
  OriginBinding binding = {.binder_id = 7, .name = "i", .value = 3};
  Node copy = *p;
  copy.source_id = 42;
  copy.origin_bindings = &binding;
  copy.bounded = (BoundedTemporalMeta){.origin = BOUNDED_NEXT, .body = q};
  check(p, &copy, true);
  check(p, q, false);
  check(node_true(a), node_true(a), true);
  check(node_false(a), node_false(a), true);
  check(node_true(a), node_false(a), false);
  check(node_int(a, INT64_MIN), node_int(a, INT64_MIN), true);
  check(node_int(a, INT64_MIN), node_int(a, INT64_MAX), false);
  Node *(*unary[])(Arena *, Node *) = {node_not, node_x, node_x_strong, node_f,
                                       node_g};
  Node *(*binary[])(Arena *, Node *, Node *) = {
      node_and, node_or, node_impl, node_equiv, node_r, node_w, node_u, node_m};
  // The expanded fragment is the enum prefix, including integer literals.
  static_assert(4 + sizeof unary / sizeof *unary +
                    sizeof binary / sizeof *binary ==
                NODE_DEF_CALL);
  for (unsigned i = 0; i < sizeof unary / sizeof *unary; i++) {
    check(unary[i](a, p), unary[i](a, &copy), true);
    check(unary[i](a, p), unary[i](a, q), false);
  }
  for (unsigned i = 0; i < sizeof binary / sizeof *binary; i++) {
    check(binary[i](a, p, q), binary[i](a, &copy, q), true);
    check(binary[i](a, p, q), binary[i](a, q, q), false);
    check(binary[i](a, p, q), binary[i](a, p, p), false);
  }
  check(node_x(a, p), node_x_strong(a, p), false);
  copy.resolved_signal = true;
  Node *x = node_g(a, node_and(a, p, q));
  Node *y = node_g(a, node_and(a, &copy, q));
  assert(formula_equal(x, y, false) && !formula_equal(x, y, true));
  TlsfNormOptions opts;
  tlsf_norm_options_default(&opts, TLSF_NORM_PHASE_VISIBLE);
  TlsfNormPassSpec pass = {.pass = TLSF_NORM_PASS_NNF, .max_iter = 3};
  opts.schedule = (TlsfNormSchedule){.items = &pass, .count = 1};
  TlsfNormStats stats;
  tlsf_norm_stats_init(&stats, opts.phase, "nnf:3");
  assert(tlsf_normalize_formula(a, y, &opts, &stats));
  assert(stats.formulas_changed == 1 && stats.passes[pass.pass].attempts == 2 &&
         stats.passes[pass.pass].fired == 1 &&
         stats.passes[pass.pass].noops == 1);
  assert(copy.source_id == 42 && copy.origin_bindings == &binding);
}

int main(void) {
  Arena *a = arena_new(ARENA_DEFAULT_SLAB_SIZE);
  assert(a);
  equality(a);
  Node *p = node_ap(a, "p"), *q = node_ap(a, "q"), *r = node_ap(a, "r");
  Node *root = node_g(a, node_and(a, p, q));
  TlsfNormPassSpec pass = {.pass = TLSF_NORM_PASS_ROUTE_SAFE, .max_iter = 3};
  TlsfNormOptions opts;
  tlsf_norm_options_default(&opts, TLSF_NORM_PHASE_VISIBLE);
  opts.schedule = (TlsfNormSchedule){.items = &pass, .count = 1};
  TlsfNormStats s;
  tlsf_norm_stats_init(&s, opts.phase, "route-safe:3");
  Node *result = tlsf_normalize_formula(a, root, &opts, &s);
  assert(result && result->kind == NODE_AND);
  assert(s.formulas_seen == 1 && s.formulas_changed == 1);
  assert(s.passes[pass.pass].attempts == 2 && s.passes[pass.pass].fired == 1 &&
         s.passes[pass.pass].noops == 1);
  totals(&s);

  for (unsigned growth = 0; growth < 2; growth++) {
    tlsf_norm_stats_init(&s, opts.phase, "route-safe:3");
    opts.max_nodes = growth ? 0 : 1;
    opts.max_growth_percent = growth ? 1 : 0;
    assert(tlsf_normalize_formula(a, root, &opts, &s) == root);
    assert(s.formulas_seen == 1 && s.formulas_changed == 0 &&
           s.formulas_rejected == 1);
    assert(s.nodes_before == 4 && s.nodes_after == 4);
    const TlsfNormPassStats *rs = &s.passes[pass.pass];
    assert(rs->attempts == 1 && rs->fired == 0 && rs->noops == 0);
    assert(rs->nodes_before_sum == 4 && rs->nodes_after_sum == 5);
    assert(growth ? rs->rejected_growth == 1 : rs->rejected_nodes == 1);
    totals(&s);
  }

  root = node_g(a, node_and(a, p, node_and(a, q, r)));
  for (unsigned pre = 0; pre < 2; pre++) {
    tlsf_norm_stats_init(&s, TLSF_NORM_PHASE_PRE_EXPAND, "split");
    Node **parts;
    assert(tlsf_normalize_split(a, root, &parts, pre != 0, &s) == 3);
    assert(tlsf_normalize_split(a, p, &parts, pre != 0, &s) == 1);
    TlsfNormPass split =
        pre ? TLSF_NORM_PASS_PRE_SPINE_SPLIT : TLSF_NORM_PASS_SPLIT;
    assert(s.formulas_seen == 2 && s.formulas_changed == 1);
    assert(s.nodes_before == 7 && s.nodes_after == 7);
    assert(s.passes[split].attempts == 2 && s.passes[split].fired == 1 &&
           s.passes[split].noops == 1);
    totals(&s);
  }
  arena_free(a);
  return 0;
}
