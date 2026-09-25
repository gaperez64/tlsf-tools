#define _POSIX_C_SOURCE 200809L
#include "oxidd_common.h"
#include "tlsf/safety_oxidd.h"
#include "tlsf/gr1_oxidd.h"
#include <stdlib.h>
#include <unistd.h>

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);                  \
      abort();                                                                 \
    }                                                                          \
  } while (0)

static unsigned fail_and, and_calls;
static const char *fail_operation;
static unsigned failures;
static bool fail_calloc, fail_realloc;
static unsigned fail_realloc_at, realloc_calls;
void *__real_calloc(size_t n, size_t size);
void *__wrap_calloc(size_t n, size_t size);
void *__wrap_calloc(size_t n, size_t size) {
  if (fail_calloc) {
    fail_calloc = false;
    return NULL;
  }
  return __real_calloc(n, size);
}
void *__real_oxidd_host_realloc(void *p, size_t size);
void *__wrap_oxidd_host_realloc(void *p, size_t size);
void *__wrap_oxidd_host_realloc(void *p, size_t size) {
  realloc_calls++;
  if (fail_realloc || (fail_realloc_at && realloc_calls == fail_realloc_at)) {
    fail_realloc = false;
    return NULL;
  }
  return __real_oxidd_host_realloc(p, size);
}
static bool injected(const char *name) {
  if (failures && fail_operation && !strcmp(fail_operation, name)) {
    failures--;
    return true;
  }
  return false;
}
#define WRAP_BINARY(name)                                                      \
  Bdd __real_oxidd_bdd_##name(Bdd a, Bdd b);                                   \
  Bdd __wrap_oxidd_bdd_##name(Bdd a, Bdd b);                                   \
  Bdd __wrap_oxidd_bdd_##name(Bdd a, Bdd b) {                                  \
    return injected(#name) ? (Bdd){0} : __real_oxidd_bdd_##name(a, b);         \
  }
WRAP_BINARY(forall)
WRAP_BINARY(exists)
WRAP_BINARY(restrict)
Bdd __real_oxidd_bdd_substitute(Bdd a, const oxidd_bdd_substitution_t *s);
Bdd __wrap_oxidd_bdd_substitute(Bdd a, const oxidd_bdd_substitution_t *s);
Bdd __wrap_oxidd_bdd_substitute(Bdd a, const oxidd_bdd_substitution_t *s) {
  return injected("substitute") ? (Bdd){0} : __real_oxidd_bdd_substitute(a, s);
}
Bdd __real_oxidd_bdd_apply_exists(oxidd_boolean_operator op, Bdd a, Bdd b,
                                  Bdd v);
Bdd __wrap_oxidd_bdd_apply_exists(oxidd_boolean_operator op, Bdd a, Bdd b,
                                  Bdd v);
Bdd __wrap_oxidd_bdd_apply_exists(oxidd_boolean_operator op, Bdd a, Bdd b,
                                  Bdd v) {
  return injected("apply_exists") ? (Bdd){0}
                                  : __real_oxidd_bdd_apply_exists(op, a, b, v);
}
Bdd __real_oxidd_bdd_and(Bdd a, Bdd b);
Bdd __wrap_oxidd_bdd_and(Bdd a, Bdd b);
Bdd __wrap_oxidd_bdd_and(Bdd a, Bdd b) {
  and_calls++;
  if (fail_and) {
    fail_and--;
    return (Bdd){0};
  }
  return __real_oxidd_bdd_and(a, b);
}

static Aig *read_game(const char *text) {
  FILE *f = tmpfile();
  CHECK(f);
  fputs(text, f);
  rewind(f);
  Aig *g = aig_read_aag(f);
  fclose(f);
  CHECK(g);
  return g;
}

static void check_order(const OxiddResolvedOrder *order,
                        const uint32_t *expected, size_t count) {
  CHECK(order->count == count);
  bool matches = true;
  for (size_t i = 0; i < count; i++)
    matches = matches && order->local[i] == expected[i];
  if (!matches) {
    fputs("actual order:", stderr);
    for (size_t i = 0; i < count; i++)
      fprintf(stderr, " %u", order->local[i]);
    fputs("\nexpected order:", stderr);
    for (size_t i = 0; i < count; i++)
      fprintf(stderr, " %u", expected[i]);
    fputc('\n', stderr);
  }
  for (size_t i = 0; i < count; i++) {
    CHECK(order->local[i] == expected[i]);
  }
}

static void variable_orders(void) {
  Aig *game = aig_new();
  uint32_t i0 = aig_input(game, "env"), i1 = aig_input(game, "controllable_c");
  uint32_t s0 = aig_latch(game, 0, 0), s1 = aig_latch(game, 0, 1);
  uint32_t g0 = aig_and(game, i0, s0), g1 = aig_and(game, i1, s1);
  CHECK(aig_set_latch_next(game, s0, g0));
  CHECK(aig_set_latch_next(game, s1, g1));
  aig_set_output(game, "bad", g0);

  OxiddSolveOptions opts = oxidd_solve_options_default();
  uint32_t output_lit = UINT32_MAX, next0 = UINT32_MAX, next1 = UINT32_MAX;
  aig_output_at(game, 0, &output_lit);
  aig_latch_at(game, 0, nullptr, &next0, nullptr);
  aig_latch_at(game, 1, nullptr, &next1, nullptr);
  CHECK(output_lit == g0 && next0 == g0 && next1 == g1);
  OxiddResolvedOrder order = {0};
  const uint32_t input_first[] = {0, 1, 2, 3, 4, 5};
  const uint32_t state_first[] = {2, 3, 0, 1, 4, 5};
  const uint32_t fanin_dfs[] = {0, 2, 1, 3, 4, 5};
  CHECK(oxidd_resolve_var_order(game, &opts, 2, &order));
  check_order(&order, input_first, 6);
  oxidd_resolved_order_free(&order);
  opts.var_order = OXIDD_VAR_ORDER_STATE_FIRST;
  CHECK(oxidd_resolve_var_order(game, &opts, 2, &order));
  check_order(&order, state_first, 6);
  oxidd_resolved_order_free(&order);
  opts.var_order = OXIDD_VAR_ORDER_FANIN_DFS;
  CHECK(oxidd_resolve_var_order(game, &opts, 2, &order));
  check_order(&order, fanin_dfs, 6);
  oxidd_bdd_manager_t manager = oxidd_bdd_manager_new(4096, 256, 1);
  oxidd_bdd_manager_add_vars(manager, 6);
  CHECK(oxidd_apply_var_order(manager, 0, &opts, &order));
  for (oxidd_level_no_t level = 0; level < 6; level++)
    CHECK(oxidd_bdd_manager_level_to_var(manager, level) == fanin_dfs[level]);
  oxidd_bdd_manager_unref(manager);
  oxidd_resolved_order_free(&order);

  char path[] = "/tmp/tlsfsolve-order-XXXXXX";
  int fd = mkstemp(path);
  CHECK(fd >= 0);
  FILE *file = fdopen(fd, "w");
  CHECK(file);
  fputs("tlsfsolve-order-v1 6\n2\n0\n3\n1\n5\n4\n", file);
  CHECK(fclose(file) == 0);
  opts = oxidd_solve_options_default();
  opts.order_file = path;
  const uint32_t custom[] = {2, 0, 3, 1, 5, 4};
  CHECK(oxidd_resolve_var_order(game, &opts, 2, &order));
  check_order(&order, custom, 6);
  CHECK(order.file_hash != 0 && order.hash != 0);
  oxidd_resolved_order_free(&order);
  file = fopen(path, "w");
  CHECK(file);
  fputs("tlsfsolve-order-v1 6\n2\n0\n3\n1\n5\n5\n", file);
  CHECK(fclose(file) == 0);
  OxiddFailure failure = {0};
  opts.failure = &failure;
  CHECK(!oxidd_resolve_var_order(game, &opts, 2, &order));
  CHECK(failure.kind == OXIDD_FAILURE_CONFIGURATION &&
        !strcmp(failure.operation, "order_file_invalid"));
  CHECK(unlink(path) == 0);

  Aig *constant = aig_new();
  aig_set_output(constant, "bad", 0);
  opts = oxidd_solve_options_default();
  opts.var_order = OXIDD_VAR_ORDER_FANIN_DFS;
  CHECK(oxidd_resolve_var_order(constant, &opts, 0, &order));
  CHECK(order.count == 0);
  oxidd_resolved_order_free(&order);
  aig_free(constant);
  aig_free(game);
}

static void roots_and_retry(void) {
  // Non-dense IDs; duplicate operands, complements, a disconnected gate,
  // roots which are later operands, a latch leaf and duplicate root uses.
  Aig *g = read_game("aag 12 2 1 1 5\n2\n4\n8 2\n24\n"
                     "12 2 2\n16 12 5\n18 16 8\n20 2 4\n24 18 13\n");
  oxidd_bdd_manager_t m = oxidd_bdd_manager_new(4096, 256, 1);
  oxidd_bdd_manager_add_vars(m, 10);
  OxiddSolveOptions opts = oxidd_solve_options_default();
  OxiddRun r;
  oxidd_run_init(&r, m, &opts, 4096, 256);
  uint32_t lits[] = {12, 16, 19, 24, 12, 8, 0, 1};
  Bdd roots[8] = {0}, map[13] = {0}, eager[13] = {0};
  const uint32_t leaf[] = {1, 2, 4};
  for (unsigned i = 0; i < 3; i++)
    map[leaf[i]] = eager[leaf[i]] = oxidd_bdd_var(m, i + 7);
  for (unsigned i = 0; i < 3; i++)
    oxidd_bdd_ref(eager[leaf[i]]);
  // Both host allocations happen before map consumption or root publication.
  // Inject each one and prove the caller's sentinel outputs stay untouched.
  for (unsigned failure = 1; failure <= 2; failure++) {
    Bdd sentinel = oxidd_bdd_true(m);
    for (unsigned i = 0; i < 8; i++)
      roots[i] = sentinel;
    realloc_calls = 0;
    fail_realloc_at = failure;
    CHECK(!oxidd_build_roots(&r, g, map, 12, lits, roots, 8));
    CHECK(realloc_calls == failure);
    for (unsigned i = 0; i < 8; i++)
      CHECK(bdd_same_identity(roots[i], sentinel));
    oxidd_bdd_unref(sentinel);
    fail_realloc_at = 0;
  }
  for (uint32_t i = 0; i < aig_num_ands(g); i++) {
    uint32_t lhs, a, b;
    aig_and_at(g, i, &lhs, &a, &b);
    Bdd ba = lit_to_bdd(m, eager, a), bb = lit_to_bdd(m, eager, b);
    eager[lhs / 2] = oxidd_bdd_and(ba, bb);
    oxidd_bdd_unref(ba);
    oxidd_bdd_unref(bb);
  }
  CHECK(oxidd_build_roots(&r, g, map, 12, lits, roots, 8));
  CHECK(r.built_gates == 4 && r.relevant_gates == 4);
  for (unsigned i = 0; i < 13; i++)
    CHECK(bdd_invalid(map[i]));
  for (unsigned i = 0; i < 8; i++) {
    Bdd expected = lit_to_bdd(m, eager, lits[i]);
    CHECK(bdd_eq(roots[i], expected));
    oxidd_bdd_unref(expected);
    oxidd_bdd_unref(roots[i]);
  }
  // Invalid selected roots and invalid references in a selected cone fail;
  // an unselected dead cone is not evaluated by this low-level constructor.
  Bdd invalid_roots[1] = {0};
  Bdd invalid_map[13] = {0};
  invalid_map[1] = oxidd_bdd_var(m, 7);
  uint32_t invalid_lit = 26;
  CHECK(!oxidd_build_roots(&r, g, invalid_map, 12, &invalid_lit, invalid_roots,
                           1));
  oxidd_bdd_unref(invalid_map[1]);
  Bdd a = oxidd_bdd_var(m, 7), b = oxidd_bdd_var(m, 8);
  fail_and = 1;
  and_calls = 0;
  Bdd result = oxidd_run_and(&r, a, b);
  CHECK(!bdd_invalid(result) && and_calls == 2 && r.recovered == 1);
  oxidd_bdd_unref(result);
  fail_and = 2;
  and_calls = 0;
  result = oxidd_run_and(&r, a, b);
  CHECK(bdd_invalid(result) && and_calls == 2 && r.retries == 2);
  CHECK(r.failed_operation && !strcmp(r.failed_operation, "and"));
  result = oxidd_run_and(&r, a, b);
  CHECK(bdd_invalid(result) && and_calls == 2);
  CHECK(!bdd_eq((Bdd){0}, (Bdd){0}));
  oxidd_bdd_unref(a);
  oxidd_bdd_unref(b);
  for (unsigned i = 0; i < 13; i++)
    oxidd_bdd_unref(eager[i]);
  aig_free(g);
  oxidd_bdd_manager_unref(m);
}

static void roots_with_prebuilt_gate(void) {
  // Gate 16 is a retained boundary root.  Building output 20 must reuse it,
  // skip both gates in its fanin cone, preserve positive and complemented
  // aliases, and consume every caller-owned map ref.
  Aig *g = read_game("aag 10 2 0 1 3\n2\n4\n20\n"
                     "12 2 4\n16 12 2\n20 16 2\n");
  oxidd_bdd_manager_t m = oxidd_bdd_manager_new(4096, 256, 1);
  oxidd_bdd_manager_add_vars(m, 2);
  OxiddSolveOptions opts = oxidd_solve_options_default();
  OxiddRun r;
  oxidd_run_init(&r, m, &opts, 4096, 256);
  Bdd a = oxidd_bdd_var(m, 0), b = oxidd_bdd_var(m, 1);
  Bdd boundary = oxidd_bdd_and(a, b);
  Bdd not_boundary = oxidd_bdd_not(boundary);
  Bdd expected = oxidd_bdd_and(boundary, a);
  Bdd not_expected = oxidd_bdd_not(expected);
  Bdd map[11] = {0};
  map[1] = oxidd_bdd_ref(a);
  map[2] = oxidd_bdd_ref(b);
  map[8] = oxidd_bdd_ref(boundary);
  uint32_t lits[] = {16, 17, 20, 21};
  Bdd roots[4] = {0};
  CHECK(oxidd_build_roots(&r, g, map, 10, lits, roots, 4));
  CHECK(r.built_gates == 1 && r.relevant_gates == 1);
  CHECK(bdd_eq(roots[0], boundary));
  CHECK(bdd_eq(roots[1], not_boundary));
  CHECK(bdd_eq(roots[2], expected));
  CHECK(bdd_eq(roots[3], not_expected));
  for (unsigned i = 0; i < 11; i++)
    CHECK(bdd_invalid(map[i]));
  for (unsigned i = 0; i < 4; i++)
    oxidd_bdd_unref(roots[i]);
  oxidd_bdd_unref(not_expected);
  oxidd_bdd_unref(expected);
  oxidd_bdd_unref(not_boundary);
  oxidd_bdd_unref(boundary);
  oxidd_bdd_unref(a);
  oxidd_bdd_unref(b);
  aig_free(g);
  oxidd_bdd_manager_unref(m);
}

static void memo_churn(void) {
  oxidd_bdd_manager_t m = oxidd_bdd_manager_new(1024, 64, 1);
  oxidd_bdd_manager_add_vars(m, 9);
  Aig *g = aig_new();
  uint32_t mapping[2] = {aig_input(g, "a"), aig_input(g, "b")};
  Bdd2Aig ctx = {.strat = g, .var2lit = mapping, .var_base = 7, .var_count = 2};
  for (unsigned i = 0; i < 40; i++) {
    Bdd a = oxidd_bdd_var(m, 7), b = oxidd_bdd_var(m, 8);
    Bdd root = i % 2 ? oxidd_bdd_or(a, b) : oxidd_bdd_and(a, b);
    oxidd_bdd_unref(a);
    oxidd_bdd_unref(b);
    oxidd_bdd_manager_gc(m);
    uint32_t out = bdd2aig_root(&ctx, root);
    CHECK(!ctx.error && ctx.memo.n == 0 && ctx.memo.cap == 0);
    for (unsigned assignment = 0; assignment < 4; assignment++) {
      bool *values = calloc(3 + aig_num_ands(g), sizeof *values);
      CHECK(values);
      values[1] = (assignment & 1) != 0;
      values[2] = (assignment & 2) != 0;
      for (uint32_t j = 0; j < aig_num_ands(g); j++) {
        uint32_t lhs, x, y;
        aig_and_at(g, j, &lhs, &x, &y);
        values[lhs / 2] =
            (values[x / 2] ^ (x & 1)) && (values[y / 2] ^ (y & 1));
      }
      bool actual = values[out / 2] ^ (out & 1);
      CHECK(actual == (i % 2 ? assignment != 0 : assignment == 3));
      free(values);
    }
    if (i == 39) {
      fail_calloc = true;
      bdd2aig_root(&ctx, root);
      CHECK(ctx.error && ctx.memo.cap == 0);
    }
    oxidd_bdd_unref(root);
    oxidd_bdd_manager_gc(m);
  }
  aig_free(g);
  oxidd_bdd_manager_unref(m);
}

static void pressure_backoff(void) {
  oxidd_bdd_manager_t m = oxidd_bdd_manager_new(4096, 64, 1);
  oxidd_bdd_manager_add_vars(m, 1);
  Bdd pinned = oxidd_bdd_var(m, 0);
  OxiddSolveOptions opts = oxidd_solve_options_default();
  opts.gc_mode = OXIDD_GC_PRESSURE;
  OxiddRun r;
  // A deliberately low policy threshold forces checkpoints without filling
  // the real arena; the empty manager has nothing collectible.
  oxidd_run_init(&r, m, &opts, 1, 64);
  oxidd_pressure_gc_checkpoint(&r);
  CHECK(r.explicit_gc == 1);
  oxidd_pressure_gc_checkpoint(&r);
  CHECK(r.explicit_gc == 1);
  r.operations = r.next_gc;
  oxidd_pressure_gc_checkpoint(&r);
  CHECK(r.explicit_gc == 2);
  oxidd_phase(&r, "extraction");
  CHECK(r.explicit_gc == 3);
  oxidd_bdd_unref(pinned);
  oxidd_bdd_manager_unref(m);
}

static Aig *unused_mux_game(void) {
  Aig *g = aig_new();
  uint32_t inputs[20];
  for (unsigned i = 0; i < 20; i++) {
    char name[32];
    snprintf(name, sizeof name, "env_%u", i);
    inputs[i] = aig_input(g, name);
  }
  uint32_t latch = aig_latch(g, 0, 0);
  uint32_t values[16];
  memcpy(values, inputs, sizeof values);
  for (unsigned level = 0, n = 16; level < 4; level++, n /= 2)
    for (unsigned i = 0; i < n / 2; i++) {
      uint32_t hi = aig_and(g, inputs[16 + level], values[2 * i + 1]);
      uint32_t lo = aig_and(g, aig_not(inputs[16 + level]), values[2 * i]);
      values[i] = aig_or(g, hi, lo);
    }
  CHECK(aig_set_latch_next(g, latch, values[0]));
  aig_set_output(g, "bad", 0);
  return g;
}

static void demand_avoids_unused_updates(void) {
  // Data-before-address ordering makes this unused mux update expensive.
  // Safety is nevertheless trivial. Compare like-for-like verdict-only runs,
  // and check that full synthesis still tries to preserve the latch update.
  OxiddSolveOptions opts = oxidd_solve_options_default();
  opts.node_cap = 1024;
  opts.cache_cap = 64;
  opts.realizability_only = true;
  OxiddSolveResult result = solve_safety_oxidd_result(unused_mux_game(), &opts);
  CHECK(result.status == OXIDD_SOLVE_ERROR &&
        result.failure.kind == OXIDD_FAILURE_BDD);
  opts.demand_transitions = true;
  result = solve_safety_oxidd_result(unused_mux_game(), &opts);
  CHECK(result.status == OXIDD_SOLVE_REALIZABLE && !result.strategy);
  opts.realizability_only = false;
  result = solve_safety_oxidd_result(unused_mux_game(), &opts);
  CHECK(result.status == OXIDD_SOLVE_ERROR &&
        result.failure.kind == OXIDD_FAILURE_BDD);
  CHECK(!strcmp(result.failure.phase, "strategy_updates"));
}

static void sessions(void) {
  const char *safe =
      "aag 3 2 1 1 0\n2\n4\n6 4 1\n7\ni0 env\ni1 controllable_c\n";
  const char *gr1 =
      "aag 3 2 1 1 0 0 0 1 0\n2\n4\n6 4\n0\n1\n6\ni0 env\ni1 controllable_c\n";
  oxidd_session_init(4096, 256);
  OxiddSolveOptions opts = oxidd_solve_options_default();
  opts.gc_mode = OXIDD_GC_PRESSURE;
  for (unsigned i = 0; i < 12; i++) {
    int unreal = -1;
    Aig *strat = solve_safety_oxidd_ex(read_game(safe), &unreal, &opts);
    CHECK(strat && !unreal);
    aig_free(strat);
    opts.demand_transitions = true;
    opts.realizability_only = true;
    OxiddSolveResult verdict =
        solve_safety_oxidd_result(read_game(safe), &opts);
    CHECK(verdict.status == OXIDD_SOLVE_REALIZABLE && !verdict.strategy);
    opts.demand_transitions = false;
    opts.realizability_only = false;
    strat = solve_gr1_oxidd_ex(read_game(gr1), &unreal, &opts);
    CHECK(strat && !unreal);
    aig_free(strat);
  }
  for (unsigned kind = 0; kind < 2; kind++) {
    const char *ops[] = {"substitute", "apply_exists", "forall", "restrict",
                         "exists"};
    for (unsigned op = 0; op < 5; op++)
      for (unsigned n = 1; n <= 2; n++) {
        Aig *game = read_game(kind ? gr1 : safe);
        fail_operation = ops[op];
        failures = n;
        OxiddFailure failure = {0};
        opts.failure = &failure;
        int unreal = -1;
        Aig *strat = kind ? solve_gr1_oxidd_ex(game, &unreal, &opts)
                          : solve_safety_oxidd_ex(game, &unreal, &opts);
        CHECK(failures == 0 && !unreal);
        if (n == 1)
          CHECK(strat && failure.kind == OXIDD_FAILURE_NONE);
        else
          CHECK(!strat && failure.kind == OXIDD_FAILURE_BDD &&
                !strcmp(failure.operation, ops[op]));
        aig_free(strat);
        opts.failure = NULL;
      }
  }
  Aig *game = read_game(gr1);
  OxiddFailure allocation_failure = {0};
  opts.failure = &allocation_failure;
  fail_realloc = true;
  int failed_unreal = -1;
  CHECK(!solve_gr1_oxidd_ex(game, &failed_unreal, &opts) && !failed_unreal);
  CHECK(!fail_realloc);
  CHECK(allocation_failure.kind == OXIDD_FAILURE_HOST &&
        !strcmp(allocation_failure.operation, "realloc"));
  opts.failure = NULL;
  // The sole run alternates s forever: both GF s and GF !s hold, whereas
  // the system goal GF false cannot. Never claim a winning controller here.
  game = aig_new();
  uint32_t state = aig_latch(game, 0, 0);
  CHECK(aig_set_latch_next(game, state, aig_not(state)));
  aig_set_output(game, "bad", 0);
  uint32_t impossible = 0;
  aig_add_justice(game, &impossible, 1, "impossible");
  aig_add_fairness(game, state, "even");
  aig_add_fairness(game, aig_not(state), "odd");
  CHECK(!solve_gr1_oxidd_ex(game, &failed_unreal, &opts) && failed_unreal);
  opts.node_cap = 8192;
  OxiddFailure failure = {0};
  opts.failure = &failure;
  int unreal = -1;
  CHECK(!solve_safety_oxidd_ex(read_game(safe), &unreal, &opts));
  CHECK(!unreal && failure.kind == OXIDD_FAILURE_CONFIGURATION);
  opts.node_cap = 0;
  opts.var_order = OXIDD_VAR_ORDER_STATE_FIRST;
  failure = (OxiddFailure){0};
  CHECK(!solve_safety_oxidd_ex(read_game(safe), &unreal, &opts));
  CHECK(!unreal && failure.kind == OXIDD_FAILURE_CONFIGURATION &&
        !strcmp(failure.operation, "session_nondefault_order"));
  oxidd_session_free();
}

int main(void) {
  variable_orders();
  roots_and_retry();
  roots_with_prebuilt_gate();
  memo_churn();
  pressure_backoff();
  demand_avoids_unused_updates();
  sessions();
  return 0;
}
