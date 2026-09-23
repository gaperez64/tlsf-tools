// oxidd_common.c — BDD helpers shared by safety_oxidd.c and gr1_oxidd.c.
//
// See oxidd_common.h.  Memory: OxiDD operations do not take ownership of their
// `oxidd_bdd_t` arguments and return a *new* reference; every returned handle
// must be `oxidd_bdd_unref`'d (a no-op on the invalid/NULL handle).

#define _POSIX_C_SOURCE 200809L
#include "tlsf/oxidd_common.h"

#include <stdarg.h>
#include <stdlib.h>
#include <time.h>

// ---------------------------------------------------------------------------
// Small BDD helpers
// ---------------------------------------------------------------------------

OxiddSolveOptions oxidd_solve_options_default(void) {
#ifdef NDEBUG
  return (OxiddSolveOptions){.node_cap = 0,
                             .cache_cap = 0,
                             .gc_mode = OXIDD_GC_AUTO,
                             .gc_threshold_percent = 80,
                             .verbosity = 0,
                             .trace = stderr,
                             .safety_objective = OXIDD_SAFETY_OBJECTIVE_OUTPUT,
                             .safety_output_index = 0,
                             .var_order = OXIDD_VAR_ORDER_INPUT_FIRST,
                             .build_plan = OXIDD_BUILD_GATES};
#else
  OxiddSolveOptions options = {
      .node_cap = 0,
      .cache_cap = 0,
      .gc_mode = OXIDD_GC_AUTO,
      .gc_threshold_percent = 80,
      .verbosity = 0,
      .trace = stderr,
      .safety_objective = OXIDD_SAFETY_OBJECTIVE_OUTPUT,
      .safety_output_index = 0,
      .var_order = OXIDD_VAR_ORDER_INPUT_FIRST,
      .build_plan = OXIDD_BUILD_GATES,
  };
  options.trace_gate = UINT32_MAX;
  options.trace_node_limit = 100000;
  options.trace_scratch_bytes = (size_t)16 << 20;
  return options;
#endif
}

size_t oxidd_default_capacity(uint32_t local_vars, uint32_t extra_exp) {
  uint32_t exp = local_vars + extra_exp;
  if (exp > 22)
    exp = 22;
  size_t cap = (size_t)1 << exp;
  size_t min = (size_t)1 << 10;
  return cap < min ? min : cap;
}

void oxidd_trace(const OxiddSolveOptions *opts, const char *phase,
                 const char *event, const char *fmt, ...) {
#ifdef NDEBUG
  (void)opts;
  (void)phase;
  (void)event;
  (void)fmt;
  return;
#else
  if (!opts || opts->verbosity == 0)
    return;
  static unsigned long long seq = 0;
  FILE *out = opts->trace ? opts->trace : stderr;
  fprintf(out,
          "TLSFSOLVE_TRACE {\"schema\":1,\"seq\":%llu,"
          "\"phase\":\"%s\",\"event\":\"%s\"",
          ++seq, phase ? phase : "unknown", event ? event : "event");
  if (fmt && *fmt) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(out, fmt, ap);
    va_end(ap);
  }
  fputs("}\n", out);
  fflush(out);
#endif
}

static double monotonic_seconds(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

void oxidd_record_failure(const OxiddSolveOptions *opts, OxiddFailureKind kind,
                          const char *phase, const char *operation,
                          size_t operation_id, uint32_t index) {
  if (opts->failure && opts->failure->kind != OXIDD_FAILURE_NONE)
    return;
  if (opts->failure)
    *opts->failure =
        (OxiddFailure){kind, phase, operation, operation_id, index};
  oxidd_trace(
      opts, phase, "failure",
      ",\"kind\":%u,\"operation\":\"%s\",\"operation_id\":%zu,\"index\":%u",
      (unsigned)kind, operation, operation_id, index);
}

void oxidd_run_init(OxiddRun *r, oxidd_bdd_manager_t m,
                    const OxiddSolveOptions *opts, size_t nodes, size_t cache) {
  *r = (OxiddRun){.manager = m,
                  .options = opts,
                  .phase = "construction",
                  .node_cap = nodes,
                  .cache_cap = cache,
                  .phase_started = monotonic_seconds()};
  oxidd_trace(opts, r->phase, "configuration",
              ",\"node_cap\":%zu,\"cache_cap\":%zu", nodes, cache);
#ifndef NDEBUG
  oxidd_trace(
      opts, r->phase, "construction_plan",
      ",\"requested\":\"gates\",\"effective\":\"gates\","
      "\"plan_version\":1,"
      "\"plan_hash\":"
      "\"8a0c452b2b96d9f8afcc0f65812f72266bfd4578f2e4d425a64e38f58fc6d119\"");
#endif
}

static void sample_nodes(OxiddRun *r) {
  size_t n = oxidd_bdd_manager_approx_num_inner_nodes(r->manager);
  if (n > r->sampled_peak)
    r->sampled_peak = n;
}

static size_t collect(OxiddRun *r, const char *reason) {
  size_t before = oxidd_bdd_manager_approx_num_inner_nodes(r->manager);
  double started = monotonic_seconds();
  uint64_t gc_before = oxidd_bdd_manager_gc_count(r->manager);
  size_t removed = oxidd_bdd_manager_gc(r->manager);
  r->explicit_gc++;
  // A zero return can also mean another collector was active. In either
  // case, wait for deterministic operation progress before trying pressure GC.
  r->next_gc =
      r->operations + (!removed || removed < r->node_cap / 100 ? 4096 : 256);
  oxidd_trace(r->options, r->phase, "gc",
              ",\"reason\":\"%s\",\"stored_nodes_approx\":%zu,"
              "\"removed\":%zu,\"next_gc_operation\":%zu,\"seconds\":%.6f,"
              "\"gc_count_before\":%llu,\"gc_count_after\":%llu",
              reason, before, removed, r->next_gc,
              monotonic_seconds() - started, (unsigned long long)gc_before,
              (unsigned long long)oxidd_bdd_manager_gc_count(r->manager));
  return removed;
}

bool oxidd_pressure_gc_checkpoint(OxiddRun *r) {
  const OxiddSolveOptions *opts = r->options;
  if (opts->gc_mode != OXIDD_GC_PRESSURE || r->operations < r->next_gc)
    return false;
  unsigned threshold =
      opts->gc_threshold_percent ? opts->gc_threshold_percent : 80;
  size_t approx = oxidd_bdd_manager_approx_num_inner_nodes(r->manager);
  size_t limit = (r->node_cap / 100) * threshold +
                 ((r->node_cap % 100) * threshold + 99) / 100;
  if (approx < limit)
    return false;
  return collect(r, "pressure") != 0;
}

void oxidd_phase(OxiddRun *r, const char *phase) {
  sample_nodes(r);
  oxidd_trace(r->options, r->phase, "phase_end",
              ",\"sampled_stored_peak\":%zu,\"operations\":%zu,"
              "\"stored_nodes_approx\":%zu,\"seconds\":%.6f",
              r->sampled_peak, r->operations,
              oxidd_bdd_manager_approx_num_inner_nodes(r->manager),
              monotonic_seconds() - r->phase_started);
  if (strcmp(r->phase, phase))
    r->next_gc = r->operations;
  r->phase = phase;
  r->phase_started = monotonic_seconds();
  r->index = 0;
  oxidd_trace(r->options, phase, "phase_begin", "");
  oxidd_pressure_gc_checkpoint(r);
}

void oxidd_run_finish(OxiddRun *r) {
  sample_nodes(r);
  oxidd_trace(r->options, r->phase, "phase_end",
              ",\"seconds\":%.6f,\"operations\":%zu,\"index\":%u",
              monotonic_seconds() - r->phase_started, r->operations, r->index);
  oxidd_trace(r->options, r->phase, "summary",
              ",\"operations\":%zu,\"retries\":%zu,\"recovered\":%zu,"
              "\"explicit_gc\":%zu,\"sampled_stored_peak\":%zu,"
              "\"built_gates\":%zu,\"relevant_gates\":%zu",
              r->operations, r->retries, r->recovered, r->explicit_gc,
              r->sampled_peak, r->built_gates, r->relevant_gates);
}

static bool operation_begin(OxiddRun *r, const char *op) {
  if (r->failed_operation)
    return false;
  r->operations++;
  oxidd_pressure_gc_checkpoint(r);
  if (r->options->verbosity >= 2)
    oxidd_trace(r->options, r->phase, "op_begin",
                ",\"operation\":\"%s\",\"operation_id\":%zu,\"index\":%u", op,
                r->operations, r->index);
  return true;
}

static Bdd operation_end(OxiddRun *r, const char *op, Bdd result) {
  if (r->options->verbosity)
    sample_nodes(r);
  if (bdd_invalid(result)) {
    r->failed_operation = op;
    oxidd_record_failure(r->options, OXIDD_FAILURE_BDD, r->phase, op,
                         r->operations, r->index);
    oxidd_trace(r->options, r->phase, "failure",
                ",\"operation\":\"%s\",\"operation_id\":%zu,\"index\":%u,"
                "\"reason\":\"invalid_bdd_after_retry\"",
                op, r->operations, r->index);
  } else if (r->options->verbosity >= 2) {
    oxidd_trace(r->options, r->phase, "op_end",
                ",\"operation\":\"%s\",\"operation_id\":%zu", op,
                r->operations);
  }
  return result;
}

// Only pure, BDD-producing operations enter this wrapper. Arguments and
// substitution objects stay owned by the caller across exactly one retry.
#define RUN_OPERATION(name, valid, expression)                                 \
  if (!operation_begin(r, name))                                               \
    return (Bdd){0};                                                           \
  if (!(valid)) {                                                              \
    oxidd_record_failure(r->options, OXIDD_FAILURE_INVALID, r->phase, name,    \
                         r->operations, r->index);                             \
    r->failed_operation = name;                                                \
    return (Bdd){0};                                                           \
  }                                                                            \
  Bdd result = (expression);                                                   \
  if (bdd_invalid(result)) {                                                   \
    r->retries++;                                                              \
    collect(r, "allocation_retry");                                            \
    result = (expression);                                                     \
    if (!bdd_invalid(result))                                                  \
      r->recovered++;                                                          \
    oxidd_trace(r->options, r->phase, "retry",                                 \
                ",\"operation\":\"%s\",\"recovered\":%s", name,                \
                bdd_invalid(result) ? "false" : "true");                       \
  }                                                                            \
  return operation_end(r, name, result)

Bdd oxidd_run_not(OxiddRun *r, Bdd a) {
  RUN_OPERATION("not", !bdd_invalid(a), oxidd_bdd_not(a));
}
Bdd oxidd_run_var(OxiddRun *r, uint32_t var) {
  RUN_OPERATION("var", true, oxidd_bdd_var(r->manager, var));
}
#define BINARY_OPERATION(name)                                                 \
  Bdd oxidd_run_##name(OxiddRun *r, Bdd a, Bdd b) {                            \
    RUN_OPERATION(#name, !bdd_invalid(a) && !bdd_invalid(b),                   \
                  oxidd_bdd_##name(a, b));                                     \
  }
BINARY_OPERATION(and)
BINARY_OPERATION(or)
BINARY_OPERATION(exists)
BINARY_OPERATION(forall)
BINARY_OPERATION(restrict)

Bdd oxidd_run_substitute(OxiddRun *r, Bdd a,
                         const oxidd_bdd_substitution_t *sub) {
  RUN_OPERATION("substitute", !bdd_invalid(a) && sub,
                oxidd_bdd_substitute(a, sub));
}
Bdd oxidd_run_apply_exists(OxiddRun *r, oxidd_boolean_operator op, Bdd a, Bdd b,
                           Bdd vars) {
  RUN_OPERATION("apply_exists",
                !bdd_invalid(a) && !bdd_invalid(b) && !bdd_invalid(vars),
                oxidd_bdd_apply_exists(op, a, b, vars));
}
#undef BINARY_OPERATION
#undef RUN_OPERATION

Bdd oxidd_run_cube(OxiddRun *r, const uint32_t *vars, uint32_t n) {
  Bdd cube = oxidd_bdd_true(r->manager);
  for (uint32_t i = 0; i < n && !bdd_invalid(cube); i++) {
    Bdd v = oxidd_run_var(r, vars[i]);
    Bdd next = oxidd_run_and(r, cube, v);
    oxidd_bdd_unref(cube);
    oxidd_bdd_unref(v);
    cube = next;
  }
  return cube;
}

static bool consume_literal(Bdd *map, size_t *uses, uint32_t lit) {
  uint32_t v = lit / 2;
  if (v && --uses[v] == 0) {
    bool released = !bdd_invalid(map[v]);
    oxidd_bdd_unref(map[v]);
    map[v] = (Bdd){0};
    return released;
  }
  return false;
}

static Bdd run_literal(OxiddRun *r, Bdd *map, uint32_t lit) {
  if (lit < 2)
    return lit ? oxidd_bdd_true(r->manager) : oxidd_bdd_false(r->manager);
  Bdd b = map[lit / 2];
  if (bdd_invalid(b))
    return (Bdd){0};
  return lit & 1 ? oxidd_run_not(r, b) : oxidd_bdd_ref(b);
}

#ifndef NDEBUG
typedef struct {
  size_t nodes, effective_limit, scratch_bytes, invalid_roots;
  double seconds;
  bool complete;
} BoundedNodeCount;

static size_t bdd_identity_hash(Bdd value) {
  size_t hash = (size_t)(uintptr_t)value._p;
  hash ^= value._i + (size_t)0x9e3779b9u + (hash << 6) + (hash >> 2);
  hash ^= hash >> 16;
  return hash;
}

static bool count_layout(size_t requested, size_t root_count,
                         size_t scratch_limit, size_t *effective,
                         size_t *table_capacity, size_t *stack_capacity,
                         size_t *scratch_bytes) {
  size_t limit = requested;
  while (limit) {
    if (limit > (SIZE_MAX - root_count) / 2)
      limit /= 2;
    else {
      size_t table = 1;
      while (table < limit * 2 && table <= SIZE_MAX / 2)
        table *= 2;
      size_t stack = root_count + limit * 2;
      if (table >= limit * 2 && stack <= SIZE_MAX / sizeof(Bdd) &&
          table <= (SIZE_MAX / sizeof(Bdd)) - stack) {
        size_t bytes = (table + stack) * sizeof(Bdd);
        if (bytes <= scratch_limit) {
          *effective = limit;
          *table_capacity = table;
          *stack_capacity = stack;
          *scratch_bytes = bytes;
          return true;
        }
      }
      limit /= 2;
    }
  }
  return false;
}

static BoundedNodeCount bounded_node_union(const Bdd *roots, size_t root_count,
                                           size_t requested_limit,
                                           size_t scratch_limit) {
  BoundedNodeCount result = {.complete = false};
  double started = monotonic_seconds();
  size_t table_capacity = 0, stack_capacity = 0;
  if (!count_layout(requested_limit, root_count, scratch_limit,
                    &result.effective_limit, &table_capacity, &stack_capacity,
                    &result.scratch_bytes)) {
    result.seconds = monotonic_seconds() - started;
    return result;
  }
  Bdd *table = calloc(table_capacity, sizeof *table);
  Bdd *stack = malloc(stack_capacity * sizeof *stack);
  if (!table || !stack) {
    free(stack);
    free(table);
    result.scratch_bytes = 0;
    result.seconds = monotonic_seconds() - started;
    return result;
  }
  size_t top = 0;
  for (size_t i = 0; i < root_count; i++) {
    if (bdd_invalid(roots[i])) {
      result.invalid_roots++;
      continue;
    }
    stack[top++] = oxidd_bdd_ref(roots[i]);
  }
  result.complete = result.invalid_roots == 0;
  while (top) {
    Bdd node = stack[--top];
    if (oxidd_bdd_node_level(node) == (oxidd_level_no_t)-1) {
      oxidd_bdd_unref(node);
      continue;
    }
    size_t slot = bdd_identity_hash(node) & (table_capacity - 1);
    while (!bdd_invalid(table[slot]) && !bdd_same_identity(table[slot], node))
      slot = (slot + 1) & (table_capacity - 1);
    if (!bdd_invalid(table[slot])) {
      oxidd_bdd_unref(node);
      continue;
    }
    if (result.nodes == result.effective_limit) {
      result.complete = false;
      oxidd_bdd_unref(node);
      break;
    }
    table[slot] = node;
    result.nodes++;
    oxidd_bdd_pair_t children = oxidd_bdd_cofactors(node);
    if (bdd_invalid(children.first) || bdd_invalid(children.second) ||
        top + 2 > stack_capacity) {
      oxidd_bdd_unref(children.first);
      oxidd_bdd_unref(children.second);
      result.complete = false;
      break;
    }
    stack[top++] = children.first;
    stack[top++] = children.second;
  }
  while (top)
    oxidd_bdd_unref(stack[--top]);
  for (size_t i = 0; i < table_capacity; i++)
    oxidd_bdd_unref(table[i]);
  free(stack);
  free(table);
  result.seconds = monotonic_seconds() - started;
  return result;
}

enum SupportClass {
  SUPPORT_CONSTANT,
  SUPPORT_INPUT,
  SUPPORT_STATE,
  SUPPORT_MIXED,
};

static enum SupportClass merge_support(enum SupportClass left,
                                       enum SupportClass right) {
  if (left == SUPPORT_CONSTANT)
    return right;
  if (right == SUPPORT_CONSTANT || left == right)
    return left;
  return SUPPORT_MIXED;
}

static unsigned char *aig_support_classes(const Aig *game, uint32_t maxvar) {
  unsigned char *classes = calloc((size_t)maxvar + 1, sizeof *classes);
  if (!classes)
    return nullptr;
  for (uint32_t i = 0; i < aig_num_inputs(game); i++) {
    uint32_t lit;
    aig_input_name(game, i, &lit);
    classes[lit / 2] = SUPPORT_INPUT;
  }
  for (uint32_t i = 0; i < aig_num_latches(game); i++) {
    uint32_t lit;
    aig_latch_at(game, i, &lit, nullptr, nullptr);
    classes[lit / 2] = SUPPORT_STATE;
  }
  for (uint32_t i = 0; i < aig_num_ands(game); i++) {
    uint32_t lhs, left, right;
    aig_and_at(game, i, &lhs, &left, &right);
    classes[lhs / 2] =
        (unsigned char)merge_support(classes[left / 2], classes[right / 2]);
  }
  return classes;
}

static const char *support_name(const unsigned char *classes, uint32_t lit) {
  if (!classes)
    return "unknown";
  switch ((enum SupportClass)classes[lit / 2]) {
  case SUPPORT_CONSTANT:
    return "constant";
  case SUPPORT_INPUT:
    return "primary-input-only";
  case SUPPORT_STATE:
    return "state-only";
  case SUPPORT_MIXED:
    return "mixed";
  }
  return "unknown";
}
#endif

bool oxidd_build_roots(OxiddRun *r, const Aig *game, Bdd *map, uint32_t maxvar,
                       const uint32_t *lits, Bdd *roots, size_t count) {
  size_t uses_count = (size_t)maxvar + 1;
  size_t *uses = oxidd_host_realloc(nullptr, uses_count * sizeof *uses);
  if (!uses) {
    oxidd_record_failure(r->options, OXIDD_FAILURE_HOST, r->phase, "realloc",
                         r->operations, r->index);
    return false;
  }
  memset(uses, 0, uses_count * sizeof *uses);
  Bdd *published =
      count ? oxidd_host_realloc(nullptr, count * sizeof *published) : nullptr;
  if (count && !published) {
    oxidd_record_failure(r->options, OXIDD_FAILURE_HOST, r->phase, "realloc",
                         r->operations, r->index);
    free(uses);
    return false;
  }
  if (published)
    memset(published, 0, count * sizeof *published);
  bool ok = true;
  size_t retained = 0, peak = 0, released = 0;
#ifndef NDEBUG
  unsigned char *support =
      r->options->verbosity && r->options->trace_gate != UINT32_MAX
          ? aig_support_classes(game, maxvar)
          : nullptr;
#endif
  for (uint32_t v = 1; v <= maxvar; v++)
    retained += !bdd_invalid(map[v]);
  peak = retained;
  for (size_t i = 0; i < count; i++) {
    if (lits[i] / 2 > maxvar) {
      ok = false;
      break;
    }
    if (lits[i] > 1)
      uses[lits[i] / 2]++;
#ifndef NDEBUG
    if (r->options->verbosity && r->options->trace_roots)
      oxidd_trace(r->options, r->phase, "root_descriptor",
                  ",\"root_index\":%zu,\"aig_literal\":%u", i, lits[i]);
#endif
  }
  uint32_t ngates = aig_num_ands(game);
  // The reader and AIG builder guarantee topological gate order. Count each
  // edge, including duplicate/complemented operands, and every root occurrence.
  for (uint32_t i = ngates; i > 0 && ok; i--) {
    uint32_t lhs, a, b;
    aig_and_at(game, i - 1, &lhs, &a, &b);
    if (!uses[lhs / 2])
      continue;
    if (a / 2 > maxvar || b / 2 > maxvar) {
      ok = false;
      break;
    }
    if (a > 1)
      uses[a / 2]++;
    if (b > 1)
      uses[b / 2]++;
    r->relevant_gates++;
  }
  for (uint32_t v = 1; v <= maxvar; v++)
    if (!uses[v]) {
      if (!bdd_invalid(map[v])) {
        retained--;
        released++;
      }
      oxidd_bdd_unref(map[v]);
      map[v] = (Bdd){0};
    }
  for (uint32_t i = 0; i < ngates && ok; i++) {
    uint32_t lhs, a, b;
    aig_and_at(game, i, &lhs, &a, &b);
    if (!uses[lhs / 2])
      continue;
    r->index = i;
#ifndef NDEBUG
    bool selected = r->options->verbosity && r->options->trace_gate == i;
    size_t stored_before = 0;
    if (selected) {
      stored_before = oxidd_bdd_manager_approx_num_inner_nodes(r->manager);
      oxidd_trace(r->options, r->phase, "selected_gate_begin",
                  ",\"normalized_gate_index\":%u,\"source_index_kind\":"
                  "\"normalized-only\",\"aig_literal\":%u,\"left_literal\":%u,"
                  "\"right_literal\":%u,\"left_support\":\"%s\","
                  "\"right_support\":\"%s\",\"result_support\":\"%s\","
                  "\"result_uses\":%zu,\"left_uses\":%zu,\"right_uses\":%zu,"
                  "\"stored_nodes_before\":%zu,\"operation\":\"and\"",
                  i, lhs, a, b, support_name(support, a),
                  support_name(support, b), support_name(support, lhs),
                  uses[lhs / 2], uses[a / 2], uses[b / 2], stored_before);
    }
#endif
    Bdd ba = run_literal(r, map, a);
    Bdd bb = run_literal(r, map, b);
    Bdd result = oxidd_run_and(r, ba, bb);
#ifndef NDEBUG
    if (selected) {
      BoundedNodeCount left =
          bounded_node_union(&ba, 1, r->options->trace_node_limit,
                             r->options->trace_scratch_bytes);
      BoundedNodeCount right =
          bounded_node_union(&bb, 1, r->options->trace_node_limit,
                             r->options->trace_scratch_bytes);
      BoundedNodeCount output =
          bounded_node_union(&result, 1, r->options->trace_node_limit,
                             r->options->trace_scratch_bytes);
      oxidd_trace(r->options, r->phase, "selected_gate_end",
                  ",\"normalized_gate_index\":%u,\"aig_literal\":%u,"
                  "\"stored_nodes_before\":%zu,\"stored_nodes_after\":%zu,"
                  "\"left_nodes_lower_bound\":%zu,\"left_complete\":%s,"
                  "\"right_nodes_lower_bound\":%zu,\"right_complete\":%s,"
                  "\"result_nodes_lower_bound\":%zu,\"result_complete\":%s,"
                  "\"node_visit_limit\":%zu,\"scratch_limit_bytes\":%zu,"
                  "\"count_seconds\":%.6f",
                  i, lhs, stored_before,
                  oxidd_bdd_manager_approx_num_inner_nodes(r->manager),
                  left.nodes, left.complete ? "true" : "false", right.nodes,
                  right.complete ? "true" : "false", output.nodes,
                  output.complete ? "true" : "false",
                  r->options->trace_node_limit, r->options->trace_scratch_bytes,
                  left.seconds + right.seconds + output.seconds);
    }
#endif
    oxidd_bdd_unref(ba);
    oxidd_bdd_unref(bb);
    map[lhs / 2] = result;
    retained += !bdd_invalid(result);
    if (retained > peak)
      peak = retained;
    size_t dropped = (size_t)consume_literal(map, uses, a);
    dropped += consume_literal(map, uses, b);
    retained -= dropped;
    released += dropped;
    r->built_gates++;
    ok = !bdd_invalid(result);
  }
  for (size_t i = 0; i < count && ok; i++) {
    published[i] = run_literal(r, map, lits[i]);
    ok = !bdd_invalid(published[i]);
    bool dropped = consume_literal(map, uses, lits[i]);
    retained -= dropped;
    released += dropped;
  }
#ifndef NDEBUG
  if (r->options->verbosity && r->options->trace_roots && ok) {
    BoundedNodeCount root_union =
        bounded_node_union(published, count, r->options->trace_node_limit,
                           r->options->trace_scratch_bytes);
    oxidd_trace(r->options, r->phase, "root_node_union",
                ",\"distinct_inner_nodes_lower_bound\":%zu,\"complete\":%s,"
                "\"invalid_roots\":%zu,\"requested_node_limit\":%zu,"
                "\"effective_node_limit\":%zu,\"scratch_limit_bytes\":%zu,"
                "\"scratch_bytes\":%zu,\"seconds\":%.6f",
                root_union.nodes, root_union.complete ? "true" : "false",
                root_union.invalid_roots, r->options->trace_node_limit,
                root_union.effective_limit, r->options->trace_scratch_bytes,
                root_union.scratch_bytes, root_union.seconds);
  }
  free(support);
#endif
  oxidd_trace(r->options, r->phase, "construction_roots",
              ",\"map_references_peak\":%zu,\"map_references_released\":%zu,"
              "\"map_references_remaining\":%zu,\"requested_roots\":%zu",
              peak, released, retained, count);
  if (ok)
    for (size_t i = 0; i < count; i++) {
      roots[i] = published[i];
      published[i] = (Bdd){0};
    }
  for (size_t i = 0; i < count; i++)
    oxidd_bdd_unref(published[i]);
  free(published);
  free(uses);
  return ok;
}

bool oxidd_build_game(OxiddRun *r, const Aig *game, Bdd *map, uint32_t maxvar,
                      Bdd *bad, Bdd *next, Bdd *goals, Bdd *fair) {
  bool typed =
      r->options->safety_objective == OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR;
  uint32_t nb = typed ? aig_num_bad(game) : 1;
  uint32_t nl = r->options->demand_transitions ? 0 : aig_num_latches(game);
  uint32_t nj = aig_num_justice(game);
  uint32_t nf = aig_num_fairness(game);
  size_t count = (size_t)nb + nl + nj + nf;
  uint32_t *lits = calloc(count, sizeof *lits);
  Bdd *roots = calloc(count, sizeof *roots);
  bool ok = lits && roots;
  size_t k = 0;
  for (uint32_t i = 0; i < nb && ok; i++) {
    if (typed)
      aig_bad_at(game, i, &lits[k++]);
    else if (r->options->safety_output_index < aig_num_outputs(game))
      aig_output_at(game, r->options->safety_output_index, &lits[k++]);
    else
      ok = false;
  }
  for (uint32_t i = 0; i < nl && ok; i++)
    aig_latch_at(game, i, NULL, &lits[k++], NULL);
  for (uint32_t i = 0; i < nj && ok; i++) {
    const uint32_t *js;
    uint32_t n;
    aig_justice_at(game, i, &js, &n);
    if (n != 1 || !goals)
      ok = false;
    else
      lits[k++] = js[0];
  }
  for (uint32_t i = 0; i < nf && ok; i++) {
    if (!fair)
      ok = false;
    else
      lits[k++] = aig_fairness_at(game, i);
  }
  if (ok)
    ok = oxidd_build_roots(r, game, map, maxvar, lits, roots, count);
  if (ok) {
    *bad = oxidd_bdd_false(r->manager);
    for (uint32_t i = 0; i < nb; i++) {
      Bdd b = oxidd_run_or(r, *bad, roots[i]);
      oxidd_bdd_unref(*bad);
      *bad = b;
    }
    ok = !bdd_invalid(*bad);
    k = nb;
    for (uint32_t i = 0; i < nl; i++, k++) {
      next[i] = roots[k];
      roots[k] = (Bdd){0};
    }
    for (uint32_t i = 0; i < nj; i++, k++) {
      goals[i] = roots[k];
      roots[k] = (Bdd){0};
    }
    for (uint32_t i = 0; i < nf; i++, k++) {
      fair[i] = roots[k];
      roots[k] = (Bdd){0};
    }
  }
  if (roots)
    for (size_t i = 0; i < count; i++)
      oxidd_bdd_unref(roots[i]);
  free(roots);
  free(lits);
  return ok;
}

Bdd lit_to_bdd(oxidd_bdd_manager_t m, const Bdd *var_bdd, uint32_t lit) {
  if (lit == AIG_FALSE)
    return oxidd_bdd_false(m);
  if (lit == AIG_TRUE)
    return oxidd_bdd_true(m);
  Bdd base = var_bdd[lit / 2];
  if (bdd_invalid(base))
    return (Bdd){0};
  return (lit & 1u) ? oxidd_bdd_not(base) : oxidd_bdd_ref(base);
}

Bdd cube_of(oxidd_bdd_manager_t m, const uint32_t *vars, uint32_t n) {
  Bdd cube = oxidd_bdd_true(m);
  for (uint32_t i = 0; i < n; i++) {
    Bdd v = oxidd_bdd_var(m, vars[i]);
    Bdd nx = oxidd_bdd_and(cube, v);
    oxidd_bdd_unref(cube);
    oxidd_bdd_unref(v);
    cube = nx;
  }
  return cube;
}

bool bdd_same_identity(Bdd a, Bdd b) {
  return !bdd_invalid(a) && !bdd_invalid(b) && a._p == b._p && a._i == b._i;
}

bool bdd_eq(Bdd a, Bdd b) {
  // OxiDD BDDs are canonical within one manager.  Field-wise identity is
  // allocation-free and avoids retaining extra equivalence roots just to test
  // fixpoint convergence or memo keys.
  return bdd_same_identity(a, b);
}

// ---------------------------------------------------------------------------
// BDD node -> AIG memo (open-addressing hash on the 16-byte handle identity)
// ---------------------------------------------------------------------------

static uint64_t memo_hash(Bdd k) {
  uint64_t h = 1469598103934665603ull;
  uintptr_t p = (uintptr_t)k._p;
  for (size_t i = 0; i < sizeof p; i++) {
    h ^= (unsigned char)(p >> (i * 8));
    h *= 1099511628211ull;
  }
  for (size_t i = 0; i < sizeof k._i; i++) {
    h ^= (unsigned char)(k._i >> (i * 8));
    h *= 1099511628211ull;
  }
  return h;
}

static bool memo_grow(Memo *t, size_t cap) {
  Bdd *keys = calloc(cap, sizeof *keys);
  uint32_t *lits = calloc(cap, sizeof *lits);
  bool *used = calloc(cap, sizeof *used);
  if (!keys || !lits || !used) {
    free(keys);
    free(lits);
    free(used);
    return false;
  }
  for (size_t i = 0; i < t->cap; i++) {
    if (!t->used[i])
      continue;
    size_t j = memo_hash(t->keys[i]) & (cap - 1);
    while (used[j])
      j = (j + 1) & (cap - 1);
    keys[j] = t->keys[i];
    lits[j] = t->lits[i];
    used[j] = true;
  }
  free(t->keys);
  free(t->lits);
  free(t->used);
  t->keys = keys;
  t->lits = lits;
  t->used = used;
  t->cap = cap;
  return true;
}

// Returns true and sets *lit if `k` is memoised; otherwise returns false.
static bool memo_get(const Memo *t, Bdd k, uint32_t *lit) {
  if (t->cap == 0)
    return false;
  size_t j = memo_hash(k) & (t->cap - 1);
  while (t->used[j]) {
    if (bdd_same_identity(t->keys[j], k)) {
      *lit = t->lits[j];
      return true;
    }
    j = (j + 1) & (t->cap - 1);
  }
  return false;
}

static bool memo_put(Memo *t, Bdd k, uint32_t lit) {
  if (t->n * 10 >= t->cap * 7) // grow at load factor 0.7
    if (!memo_grow(t, t->cap ? t->cap * 2 : 64))
      return false;
  size_t j = memo_hash(k) & (t->cap - 1);
  while (t->used[j]) {
    if (bdd_same_identity(t->keys[j], k)) {
      t->lits[j] = lit;
      return true;
    }
    j = (j + 1) & (t->cap - 1);
  }
  t->keys[j] = k;
  t->lits[j] = lit;
  t->used[j] = true;
  t->n++;
  return true;
}

void memo_free(Memo *t) {
  free(t->keys);
  free(t->lits);
  free(t->used);
  *t = (Memo){0};
}

static bool visit_support(Bdd f, uint32_t base, uint32_t count, bool *support,
                          Memo *seen) {
  if (bdd_invalid(f))
    return false;
  if (oxidd_bdd_node_level(f) == (oxidd_level_no_t)-1)
    return true;
  uint32_t ignored;
  if (memo_get(seen, f, &ignored))
    return true;
  uint32_t var = oxidd_bdd_node_var(f);
  if (var < base || var - base >= count)
    return false;
  support[var - base] = true;
  if (!memo_put(seen, f, 0))
    return false;
  Bdd hi = oxidd_bdd_cofactor_true(f), lo = oxidd_bdd_cofactor_false(f);
  bool ok = visit_support(hi, base, count, support, seen) &&
            visit_support(lo, base, count, support, seen);
  oxidd_bdd_unref(hi);
  oxidd_bdd_unref(lo);
  return ok;
}

bool oxidd_state_support(Bdd root, uint32_t base, uint32_t count,
                         bool *support) {
  Memo seen = {0};
  bool ok = visit_support(root, base, count, support, &seen);
  memo_free(&seen);
  return ok;
}

// ---------------------------------------------------------------------------
// Persistent BDD manager session
// ---------------------------------------------------------------------------

static oxidd_bdd_manager_t g_session_mgr = {._p = NULL};
static uint32_t g_session_var_base = 0;
static size_t g_session_nodes, g_session_cache;

void oxidd_session_init(uint32_t inner_cap, uint32_t cache_cap) {
  oxidd_session_free();
  g_session_mgr = oxidd_bdd_manager_new(inner_cap, cache_cap, 1);
  g_session_var_base = 0;
  g_session_nodes = inner_cap;
  g_session_cache = cache_cap;
}

bool oxidd_session_config(const OxiddSolveOptions *opts, size_t *nodes,
                          size_t *cache) {
  *nodes = g_session_nodes;
  *cache = g_session_cache;
  return (!opts->node_cap || opts->node_cap == *nodes) &&
         (!opts->cache_cap || opts->cache_cap == *cache);
}

void oxidd_session_free(void) {
  if (g_session_mgr._p) {
    oxidd_bdd_manager_unref(g_session_mgr);
    g_session_mgr._p = NULL;
  }
  g_session_var_base = 0;
}

oxidd_bdd_manager_t oxidd_session_get(void) { return g_session_mgr; }

uint32_t oxidd_session_alloc_vars(uint32_t n) {
  if (n > UINT32_MAX - g_session_var_base)
    return UINT32_MAX;
  uint32_t base = g_session_var_base;
  oxidd_bdd_manager_add_vars(g_session_mgr, n);
  g_session_var_base += n;
  return base;
}

void oxidd_session_gc(void) {
  if (g_session_mgr._p)
    oxidd_bdd_manager_gc(g_session_mgr);
}

// ---------------------------------------------------------------------------
// BDD -> AIG (memoised ite expansion over the strategy AIG)
// ---------------------------------------------------------------------------

uint32_t bdd2aig(Bdd2Aig *ctx, Bdd f) {
  if (ctx->error)
    return AIG_FALSE;
  if (bdd_invalid(f)) {
    ctx->error = true;
    return AIG_FALSE;
  }
  if (oxidd_bdd_node_level(f) == (oxidd_level_no_t)-1) // terminal
    return oxidd_bdd_satisfiable(f) ? AIG_TRUE : AIG_FALSE;
  uint32_t cached;
  if (memo_get(&ctx->memo, f, &cached))
    return cached;
  oxidd_var_no_t abs_v = oxidd_bdd_node_var(f);
  if (abs_v < ctx->var_base || abs_v - ctx->var_base >= ctx->var_count) {
    ctx->error = true;
    return AIG_FALSE;
  }
  oxidd_var_no_t v = abs_v - ctx->var_base;
  uint32_t vlit = ctx->var2lit[v];
  if (vlit ==
      UINT32_MAX) { // a variable that must not appear (e.g. controllable)
    ctx->error = true;
    return AIG_FALSE;
  }
  Bdd t = oxidd_bdd_cofactor_true(f);
  Bdd e = oxidd_bdd_cofactor_false(f);
  uint32_t at = bdd2aig(ctx, t);
  uint32_t ae = bdd2aig(ctx, e);
  oxidd_bdd_unref(t);
  oxidd_bdd_unref(e);
  uint32_t hi = aig_and(ctx->strat, vlit, at);
  uint32_t lo = aig_and(ctx->strat, aig_not(vlit), ae);
  uint32_t res = aig_or(ctx->strat, hi, lo);
  if (!memo_put(&ctx->memo, f, res))
    ctx->error = true;
  return res;
}

uint32_t bdd2aig_root(Bdd2Aig *ctx, Bdd f) {
  memo_free(&ctx->memo);
  uint32_t lit = bdd2aig(ctx, f);
  memo_free(&ctx->memo);
  return lit;
}
