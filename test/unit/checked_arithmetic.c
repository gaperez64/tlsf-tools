// Private evaluator correspondence, following integer_literal and set_dedup.
#define _POSIX_C_SOURCE 200809L
#include "../../src/lib/expand.c"

static unsigned checks;

// Independent wide-integer oracle: no checked builtin and no signed-64
// operation.
static bool mathematical(NodeKind op, int64_t a, int64_t b, int64_t *out) {
  __int128_t value;
  if (op == NODE_INT_DIV || op == NODE_INT_MOD) {
    if (!b || (a == INT64_MIN && b == -1))
      return false;
    value = op == NODE_INT_DIV ? (__int128_t)a / b : (__int128_t)a % b;
  } else if (op == NODE_INT_ADD)
    value = (__int128_t)a + b;
  else if (op == NODE_INT_SUB)
    value = (__int128_t)a - b;
  else
    value = (__int128_t)a * b;
  if (value < INT64_MIN || value > INT64_MAX)
    return false;
  *out = (int64_t)value;
  return true;
}

// apply_iff/boundary_witnesses: guard edges, operand order, signs and C
// quotient semantics.
static void operators(void) {
  const int64_t values[] = {INT64_MIN,
                            INT64_MIN + 1,
                            -INT64_MAX,
                            -3037000500,
                            -3037000499,
                            -7,
                            -2,
                            -1,
                            0,
                            1,
                            2,
                            3,
                            3037000499,
                            3037000500,
                            INT64_MAX - 1,
                            INT64_MAX};
  const NodeKind ops[] = {NODE_INT_ADD, NODE_INT_SUB, NODE_INT_MUL,
                          NODE_INT_DIV, NODE_INT_MOD};
  TlsfSpec *spec = spec_new();
  assert(spec);
  const char *x = intern(spec->intern, "x"), *y = intern(spec->intern, "y");
  Node lhs = {.kind = NODE_INT_VAR, .name = x};
  Node rhs = {.kind = NODE_INT_VAR, .name = y};
  for (unsigned i = 0; i < sizeof values / sizeof *values; i++) {
    Env outer = {.b = {.name = x, .value = 42}};
    Env env = {.b = {.name = x, .value = values[i]}, .parent = &outer};
    Node neg = {.kind = NODE_INT_NEG, .arg = &lhs};
    int64_t actual = 42;
    bool ok = eval_int(spec, &neg, &env, &actual, 0);
    assert(ok == (values[i] != INT64_MIN));
    if (ok)
      assert((__int128_t)actual == -(__int128_t)values[i]);
    checks++;
    for (unsigned j = 0; j < sizeof values / sizeof *values; j++) {
      Env child = {.b = {.name = y, .value = values[j]}, .parent = &env};
      for (unsigned k = 0; k < sizeof ops / sizeof *ops; k++) {
        Node expression = {.kind = ops[k], .lhs = &lhs, .rhs = &rhs};
        int64_t expected;
        bool fits = mathematical(ops[k], values[i], values[j], &expected);
        ok = eval_int(spec, &expression, &child, &actual, 0);
        assert(ok == fits);
        if (ok)
          assert(actual == expected);
        // Builtins may overwrite scratch out on false; callers must honor bool.
        checks++;
      }
    }
  }
  spec_free(spec);
}

static TlsfSpec *parse_expression(const char *expression) {
  FILE *input = tmpfile();
  assert(input);
  fprintf(input,
          "INFO { SEMANTICS: Mealy TARGET: Mealy } "
          "MAIN { GUARANTEES { %s; } }",
          expression);
  rewind(input);
  TlsfSpec *spec = spec_parse(input, "checked-arithmetic-unit");
  fclose(input);
  assert(spec);
  return spec;
}

// eval_iff/eval_rejects: prefixes, empty seeds, binder environments and nested
// reductions.
static void accumulators(void) {
  const struct {
    const char *expression;
    bool ok;
    int64_t value;
  } cases[] = {
      {"+[0 <= k <= 1] 9223372036854775807", false, 0},
      {"+[0 <= k <= 1] -9223372036854775808", false, 0},
      {"*[0 <= k <= 1] 9223372036854775807", false, 0},
      {"*[k IN {-9223372036854775808, -1}] k", false, 0},
      {"+[k IN {9223372036854775807, 1, -1}] k", false, 0},
      {"*[k IN {9223372036854775807, 2, 0}] k", false, 0},
      {"+[1 <= k <= 0] (9223372036854775807 + 1)", true, 0},
      {"*[1 <= k <= 0] (9223372036854775807 + 1)", true, 1},
      {"+[k IN {9223372036854775807, -1}] k", true, INT64_MAX - 1},
      {"*[k IN {-9223372036854775808, 1}] k", true, INT64_MIN},
      {"+[0 <= k <= 2] k", true, 3},
      {"*[1 <= k <= 3] k", true, 6},
      {"+[0 <= k <= 1] (+[0 <= j <= 1] (k + j))", true, 4},
      {"*[0 <= k <= 1] (+[0 <= j <= 1] (k + j))", true, 3},
      {"+[0 <= k <= 1] (-9223372036854775808 / (-1))", false, 0},
      {"*[0 <= k <= 1] (-9223372036854775808 % (-1))", false, 0},
  };
  for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++) {
    TlsfSpec *spec = parse_expression(cases[i].expression);
    SubstCopy *copies = nullptr;
    Env env = {.copies = &copies};
    int64_t value = 42;
    bool ok = eval_int(spec, spec->guarantee.formulas[0], &env, &value, 0);
    assert(ok == cases[i].ok);
    // The reduction publishes acc only at the end, even after some successful
    // terms.
    assert(value == (ok ? cases[i].value : 42));
    checks++;
    spec_free(spec);
  }
}

// eval_domain_exact/issue115_rejected: computed endpoints, all strictness
// flags, reversed intervals and both extremes. Existing #116 units check
// literal domains.
static void domains(void) {
  const struct {
    const char *lo, *hi;
    bool ok;
    int64_t first, last;
  } cases[] = {
      {"0", "((9223372036854775807 + 1) / 9223372036854775807)", false, 0, 0},
      {"1", "((9223372036854775807 * 2) / 9223372036854775807)", false, 0, 0},
      {"0", "(-(-9223372036854775807 - 1) / 9223372036854775807)", false, 0, 0},
      {"0", "(-9223372036854775808 / (-1))", false, 0, 0},
      {"0", "(-9223372036854775808 % (-1))", false, 0, 0},
      {"(9223372036854775807 + 1)", "0", false, 0, 0},
      {"9223372036854775807", "(9223372036854775807 + 1)", false, 0, 0},
      {"0", "(+[0 <= j <= 1] 9223372036854775807)", false, 0, 0},
      {"0", "(*[0 <= j <= 1] 9223372036854775807)", false, 0, 0},
      {"(+[0 <= j <= 1] j)", "(*[1 <= j <= 2] j)", true, 1, 2},
      {"(*[1 <= j <= 2] j)", "(+[0 <= j <= 1] j)", true, 2, 1},
      {"(-9223372036854775807 - 1)", "(-9223372036854775808 + 2)", true,
       INT64_MIN, INT64_MIN + 2},
      {"(9223372036854775807 - 2)", "(9223372036854775807 * 1)", true,
       INT64_MAX - 2, INT64_MAX},
      {"(+[0 <= j <= 0] -9223372036854775808)", "(-9223372036854775808 * 1)",
       true, INT64_MIN, INT64_MIN},
      {"(9223372036854775807 + 0)", "(*[0 <= j <= 0] 9223372036854775807)",
       true, INT64_MAX, INT64_MAX},
  };
  for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++)
    for (unsigned flags = 0; flags < 4; flags++) {
      char expression[512];
      snprintf(expression, sizeof expression, "&&[%s %s k %s %s] false",
               cases[i].lo,
               flags & 1 ? "<" : "<=", flags & 2 ? "<" : "<=", cases[i].hi);
      TlsfSpec *spec = parse_expression(expression);
      Node *n = spec->guarantee.formulas[0];
      SubstCopy *copies = nullptr;
      Env env = {.copies = &copies};
      EvalSet sentinel = {0}, *domain = &sentinel;
      assert(eval_domain(spec, n, &env, &domain, 0) == cases[i].ok);
      if (!cases[i].ok) {
        assert(domain == &sentinel);
        bool ok = true;
        assert(expand_quantifier(spec, n, &env, &ok, 0) == nullptr && !ok);
      } else {
        // Compute strict shifts in 128 bits, including MAX+1 and MIN-1 empties.
        __int128_t first = (__int128_t)cases[i].first + !!(flags & 1);
        __int128_t last = (__int128_t)cases[i].last - !!(flags & 2);
        unsigned count = 0;
        for (__int128_t k = first; k <= last; k++) {
          assert(count < domain->count);
          assert(domain->items[count].kind == EVAL_VALUE_INT);
          assert((__int128_t)domain->items[count++].integer == k);
        }
        assert(count == domain->count);
      }
      checks++;
      spec_free(spec);
    }
}

int main(void) {
  FILE *diagnostics = tmpfile();
  assert(diagnostics);
  FILE *previous = tlsf_diagnostic_swap(diagnostics);
  operators();
  accumulators();
  domains();
  tlsf_diagnostic_swap(previous);
  fclose(diagnostics);
  printf("checked arithmetic correspondence: %u checks passed\n", checks);
  return 0;
}
