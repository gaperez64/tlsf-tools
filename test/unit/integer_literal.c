// Reach eval_int/eval_domain without adding production API, as in set_dedup.
#define _POSIX_C_SOURCE 200809L
#include "../../src/lib/expand.c"
#include "tlsf_parse.h"
#include "tlsf_lex.h"
#include <errno.h>

static unsigned checks;

static TlsfSpec *parse_expression(const char *expression) {
  FILE *input = tmpfile();
  assert(input);
  fprintf(input,
          "INFO { SEMANTICS: Mealy TARGET: Mealy } "
          "MAIN { GUARANTEES { %s; } }",
          expression);
  rewind(input);
  TlsfSpec *spec = spec_parse(input, "integer-literal-unit");
  fclose(input);
  return spec;
}

// IntegerLiteral.lex: both guards, including libc ERANGE, and leading zeros.
static void tokens(void) {
  const struct {
    const char *text;
    int token;
    int64_t value;
  } cases[] = {
      {"0", TOK_INTEGER, 0},
      {"000", TOK_INTEGER, 0},
      {"9223372036854775807", TOK_INTEGER, INT64_MAX},
      {"0009223372036854775807", TOK_INTEGER, INT64_MAX},
      {"9223372036854775808", TOK_MIN_MAGNITUDE, 0},
      {"0009223372036854775808", TOK_MIN_MAGNITUDE, 0},
      {"9223372036854775809", TOK_ERROR, 0},
      {"0009223372036854775809", TOK_ERROR, 0},
      {"18446744073709551615", TOK_ERROR, 0},
      {"18446744073709551616", TOK_ERROR, 0},
      {"9999999999999999999999999999999999999999", TOK_ERROR, 0},
      {"0000000000000000000000000000000000000001", TOK_INTEGER, 1},
  };
  TlsfSpec *spec = spec_new();
  assert(spec);
  yyscan_t scanner;
  assert(yylex_init_extra(spec, &scanner) == 0);
  for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++) {
    YY_BUFFER_STATE buffer = yy_scan_string(cases[i].text, scanner);
    assert(buffer);
    YYSTYPE value = {0};
    YYLTYPE location = {0};
    errno = ERANGE; // The lexer must reset stale range errors.
    assert(yylex(&value, &location, scanner) == cases[i].token);
    if (cases[i].token == TOK_INTEGER)
      assert(value.ival == cases[i].value);
    assert(yylex(&value, &location, scanner) == 0);
    yy_delete_buffer(buffer, scanner);
    checks++;
  }
  yylex_destroy(scanner);
  spec_free(spec);
}

// IntegerLiteral.parse/eval: check the AST as well as the decoded payload.
static void spellings(void) {
  const struct {
    const char *text;
    bool parses, evaluates;
    NodeKind kind;
    int64_t value;
  } cases[] = {
      {"0", true, true, NODE_INT, 0},
      {"-000", true, true, NODE_INT_NEG, 0},
      {"9223372036854775807", true, true, NODE_INT, INT64_MAX},
      {"0009223372036854775807", true, true, NODE_INT, INT64_MAX},
      {"-9223372036854775807", true, true, NODE_INT_NEG, -INT64_MAX},
      {"-9223372036854775808", true, true, NODE_INT, INT64_MIN},
      {"-0009223372036854775808", true, true, NODE_INT, INT64_MIN},
      {"- /* gap */ 9223372036854775808", true, true, NODE_INT, INT64_MIN},
      {"MINUS 9223372036854775808", true, true, NODE_INT, INT64_MIN},
      {"(-9223372036854775808)", true, true, NODE_INT, INT64_MIN},
      {"(-9223372036854775807 - 1)", true, true, NODE_INT_SUB, INT64_MIN},
      {"-(9223372036854775807)", true, true, NODE_INT_NEG, -INT64_MAX},
      {"--9223372036854775808", true, false, NODE_INT_NEG, 0},
      {"-(-9223372036854775808)", true, false, NODE_INT_NEG, 0},
      {"9223372036854775808", false, false, NODE_INT, 0},
      {"0009223372036854775808", false, false, NODE_INT, 0},
      {"-(9223372036854775808)", false, false, NODE_INT, 0},
      {"9223372036854775809", false, false, NODE_INT, 0},
      {"-9223372036854775809", false, false, NODE_INT, 0},
      {"-0009223372036854775809", false, false, NODE_INT, 0},
      {"18446744073709551615", false, false, NODE_INT, 0},
      {"-18446744073709551616", false, false, NODE_INT, 0},
      {"-9999999999999999999999999999999999999999", false, false, NODE_INT, 0},
  };
  for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++) {
    TlsfSpec *spec = parse_expression(cases[i].text);
    assert((spec != nullptr) == cases[i].parses);
    if (spec) {
      const Node *n = spec->guarantee.formulas[0];
      assert(n->kind == cases[i].kind);
      int64_t value;
      Env env = {0};
      assert(eval_int(spec, n, &env, &value, 0) == cases[i].evaluates);
      if (cases[i].evaluates) {
        assert(value == cases[i].value);
        if (n->kind == NODE_INT)
          assert(n->ival == value);
        else if (n->kind == NODE_INT_NEG)
          assert(n->arg->kind == NODE_INT && n->arg->ival == -value);
        else {
          assert(n->lhs->kind == NODE_INT_NEG);
          assert(n->lhs->arg->kind == NODE_INT &&
                 n->lhs->arg->ival == INT64_MAX);
          assert(n->rhs->kind == NODE_INT && n->rhs->ival == 1);
        }
      } else {
        assert(n->arg->kind == NODE_INT && n->arg->ival == INT64_MIN);
      }
      spec_free(spec);
    }
    checks++;
  }
}

// IntegerLiteral.decoded_range_exact: inspect every member of tiny domains
// at both extremes, in the middle, and inverted. Never enumerate a wide range.
static void domains(void) {
  const struct {
    const char *lo, *hi;
    int64_t values[3];
    unsigned count;
  } cases[] = {
      {"-9223372036854775808",
       "-9223372036854775806",
       {INT64_MIN, INT64_MIN + 1, INT64_MIN + 2},
       3},
      {"9223372036854775805",
       "9223372036854775807",
       {INT64_MAX - 2, INT64_MAX - 1, INT64_MAX},
       3},
      {"-1", "1", {-1, 0, 1}, 3},
      {"9223372036854775807", "9223372036854775807", {INT64_MAX}, 1},
      {"-9223372036854775808", "-9223372036854775808", {INT64_MIN}, 1},
      {"9223372036854775807", "-9223372036854775808", {0}, 0},
  };
  for (unsigned i = 0; i < sizeof cases / sizeof *cases; i++)
    for (unsigned flags = 0; flags < 4; flags++) {
      char expression[256];
      snprintf(expression, sizeof expression, "&&[%s %s k %s %s] false",
               cases[i].lo,
               flags & 1 ? "<" : "<=", flags & 2 ? "<" : "<=", cases[i].hi);
      TlsfSpec *spec = parse_expression(expression);
      assert(spec);
      const Node *n = spec->guarantee.formulas[0];
      assert(n->qlo_strict == !!(flags & 1) && n->qhi_strict == !!(flags & 2));
      EvalSet *set;
      Env env = {0};
      assert(eval_domain(spec, n, &env, &set, 0));
      unsigned count = 0;
      for (unsigned k = 0; k < cases[i].count; k++) {
        if (((flags & 1) && k == 0) || ((flags & 2) && k + 1 == cases[i].count))
          continue;
        assert(count < set->count && set->items[count].kind == EVAL_VALUE_INT);
        assert(set->items[count++].integer == cases[i].values[k]);
      }
      assert(count == set->count);
      checks++;
      spec_free(spec);
    }
}

int main(void) {
  FILE *diagnostics = tmpfile();
  assert(diagnostics);
  FILE *previous = tlsf_diagnostic_swap(diagnostics);
  tokens();
  spellings();
  domains();
  tlsf_diagnostic_swap(previous);
  fclose(diagnostics);
  printf("integer literal correspondence: %u checks passed\n", checks);
  return 0;
}
