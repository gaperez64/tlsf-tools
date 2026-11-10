#define _POSIX_C_SOURCE 200809L
#include "../../src/lib/expand_check.h"
#include "tlsf/expand.h"
#include "../../src/lib/diagnostic.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void check_impl(const char *declarations, const char *signals,
                       const char *formula, const char *diagnostic,
                       bool expand_all) {
  char source[4096];
  int length =
      snprintf(source, sizeof source,
               "INFO { SEMANTICS: Finite,Mealy; TARGET: Mealy; } "
               "GLOBAL { %s } MAIN { OUTPUTS { o; %s } GUARANTEES { %s; } }",
               declarations, signals, formula);
  assert(length > 0 && (size_t)length < sizeof source);
  char *message = nullptr;
  size_t message_size = 0;
  FILE *in = fmemopen(source, (size_t)length, "r");
  FILE *err = open_memstream(&message, &message_size);
  assert(in && err);
  TlsfSpec *s = spec_parse(in, "scope-unit");
  assert(s);
  FILE *previous = tlsf_diagnostic_swap(err);
  bool ok = expand_all ? expand(s, nullptr, 0) == 0 : expand_check(s);
  tlsf_diagnostic_swap(previous);
  assert(fclose(err) == 0);
  assert(ok == !diagnostic);
  if (diagnostic)
    assert(strstr(message, diagnostic));
  spec_free(s);
  fclose(in);
  free(message);
}

static void check(const char *declarations, const char *signals,
                  const char *formula, const char *diagnostic) {
  check_impl(declarations, signals, formula, diagnostic, false);
}

// The C AST also admits boolean guards directly. Check that recursive LTL
// embedding cannot erase a boolean-only constraint, in either traversal order.
static void recursive_boolean_guard(bool temporal, bool guard_first) {
  char source[512];
  snprintf(source, sizeof source,
           "INFO { SEMANTICS: Mealy; TARGET: Mealy; } GLOBAL { DEFINITIONS { "
           "f(x,n) = n == 0 : %s otherwise : %s; } } "
           "MAIN { OUTPUTS { o; } GUARANTEE { f(true,1); } }",
           guard_first ? "o" : (temporal ? "f(X x,n-1)" : "f(!x,n-1)"),
           guard_first ? (temporal ? "f(X x,n-1)" : "f(!x,n-1)") : "o");
  FILE *in = fmemopen(source, strlen(source), "r");
  assert(in);
  TlsfSpec *s = spec_parse(in, "recursive-boolean-guard");
  fclose(in);
  assert(s);
  Node *guard = node_ap(s->arena, s->defs[0].params[0]);
  if (guard_first)
    s->defs[0].body->if_cond = guard;
  else {
    Node *branch = ARENA_ALLOC(s->arena, Node);
    assert(branch);
    branch->kind = NODE_ITE;
    branch->if_cond = guard;
    branch->if_then = node_ap(s->arena, intern(s->intern, "o"));
    branch->if_else = node_false(s->arena);
    s->defs[0].body->if_else = branch;
  }
  char *message = nullptr;
  size_t size = 0;
  FILE *err = open_memstream(&message, &size);
  assert(err);
  FILE *previous = tlsf_diagnostic_swap(err);
  assert(expand_check(s) == !temporal);
  tlsf_diagnostic_swap(previous);
  fclose(err);
  if (temporal)
    assert(strstr(message, "typing:"));
  free(message);
  spec_free(s);
}

int main(void) {
  for (unsigned temporal = 0; temporal < 2; temporal++)
    for (unsigned first = 0; first < 2; first++)
      recursive_boolean_guard(temporal, first);
  // §§4.1, 4.6: no use-site environment inside a declaration, even in an
  // unused definition, an unselected guard or an empty big-operator domain.
  check("DEFINITIONS { d = k == 1 : true otherwise : false; }", "",
        "&&[k IN {1}] X[k] d", "scoping:");
  check("DEFINITIONS { unused = X[missing] o; }", "", "o", "scoping:");
  check("", "", "&&[k IN {}] X[missing] o", "scoping:");
  check("DEFINITIONS { id(x) = x; }", "", "x", "scoping:");
  check("", "", "(&&[k IN {1}] o) && X[k] o", "scoping:");
  // §4.7's lexical shadowing and later bound sets.
  check("", "", "&&[k IN {1}] &&[k IN {2}] X[k] o", nullptr);
  check("", "", "&&[k IN {1}, j IN {k,k+1}] X[j] o", nullptr);
  check("DEFINITIONS { delay(x) = X[x] o; }", "", "&&[k IN {1,2}] delay(k)",
        nullptr);
  // §§4.3–4.6: one category per lexical binding; fresh loop/pattern names.
  const char *decls[] = {"",
                         "",
                         "DEFINITIONS { enum E = k: 0 other: 1; }",
                         "DEFINITIONS { enum k = label: 0 other: 1; }",
                         "PARAMETERS { k = 1; }",
                         "DEFINITIONS { k = 1; }"};
  const char *sigs[] = {"k;", "k[2];", "", "", "", ""};
  for (unsigned i = 0; i < sizeof decls / sizeof *decls; i++)
    check(decls[i], sigs[i], "&&[k IN {1}] X[k] o", "typing:");
  check("DEFINITIONS { f(o) = o; }", "", "f(1) == 1", nullptr);
  check("DEFINITIONS { f(x) = x ~ X o : o otherwise : false; }", "", "o",
        "typing:");
  check("DEFINITIONS { f(x) = x ~ X x : x otherwise : false; }", "", "o",
        "not fresh");
  check("", "p;", "p[0]", "not a bus");
  check("", "", "&&[k IN {1}] k[0]", "not a bus");
  check("", "", "&&[k IN {1}] k", "wrong category");
  check("DEFINITIONS { enum E = label: 0 other: 1; }", "", "label", "typing:");
  check("DEFINITIONS { enum E = label: 0 other: 1; }", "", "o == label",
        "typing:");
  check("DEFINITIONS { enum E = label: 0 other: 1; }", "b[1];", "b == label",
        nullptr);
  check("DEFINITIONS { f(x) = x[0]; }", "b[1];", "f(X[0] b)", "typing:");
  check("DEFINITIONS { f(x) = x + 1; }", "", "f(o) == 1", "typing:");
  check("DEFINITIONS { f(x) = x == 1 : 2 otherwise : 3; }", "", "f(1) == 2",
        nullptr);
  check_impl(
      "PARAMETERS { N = 1; } DEFINITIONS { enum E = label: 00 other: 11; "
      "use(b) = b == label; }",
      "b[N];", "use(b)", "width mismatch", true);
  check_impl(
      "PARAMETERS { N = 2; } DEFINITIONS { enum E = label: 00 other: 11; "
      "use(b) = b == label; }",
      "b[N];", "use(b)", nullptr, true);
  check_impl("DEFINITIONS { enum E = label: 00 other: 11; "
             "unused = b == label; }",
             "b[1];", "o", "width mismatch", true);
  check("DEFINITIONS { wrap(x,n) = n == 0 : X x otherwise : wrap(X x,n-1); }",
        "", "wrap(o,1)", nullptr);
  check("DEFINITIONS { wrap(x,n) = n == 0 : X[x] o otherwise : "
        "wrap(X x,n-1); }",
        "", "wrap(true,1)", "typing:");
  check_impl("", "b[1]; b_0;", "o", "collides with flattened bus bit", true);
  check_impl("PARAMETERS { N = 2; }", "b[N]; b_1;", "o",
             "collides with flattened bus bit", true);
  check_impl("", "b[1]; b_1;", "o", nullptr, true);
  const char *enum_defs = "DEFINITIONS { enum E = label: 00 other: 11; }";
  check_impl(enum_defs, "b[1]; c[2];", "&&[v IN {b}] &&[v IN {c}] v == label",
             nullptr, true);
  check_impl(enum_defs, "b[1]; c[2];", "&&[v IN ({b,c} (-) {b})] v == label",
             nullptr, true);
  check_impl(enum_defs, "b[1]; c[2];", "&&[v IN ({b,c} (*) {c})] v == label",
             nullptr, true);
  check_impl(enum_defs, "b[1]; c[2];", "&&[v IN ({b,c} (-) {c})] v == label",
             "width mismatch", true);
  check_impl("DEFINITIONS { alias = b; }", "b[2];", "alias[0]", nullptr, true);
  check_impl("DEFINITIONS { alias = b; }", "b[2];", "X[SIZEOF alias] o",
             nullptr, true);
  // §4.5: names remain complete past the former 256-byte boundary, both in
  // duplicate keys and the declaration collision check.
  char bus[255], declarations[530], formula[600];
  memset(bus, 'b', sizeof bus - 1);
  bus[sizeof bus - 1] = '\0';
  snprintf(declarations, sizeof declarations, "%s[2];", bus);
  snprintf(formula, sizeof formula, "SIZE {%s[0],%s[1]} == 2", bus, bus);
  check_impl("", declarations, formula, nullptr, true);
  snprintf(declarations, sizeof declarations, "%s[2]; %s_0;", bus, bus);
  check_impl("", declarations, "o", "collides with flattened bus bit", true);
  check_impl("", "b[1];", "b[1]", "bus index out of range", true);
  check_impl("", "b[1];", "b[-1]", "bus index out of range", true);
  check_impl("DEFINITIONS { alias = b; }", "b[1];", "alias[1]",
             "bus index out of range", true);
  check_impl("", "b[2..3];", "b[2] && b[3]", nullptr, true);
  check_impl("", "b[2..3];", "b[1]", "bus index out of range", true);
  check_impl("DEFINITIONS { f(x,n) = n == 0 : o otherwise : f({x},n-1); }", "",
             "f(1,3)", nullptr, true);
  check_impl("DEFINITIONS { f(x,n) = n == 0 : o otherwise : g({x},n-1); "
             "g(y,n) = f(y,n); }",
             "", "f(1,3)", nullptr, true);
  check("DEFINITIONS { f(x,n) = n == 0 : X x otherwise : f(1,n-1); }", "", "o",
        "typing:");
  check("DEFINITIONS { f(x,n) = n == 0 : x otherwise : f({x},n-1); }", "", "o",
        "typing:");
  const char *alias_defs =
      "DEFINITIONS { enum E = label: 00 other: 11; "
      "alias = second; second = b; bad = alias == label; }";
  check_impl(alias_defs, "b[1];", "o", "width mismatch", true);
  check_impl(alias_defs, "b[2];", "o", nullptr, true);
  check_impl("", "a[SIZE {X[SIZEOF b] o, X o}]; b[2];", "X[SIZEOF a] o",
             nullptr, true);
  check_impl("", "a[SIZE {b[1]}]; b[2];", "a[0]", nullptr, true);
  check_impl("", "a[SIZEOF b]; b[SIZEOF a];", "o",
             "cyclic bus width dependency", true);
  check_impl("", "a[SIZE {b[0]}]; b[SIZEOF a];", "o",
             "cyclic bus width dependency", true);
  puts("expansion_scope: lexical environments and identifier categories "
       "checked");
}
