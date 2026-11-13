// Follow the internal-validator tests: include the implementation to reach its
// static helper, without adding a production symbol or public header.
#define _POSIX_C_SOURCE 200809L
#include "../../src/lib/expand.c"
#include <stddef.h>
#include <stdlib.h>

// Layout census, independent of the production declaration. The source-field
// inventory test additionally catches fields added inside union/padding space.
typedef struct {
  NodeKind kind;
  uint32_t source_id;
  const OriginBinding *origin_bindings;
  bool resolved_signal;
  union {
    struct {
      const char *qvar;
      Node *qlo, *qhi, *qset, *qbody;
      bool qlo_strict, qhi_strict;
    } quant;         // the largest active union arm
    int64_t integer; // preserve the union's alignment on 32-bit platforms too
  } payload;
  struct {
    BoundedTemporalOrigin origin;
    int64_t lo, hi;
    Node *body;
    bool strong;
  } bounded;
} ClassifiedNodeLayout;
_Static_assert(sizeof(Node) == sizeof(ClassifiedNodeLayout),
               "classify new Node fields for SetDedup.lean and set_dedup");
_Static_assert(offsetof(Node, bounded) ==
                   offsetof(ClassifiedNodeLayout, bounded),
               "update the Node payload census for set deduplication");
_Static_assert(sizeof(BoundedTemporalMeta) ==
                   sizeof(((ClassifiedNodeLayout *)0)->bounded),
               "classify new bounded metadata fields for set deduplication");

static unsigned checks;

static void set_growth(void) {
  Arena *arena = arena_new(4096);
  assert(arena);
  EvalSet *set = set_new(arena);
  assert(set);
  size_t retained = 0;
  unsigned allocations = 0;
  for (uint32_t i = 0; i < 1025; i++) {
    EvalValue *previous = set->items;
    EvalValue value = {.kind = EVAL_VALUE_INT, .integer = i};
    assert(set_add(arena, set, value));
    if (set->items != previous) {
      allocations++;
      retained += set->capacity;
    }
    assert(set->count == i + 1);
    previous = set->items;
    assert(set_add(arena, set, value));
    assert(set->count == i + 1 && set->items == previous);
  }
  // Bound allocation churn and retained arena storage across many growths.
  assert(allocations < 16 && retained < 4 * set->count);
  for (uint32_t i = 0; i < set->count; i++)
    assert(set->items[i].kind == EVAL_VALUE_INT && set->items[i].integer == i);
  arena_free(arena);
}

static void equal(const Node *a, const Node *b, bool expected) {
  assert(node_structural_equal(a, b) == expected);
  assert(node_structural_equal(b, a) == expected);
  checks += 2;
}

// Every mutation below changes one field, with the rest copied verbatim.
#define DIFFER(field, value)                                                   \
  do {                                                                         \
    Node changed = a;                                                          \
    changed.field = (value);                                                   \
    equal(&a, &changed, false);                                                \
  } while (0)
#define IGNORE(field, value)                                                   \
  do {                                                                         \
    Node changed = a;                                                          \
    changed.field = (value);                                                   \
    equal(&a, &changed, true);                                                 \
  } while (0)

static void identity_keys(void) {
  char source[] = "INFO { SEMANTICS: Finite,Mealy; TARGET: Mealy; } "
                  "MAIN { OUTPUTS { o; b[1]; } GUARANTEES { "
                  "&&[f IN {X[1] o, X o, X[!1] o}] f; "
                  "&&[f IN CUP[k IN {1,2}] {X[k] o, X[1] o}] f; "
                  "&&[s IN {{X[1] o}, {X o}}] &&[f IN s] f; "
                  "&&[f IN {b[0], X[0] b[0]}] f; "
                  "&&[f IN {F[2:3] o, X X (o || X o)}] f; "
                  "&&[f IN {G[1:3] o, X (o && X (o && X o))}] f; } }";
  FILE *fp = fmemopen(source, strlen(source), "r");
  assert(fp);
  TlsfSpec *s = spec_parse(fp, "identity-unit");
  fclose(fp);
  assert(s && expand_check(s));
  SubstCopy *copies = nullptr;
  BoundState states[2] = {0};
  BusBounds bounds = {.states = {nullptr, states}};
  Env env = {.copies = &copies, .bounds = &bounds};
  env.globals = &env;
  EvalSet *set;
  assert(eval_set(s, s->guarantee.formulas[0]->qset, &env, &set, 0));
  assert(set->count == 2);
  assert(set->items[0].node->kind == NODE_NEXT_N);
  assert(set->items[0].key->kind == NODE_X);
  assert(set->items[1].key->kind == NODE_X_STRONG);
  assert(set->items[0].source == set->items[0].node);
  assert(eval_set(s, s->guarantee.formulas[1]->qset, &env, &set, 0));
  assert(set->count == 2);
  assert(set->items[0].node->lhs->kind == NODE_INT);
  assert(set->items[0].node->lhs->ival == 1);
  assert(set->items[1].node->lhs->ival == 2);
  assert(eval_set(s, s->guarantee.formulas[2]->qset, &env, &set, 0));
  assert(set->count == 1 && set->items[0].set->count == 1);
  assert(eval_set(s, s->guarantee.formulas[3]->qset, &env, &set, 0));
  assert(set->count == 1);
  assert(set->items[0].node->kind == NODE_BUS_INDEX);
  assert(set->items[0].source == set->items[0].node);
  assert(set->items[0].key->kind == NODE_AP);
  assert(set->items[0].key->resolved_signal);
  for (unsigned i = 4; i < 6; i++) {
    assert(eval_set(s, s->guarantee.formulas[i]->qset, &env, &set, 0));
    assert(set->count == 1);
    assert(set->items[0].node->kind == (i == 4 ? NODE_F_RANGE : NODE_G_RANGE));
    assert(set->items[0].key->kind == NODE_X);
  }
  spec_free(s);
}

static void resolved_atoms(void) {
  char source[] = "INFO { SEMANTICS: Mealy; TARGET: Mealy; } "
                  "GLOBAL { DEFINITIONS { b_0 = 7; id(x) = x; } } "
                  "MAIN { OUTPUTS { b[1]; } GUARANTEES { b[0]; } }";
  FILE *fp = fmemopen(source, strlen(source), "r");
  assert(fp);
  TlsfSpec *s = spec_parse(fp, "resolved-atoms-unit");
  fclose(fp);
  assert(s);
  SubstCopy *copies = nullptr;
  Env env = {.copies = &copies};
  env.globals = &env;
  Node *atom = bus_elem_node(s, intern(s->intern, "b"), 0);
  assert(atom && atom->resolved_signal);
  Node *identifier = node_ap(s->arena, atom->name);
  Env child = {.b = {atom->name, 11},
               .parent = &env,
               .copies = &copies,
               .globals = &env};
  assert(close_numeric(s->arena, atom, &child) == atom);
  Node *number = close_numeric(s->arena, identifier, &child);
  assert(number && number->kind == NODE_INT && number->ival == 11);
  int64_t integer;
  assert(eval_int(s, identifier, &child, &integer, 0) && integer == 11);
  char *message = nullptr;
  size_t message_size = 0;
  FILE *err = open_memstream(&message, &message_size);
  assert(err);
  FILE *previous = tlsf_diagnostic_swap(err);
  assert(!eval_int(s, atom, &child, &integer, 0));
  tlsf_diagnostic_swap(previous);
  fclose(err);
  free(message);
  EvalValue value;
  assert(eval_value(s, atom, &child, &value, 0));
  assert(value.kind == EVAL_VALUE_NODE && value.source == atom);
  const DefDecl *id = find_def(s, intern(s->intern, "id"), 1);
  assert(id);
  Node *actuals[] = {atom};
  Node *body = instantiate(s, id, actuals, &child, 0);
  assert(body && body->resolved_signal && body->name == atom->name);
  bool ok = true;
  assert(expand_node(s, body, &child, &ok, 0) == body && ok);
  spec_free(s);
}

static void lexical_provenance(void) {
  char source[] = "INFO { SEMANTICS: Mealy; TARGET: Mealy; } "
                  "GLOBAL { DEFINITIONS { copy(x) = x && X x; d = X o; } } "
                  "MAIN { OUTPUTS { o; } GUARANTEES { "
                  "&&[k IN {1,2}] copy(o); copy(d); } }";
  FILE *fp = fmemopen(source, strlen(source), "r");
  assert(fp);
  TlsfSpec *s = spec_parse(fp, "lexical-provenance-unit");
  fclose(fp);
  assert(s);
  Node *actual = s->guarantee.formulas[1]->call_args[0];
  s->capture_provenance = true;
  assert(expand(s, nullptr, 0) == 0);
  Node *fold = s->guarantee.formulas[0];
  assert(fold->kind == NODE_AND);
  Node *atoms[] = {fold->lhs->lhs, fold->rhs->lhs};
  for (unsigned i = 0; i < 2; i++) {
    assert(atoms[i]->kind == NODE_AP);
    assert(atoms[i]->origin_bindings);
    assert(!strcmp(atoms[i]->origin_bindings->name, "k"));
    assert(atoms[i]->origin_bindings->value == (int64_t)i + 1);
  }
  assert(actual->source_id);
  Node *call = s->guarantee.formulas[1];
  assert(call->kind == NODE_AND && call->lhs->kind == NODE_X);
  assert(call->lhs->source_id == actual->source_id);
  spec_free(s);
}

int main(void) {
  set_growth();
  identity_keys();
  resolved_atoms();
  lexical_provenance();
  Node t = {.kind = NODE_TRUE}, t_copy = t, f = {.kind = NODE_FALSE};
  Node *args[] = {&t, &t}, *same_args[] = {&t_copy, &t_copy};
  Node *first_diff[] = {&f, &t}, *last_diff[] = {&t, &f};
  OriginBinding binding = {.binder_id = 123, .name = "i", .value = 7};
  equal(nullptr, nullptr, true);
  equal(&t, nullptr, false);

  for (NodeKind kind = 0; kind < NODE_KIND_COUNT; kind++) {
    Node a = {.kind = kind};
    switch (kind) {
    case NODE_TRUE:
    case NODE_FALSE:
      break; // no payload: only the kind bears meaning
    case NODE_INT:
      DIFFER(ival, 1);
      break;
    case NODE_AP:
    case NODE_INT_VAR:
      a.name = "a";
      DIFFER(name, "b");
      break;
    case NODE_SIZEOF:
      a.sizeof_name = "a";
      DIFFER(sizeof_name, "b");
      break;
    case NODE_NOT:
    case NODE_X:
    case NODE_X_STRONG:
    case NODE_F:
    case NODE_G:
    case NODE_INT_NEG:
    case NODE_SET_SIZE:
    case NODE_SET_MIN:
    case NODE_SET_MAX:
      a.arg = &t;
      DIFFER(arg, &f);
      IGNORE(arg, &t_copy); // distinct addresses, equal children
      break;
    case NODE_BUS_INDEX:
      a.bus_name = "a";
      a.bus_index = &t;
      DIFFER(bus_name, "b");
      DIFFER(bus_index, &f);
      IGNORE(bus_index, &t_copy);
      break;
    case NODE_DEF_CALL:
    case NODE_PATTERN:
      a.callee = "a";
      a.call_argc = 2;
      a.call_args = args;
      DIFFER(callee, "b");
      DIFFER(call_argc, 1);
      DIFFER(call_args, first_diff);
      DIFFER(call_args, last_diff);
      IGNORE(call_args, same_args);
      break;
    case NODE_ITE:
      a.if_cond = a.if_then = a.if_else = &t;
      DIFFER(if_cond, &f);
      DIFFER(if_then, &f);
      DIFFER(if_else, &f);
      break;
    case NODE_FORALL:
    case NODE_EXISTS:
    case NODE_SUM:
    case NODE_PRODUCT:
    case NODE_SET_BIG_UNION:
    case NODE_SET_BIG_INTER:
      a.qvar = "a";
      a.qlo = a.qhi = a.qset = a.qbody = &t;
      DIFFER(qvar, "b");
      DIFFER(qlo, &f);
      DIFFER(qhi, &f);
      DIFFER(qset, &f);
      DIFFER(qbody, &f);
      DIFFER(qlo_strict, true);
      DIFFER(qhi_strict, true);
      DIFFER(qset, nullptr);
      break;
    case NODE_G_RANGE:
    case NODE_F_RANGE:
      a.qlo = a.qhi = a.qbody = &t;
      DIFFER(qlo, &f);
      DIFFER(qhi, &f);
      DIFFER(qbody, &f);
      DIFFER(bounded.strong, true);
      // These members of the shared quantifier arm are inactive on ranges.
      IGNORE(qvar, "unused");
      IGNORE(qset, &f);
      IGNORE(qlo_strict, true);
      IGNORE(qhi_strict, true);
      break;
    case NODE_SET:
    case NODE_SET_ENUM:
      a.set_size = 2;
      a.set_elems = args;
      DIFFER(set_size, 1);
      DIFFER(set_elems, first_diff);
      DIFFER(set_elems, last_diff);
      IGNORE(set_elems, same_args);
      break;
    case NODE_NEXT_N:
      a.lhs = a.rhs = &t;
      DIFFER(lhs, &f);
      DIFFER(rhs, &f);
      DIFFER(bounded.strong, true);
      break;
    case NODE_AND:
    case NODE_OR:
    case NODE_IMPL:
    case NODE_EQUIV:
    case NODE_R:
    case NODE_W:
    case NODE_U:
    case NODE_M:
    case NODE_INT_ADD:
    case NODE_INT_SUB:
    case NODE_INT_MUL:
    case NODE_INT_DIV:
    case NODE_INT_MOD:
    case NODE_CMP_EQ:
    case NODE_CMP_NE:
    case NODE_CMP_LT:
    case NODE_CMP_LE:
    case NODE_CMP_GT:
    case NODE_CMP_GE:
    case NODE_SET_UNION:
    case NODE_SET_INTER:
    case NODE_SET_DIFF:
    case NODE_IN:
    case NODE_MATCH:
      a.lhs = a.rhs = &t;
      DIFFER(lhs, &f);
      DIFFER(rhs, &f);
      break;
    case NODE_KIND_COUNT:
      assert(false);
    }
    Node copy = a;
    equal(&a, &copy, true);
    equal(&a, &a, true); // pointer fast path
    DIFFER(kind, kind == NODE_TRUE ? NODE_FALSE : NODE_TRUE);
    IGNORE(source_id, 123);
    IGNORE(origin_bindings, &binding);
    IGNORE(resolved_signal, true);
    IGNORE(bounded.origin, BOUNDED_NEXT);
    IGNORE(bounded.lo, 4);
    IGNORE(bounded.hi, 9);
    IGNORE(bounded.body, &f);
    if (kind != NODE_NEXT_N && kind != NODE_G_RANGE && kind != NODE_F_RANGE)
      IGNORE(bounded.strong, true);
  }
  Node sentinel = {.kind = NODE_KIND_COUNT}, sentinel_copy = sentinel;
  equal(&sentinel, &sentinel_copy, false);

  // Exercise the actual value/set callers, including ignored provenance on a
  // recursively nested child. Exactly two meaningfully different values stay.
  Arena *arena = arena_new(4096);
  assert(arena);
  Node one = {.kind = NODE_INT, .ival = 1};
  Node weak = {.kind = NODE_NEXT_N, .lhs = &one, .rhs = &t};
  Node strong = weak, weak_copy = weak;
  strong.bounded.strong = true;
  weak_copy.rhs = &t_copy;
  t_copy.source_id = 42;
  EvalSet *set = set_new(arena);
  assert(set);
  assert(
      set_add(arena, set, (EvalValue){.kind = EVAL_VALUE_NODE, .node = &weak}));
  assert(set_add(arena, set,
                 (EvalValue){.kind = EVAL_VALUE_NODE, .node = &strong}));
  assert(set_add(arena, set,
                 (EvalValue){.kind = EVAL_VALUE_NODE, .node = &weak_copy}));
  assert(set->count == 2);

  // Repeated pattern identifiers demand syntactic identity of captured terms.
  TlsfSpec spec = {.arena = arena};
  Node variable = {.kind = NODE_AP, .name = "p"};
  PatternBinding *bindings = nullptr;
  bool ok = true;
  assert(match_pattern(&spec, &weak, &variable, &bindings, &ok));
  assert(match_pattern(&spec, &weak_copy, &variable, &bindings, &ok));
  assert(!match_pattern(&spec, &strong, &variable, &bindings, &ok));
  assert(ok);
  arena_free(arena);
  printf("set_dedup: %u symmetric equality checks across %u node kinds\n",
         checks, (unsigned)NODE_KIND_COUNT);
  return 0;
}
