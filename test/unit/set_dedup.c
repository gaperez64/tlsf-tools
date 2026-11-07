// Follow the internal-validator tests: include the implementation to reach its
// static helper, without adding a production symbol or public header.
#include "../../src/lib/expand.c"
#include <stddef.h>

// Layout census, independent of the production declaration. The source-field
// inventory test additionally catches fields added inside union/padding space.
typedef struct {
  NodeKind kind;
  uint32_t source_id;
  const OriginBinding *origin_bindings;
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

int main(void) {
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
