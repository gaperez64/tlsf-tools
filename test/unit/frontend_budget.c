#define _GNU_SOURCE
// Exercise allocation-free stages directly, as well as the shared pipeline.
#include "../../src/lib/expand.c"
#include "../../src/lib/provenance.c"
#include <stdlib.h>

typedef struct {
  unsigned polls, allocations;
  unsigned stop, stop_allocations;
  size_t max_allocation;
  Arena *arena;
  size_t stop_used;
} Stop;

static int stop_budget(void *raw, size_t bytes) {
  Stop *stop = raw;
  if (bytes) {
    ++stop->allocations;
    return stop->allocations == stop->stop_allocations ||
           (stop->max_allocation && bytes > stop->max_allocation);
  }
  ++stop->polls;
  return (stop->arena && stop->arena->head->used >= stop->stop_used) ||
         stop->polls == stop->stop;
}

static TlsfSpec *parse(const char *bytes) {
  FILE *in = fmemopen((void *)bytes, strlen(bytes), "r");
  assert(in);
  TlsfSpec *spec = spec_parse(in, "frontend-budget");
  fclose(in);
  assert(spec);
  return spec;
}

static const char *bus_source =
    "INFO { SEMANTICS: Mealy TARGET: Mealy } "
    "GLOBAL { PARAMETERS { n = 9; } DEFINITIONS { "
    " width(x) = x == 7 : 50000 otherwise : 1; } } "
    "MAIN { INPUTS { aux[width(n)]; } OUTPUTS { o; } "
    "GUARANTEES { G F o; } }";

static void comparisons(void) {
  Arena *a = arena_new(1 << 20);
  assert(a);
  EvalValue *items = ARENA_ALLOC_N(a, EvalValue, 8192);
  assert(items);
  for (unsigned i = 0; i < 8192; i++)
    items[i] = (EvalValue){.kind = EVAL_VALUE_INT, .integer = i};
  EvalSet set = {.items = items, .count = 8192, .capacity = 8192};
  EvalValue absent = {.kind = EVAL_VALUE_INT, .integer = -1};
  size_t used = a->head->used;
  Stop stop = {.stop = 2};
  arena_set_budget(a, stop_budget, &stop);
  // This is the inner scan shared by disjoint intersection and difference.
  assert(set_contains(a, &set, &absent) == -1);
  assert(stop.polls == 2 && stop.allocations == 0 && a->head->used == used);
  arena_free(a);

  a = arena_new(4096);
  assert(a);
  EvalSet inner = {0};
  // Rebuild after freeing the first arena, then compare equal nested sets.
  EvalValue ints[128];
  for (unsigned i = 0; i < 128; i++)
    ints[i] = (EvalValue){.kind = EVAL_VALUE_INT, .integer = i};
  inner.items = ints;
  inner.count = 128;
  EvalValue nested = {.kind = EVAL_VALUE_SET, .set = &inner};
  EvalSet outer = {.items = &nested, .count = 1};
  EvalValue value = {.kind = EVAL_VALUE_SET, .set = &outer};
  stop = (Stop){.stop = 2};
  arena_set_budget(a, stop_budget, &stop);
  assert(value_equal(a, &value, &value) == -1);
  assert(stop.polls == 2 && stop.allocations == 0);
  arena_free(a);

  a = arena_new(4096);
  Node lhs[16] = {{.kind = NODE_TRUE}}, rhs[16] = {{.kind = NODE_TRUE}};
  for (unsigned i = 1; i < 16; i++) {
    lhs[i] = (Node){.kind = NODE_AND, .lhs = &lhs[i - 1], .rhs = &lhs[i - 1]};
    rhs[i] = (Node){.kind = NODE_AND, .lhs = &rhs[i - 1], .rhs = &rhs[i - 1]};
  }
  EvalValue lv = {.kind = EVAL_VALUE_NODE, .node = &lhs[15]};
  EvalValue rv = {.kind = EVAL_VALUE_NODE, .node = &rhs[15]};
  stop = (Stop){.stop = 2};
  arena_set_budget(a, stop_budget, &stop);
  assert(value_equal(a, &lv, &rv) == -1);
  assert(stop.polls == 2 && stop.allocations == 0);
  arena_free(a);
}

static void substitution_search(void) {
  Arena *arena = arena_new(ARENA_DEFAULT_SLAB_SIZE);
  SubstCopy *copies = ARENA_ALLOC_N(arena, SubstCopy, 8192);
  assert(copies);
  Node source = {.kind = NODE_TRUE}, other = {.kind = NODE_FALSE};
  for (unsigned i = 0; i < 8192; i++) {
    copies[i].source = &other;
    copies[i].next = i == 8191 ? nullptr : &copies[i + 1];
  }
  Env env = {.copies = &copies};
  copies[8191].source = &source;
  assert(subst_source(arena, &source, &env) == &copies[8191].node);
  Stop stop = {.stop = 2};
  arena_set_budget(arena, stop_budget, &stop);
  assert(!subst(arena, &source, nullptr, nullptr, 0, &env));
  assert(stop.polls == 2 && stop.allocations == 0 && arena->failed);
  arena_free(arena);
}

static void set_operations(void) {
  const char *source =
      "INFO { SEMANTICS: Mealy TARGET: Mealy } "
      "MAIN { OUTPUTS { o; } GUARANTEES { "
      "&&[j IN ({0,1 .. 1023} CAP {1024,1025 .. 2047})] o; } }";
  for (NodeKind kind = NODE_SET_INTER; kind <= NODE_SET_DIFF; kind++) {
    TlsfSpec *spec = parse(source);
    Node *operation = spec->guarantee.formulas[0]->qset;
    operation->kind = kind;
    SubstCopy *copies = nullptr;
    Env env = {.copies = &copies};
    EvalSet *left, *right;
    assert(eval_set(spec, operation->lhs, &env, &left, 0));
    assert(eval_set(spec, operation->rhs, &env, &right, 0));
    assert(left->count == 1024 && right->count == 1024);
    // The operation allocates just its empty result after both operands.
    size_t used = spec->arena->head->used;
    size_t scan_at = (used + _Alignof(EvalSet) - 1) & ~(_Alignof(EvalSet) - 1u);
    scan_at += sizeof(EvalSet);
    spec_free(spec);

    spec = parse(source);
    operation = spec->guarantee.formulas[0]->qset;
    operation->kind = kind;
    copies = nullptr;
    Stop stop = {.arena = spec->arena, .stop_used = scan_at};
    arena_set_budget(spec->arena, stop_budget, &stop);
    EvalSet *result = nullptr;
    assert(!eval_set(spec, operation, &env, &result, 0));
    assert(!result && stop.polls && !stop.allocations);
    assert(spec->arena->head->used >= scan_at);
    if (kind == NODE_SET_INTER)
      assert(spec->arena->head->used == scan_at);
    spec_free(spec);
  }
}

static void provenance_stages(void) {
  const char hash[65] = "test";
  // Only the newly selected seed is wide. Expansion finishes before the
  // budget is attached, so cancellation must come from the duplicate scan.
  TlsfSpec *spec = parse(bus_source);
  ParamOverride seed = {"n", 7};
  assert(expand(spec, &seed, 1) == 0 && spec->input_count == 50000);
  Stop stop = {.stop = 2};
  arena_set_budget(spec->arena, stop_budget, &stop);
  FILE *out = fopen("/dev/null", "w");
  assert(out);
  assert(provenance_write(out, spec, nullptr, 0, nullptr, 0, hash) != 0);
  assert(stop.polls == 2 && stop.allocations == 0);
  spec_free(spec);

  spec = parse(bus_source);
  assert(expand(spec, nullptr, 0) == 0 && spec->input_count == 1);
  stop = (Stop){.max_allocation = 1};
  arena_set_budget(spec->arena, stop_budget, &stop);
  assert(provenance_write(out, spec, nullptr, 0, nullptr, 0, hash) != 0);
  assert(stop.allocations && arena_failed(spec->arena));
  spec_free(spec);

  // Empty JSON containers make serialization grow with no JSON allocations.
  Arena *a = arena_new(4096);
  JsonBuilder builder = jb_new();
  yyjson_mut_val *array = jb_arr(&builder);
  for (unsigned i = 0; i < 8192; i++)
    jb_push(&builder, array, jb_arr(&builder));
  assert(!builder.failed);
  stop = (Stop){.stop = 2};
  arena_set_budget(a, stop_budget, &stop);
  yyjson_alc allocator = {.malloc = provenance_malloc,
                          .realloc = provenance_realloc,
                          .free = provenance_free,
                          .ctx = a};
  assert(!provenance_json(out, array, &allocator));
  assert(stop.polls == 2 && stop.allocations == 0);
  yyjson_mut_doc_free(builder.doc);
  arena_free(a);
  fclose(out);
}

static void strings_and_printing(void) {
  char data[20000];
  for (unsigned i = 0; i < sizeof data; i++)
    data[i] = i % 200 ? 'x' : '\n';
  data[102] = '"';
  data[103] = '\\';
  data[8191] = (char)0xc3;
  data[8192] = (char)0xa9;
  data[10001] = '\0';
  JsonBuilder builder = jb_new();
  yyjson_mut_val *string = yyjson_mut_strn(builder.doc, data, sizeof data);
  size_t expected_size = 0;
  char *expected = yyjson_mut_val_write(string, 0, &expected_size);
  assert(expected);
  Arena *a = arena_new(4096);
  Stop stop = {0};
  arena_set_budget(a, stop_budget, &stop);
  yyjson_alc allocator = {.malloc = provenance_malloc,
                          .realloc = provenance_realloc,
                          .free = provenance_free,
                          .ctx = a};
  char *actual = nullptr;
  size_t actual_size = 0;
  FILE *out = frontend_memstream(a, &actual, &actual_size);
  assert(out && provenance_json(out, string, &allocator));
  assert(fclose(out) == 0 && actual_size == expected_size);
  assert(!memcmp(actual, expected, actual_size));
  free(actual);
  free(expected);

  out = fopen("/dev/null", "w");
  assert(out);
  stop = (Stop){.stop_allocations = 3};
  arena_set_budget(a, stop_budget, &stop);
  assert(!provenance_json(out, string, &allocator));
  assert(stop.allocations == 3 && a->failed);
  yyjson_mut_doc_free(builder.doc);
  arena_free(a);

  a = arena_new(4096);
  Node nodes[16] = {{.kind = NODE_TRUE}};
  for (unsigned i = 1; i < 16; i++)
    nodes[i] =
        (Node){.kind = NODE_OR, .lhs = &nodes[i - 1], .rhs = &nodes[i - 1]};
  stop = (Stop){.stop = 2};
  arena_set_budget(a, stop_budget, &stop);
  print_tlsf_formula_checked(out, &nodes[15], a);
  assert(stop.polls == 2 && !stop.allocations && a->failed);
  arena_free(a);
  fclose(out);
}

static void temporary_storage(void) {
  TlsfSpec *spec = parse(bus_source);
  Stop stop = {.max_allocation = 4096};
  arena_set_budget(spec->arena, stop_budget, &stop);
  assert(!expand_check(spec));
  assert(stop.allocations == 1 && arena_failed(spec->arena));
  spec_free(spec);

  Arena *a = arena_new(4096);
  stop = (Stop){.max_allocation = 16384};
  arena_set_budget(a, stop_budget, &stop);
  char *bytes = nullptr;
  size_t size = 0;
  FILE *out = frontend_memstream(a, &bytes, &size);
  assert(out);
  for (unsigned i = 0; i < 100000 && !ferror(out); i++)
    fputs("test", out);
  assert(fclose(out) != 0 && arena_failed(a) && !bytes);
  arena_free(a);
}

static void generated_trees(void) {
  for (const char **formula =
           (const char *[]){"X[3000] o", "&&[0 <= j < 3000] o",
                            "G[3000:3000] o", "(X[3000] o) IN {X[3000] o}",
                            "pick", nullptr};
       *formula; formula++) {
    char source[512];
    snprintf(source, sizeof source,
             "INFO { SEMANTICS: Mealy TARGET: Mealy } "
             "GLOBAL { DEFINITIONS { pick = X[3000] o ~ X p : true "
             "otherwise : false; } } "
             "MAIN { OUTPUTS { o; } GUARANTEES { %s; } }",
             *formula);
    for (unsigned budgeted = 0; budgeted < 2; budgeted++)
      for (unsigned capped = 0; capped < 2; capped++) {
        TlsfSpec *spec = parse(source);
        spec->capture_provenance = true;
        spec->limit_generated_depth = capped;
        Stop stop = {0};
        if (budgeted)
          arena_set_budget(spec->arena, stop_budget, &stop);
        if (budgeted && capped)
          assert(expand(spec, nullptr, 0) != 0 && arena_failed(spec->arena));
        else
          assert(expand(spec, nullptr, 0) == 0 && !arena_failed(spec->arena));
        spec_free(spec);
      }
  }
}

int main(void) {
  comparisons();
  substitution_search();
  set_operations();
  provenance_stages();
  strings_and_printing();
  temporary_storage();
  generated_trees();
  return 0;
}
