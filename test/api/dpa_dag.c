#include <tlsf/dpa.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#define NIL UINT32_MAX
#define ATOM(i) {TLSF_AST_AP, NIL, NIL, i}
#define UNARY(k, a) {k, a, NIL, NIL}
#define BINARY(k, a, b) {k, a, b, NIL}
static const char *const inputs[] = {"A", "unused"};
static const char *const outputs[] = {"B"};
static TlsfDpaStatus create(const TlsfDpaFormulaNode *nodes, uint32_t count,
                            uint32_t root, TlsfDpaKind kind,
                            const TlsfDpaBudget *budget, TlsfDpa **out) {
  return tlsf_dpa_create_from_dag(nodes, count, root, inputs, 2, outputs, 1,
                                  kind, budget, out);
}
static bool label(TlsfDpa *c, TlsfDpaLabel id, unsigned valuation) {
  const TlsfDpaLabelNode *n = tlsf_dpa_label_node(c, id);
  assert(n);
  if (n->kind != TLSF_DPA_DECISION)
    return n->kind == TLSF_DPA_TRUE;
  return label(c, valuation & (1u << n->ap) ? n->high : n->low, valuation);
}
static bool repeats(TlsfDpa *c, const unsigned *word, size_t length) {
  size_t bound = tlsf_dpa_state_count(c) * length;
  size_t *seen = calloc(bound, sizeof *seen);
  uint32_t *priorities = calloc(bound, sizeof *priorities);
  assert(seen && priorities);
  uint32_t state = tlsf_dpa_initial(c);
  size_t step = 0, start;
  for (;;) {
    size_t key = state * length + step % length;
    if (seen[key]) {
      start = seen[key] - 1;
      break;
    }
    seen[key] = step + 1;
    const TlsfDpaEdge *edges;
    size_t count;
    assert(tlsf_dpa_successors(c, state, &edges, &count).code == TLSF_DPA_OK);
    size_t matches = 0;
    for (size_t i = 0; i < count; ++i)
      if (label(c, edges[i].label, word[step % length])) {
        state = edges[i].successor;
        priorities[step] = edges[i].priority;
        ++matches;
      }
    assert(matches == 1);
    ++step;
  }
  uint32_t maximum = 0;
  for (size_t i = start; i < step; ++i)
    if (priorities[i] > maximum)
      maximum = priorities[i];
  free(seen);
  free(priorities);
  return maximum & 1u;
}
static int polls, cancel_at;
static int cancelled(void *unused) {
  (void)unused;
  return ++polls == cancel_at;
}
static int cancel_published(void *pointer) {
  return *(TlsfDpa **)pointer != nullptr;
}
static size_t creation_floor(const TlsfDpaFormulaNode *nodes, uint32_t count,
                             uint32_t root) {
  size_t low = 1, high = 4u << 20;
  while (low < high) {
    size_t middle = low + (high - low) / 2;
    TlsfDpaBudget budget = {.max_host_bytes = middle};
    TlsfDpa *c;
    TlsfDpaStatus status =
        create(nodes, count, root, TLSF_DPA_PARITY, &budget, &c);
    tlsf_dpa_free(c);
    if (status.code == TLSF_DPA_OK)
      high = middle;
    else {
      assert(status.reason == TLSF_DPA_HOST_LIMIT);
      low = middle + 1;
    }
  }
  return low;
}
static void scratch_budget(void) {
  const uint32_t used = 65, count = 4096;
  TlsfDpaFormulaNode *nodes = malloc(count * sizeof *nodes);
  assert(nodes);
  nodes[0] = (TlsfDpaFormulaNode)ATOM(0);
  for (uint32_t i = 1; i < used; ++i)
    nodes[i] = (TlsfDpaFormulaNode)UNARY(TLSF_AST_X, i - 1);
  for (uint32_t i = used; i < count; ++i)
    nodes[i] = (TlsfDpaFormulaNode){TLSF_AST_TRUE, NIL, NIL, NIL};
  size_t small = creation_floor(nodes, used, used - 1);
  size_t padded = creation_floor(nodes, count, used - 1);
  assert(padded >
         small + 32768); // Unreachable valid records still consume scratch.
  TlsfDpa *c;
  TlsfDpaBudget budget = {.max_host_bytes = small};
  assert(create(nodes, used, used - 1, TLSF_DPA_PARITY, &budget, &c).code ==
         TLSF_DPA_OK);
  assert(tlsf_dpa_expand(c).reason == TLSF_DPA_HOST_LIMIT);
  tlsf_dpa_free(c);
  budget.max_host_bytes = padded;
  assert(create(nodes, count, used - 1, TLSF_DPA_PARITY, &budget, &c).code ==
         TLSF_DPA_OK);
  // Expansion needs more than the constructor's reduced allowance. Releasing
  // scratch must restore the original ceiling before the first successor.
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  tlsf_dpa_free(c);
  free(nodes);
}

static void invalid(const TlsfDpaFormulaNode *nodes, uint32_t count,
                    uint32_t root) {
  TlsfDpa *c = (void *)1;
  assert(create(nodes, count, root, TLSF_DPA_PARITY, nullptr, &c).code ==
         TLSF_DPA_INVALID);
  assert(!c);
}

// FormulaDag.Node.valid relies on every branch of these record checks.
// Mutate unreachable records too: validation is independent of root traversal.
static void record_contract(void) {
  static const unsigned arities[] = {0, 0, 0, 1, 2, 2, 2, 2,
                                     1, 0, 1, 1, 2, 2, 2, 2};
  for (unsigned kind = 0; kind < TLSF_AST_KIND_COUNT; ++kind) {
    TlsfDpaFormulaNode nodes[] = {
        {TLSF_AST_TRUE, NIL, NIL, NIL}, ATOM(0), {kind, NIL, NIL, NIL}};
    unsigned arity = arities[kind];
    if (arity)
      nodes[2].left = 1;
    if (arity == 2)
      nodes[2].right = 1; // Shared child is legal for every binary operator.
    if (kind == TLSF_AST_AP)
      nodes[2].ap = 2;
    if (kind == TLSF_AST_X_STRONG) {
      invalid(nodes, 3, 0);
      continue;
    }
    TlsfDpa *c;
    assert(create(nodes, 3, 2, TLSF_DPA_PARITY, nullptr, &c).code ==
           TLSF_DPA_OK);
    tlsf_dpa_free(c);
    TlsfDpaFormulaNode valid = nodes[2];
    nodes[2].left = arity ? 2 : 0; // Self reference or extra nullary child.
    invalid(nodes, 3, 0);
    nodes[2].left = arity ? NIL : 1;
    invalid(nodes, 3, 0);
    nodes[2] = valid;
    nodes[2].right = arity == 2 ? 2 : 0;
    invalid(nodes, 3, 0);
    nodes[2].right = arity == 2 ? NIL : 1;
    invalid(nodes, 3, 0);
    nodes[2] = valid;
    nodes[2].ap = kind == TLSF_AST_AP ? 3 : 0;
    invalid(nodes, 3, 0);
    nodes[2].ap = kind == TLSF_AST_AP ? NIL : 1;
    invalid(nodes, 3, 0);
  }
  TlsfDpaFormulaNode nodes[] = {{TLSF_AST_TRUE, NIL, NIL, NIL},
                                {TLSF_AST_FALSE, NIL, NIL, NIL}};
  TlsfDpa *c;
  for (uint32_t root = 0; root < 2; ++root) {
    assert(create(nodes, 2, root, TLSF_DPA_PARITY, nullptr, &c).code ==
           TLSF_DPA_OK);
    assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
    const unsigned word[] = {0};
    assert(repeats(c, word, 1) == (root == 0));
    tlsf_dpa_free(c);
  }
  nodes[1].kind = TLSF_AST_KIND_COUNT;
  invalid(nodes, 2, 0);
  nodes[1].kind = (TlsfAstKind)-1;
  invalid(nodes, 2, 0);
  nodes[1] = (TlsfDpaFormulaNode)UNARY(TLSF_AST_X, 2); // Forward child.
  invalid(nodes, 2, 0);
  invalid(nullptr, 1, 0);
  invalid(nodes, 0, 0);
  invalid(nodes, 2, 2);
  assert(create(nodes, 2, 0, TLSF_DPA_PARITY, nullptr, nullptr).code ==
         TLSF_DPA_INVALID);
}

static void declaration_contract(void) {
  const TlsfDpaFormulaNode truth = {TLSF_AST_TRUE, NIL, NIL, NIL};
  const char *bad[][2] = {{nullptr, "unused"}, {"", "unused"}, {"A", "A"},
                          {"A", "B"},          {"A", nullptr}, {"A", ""}};
  for (TlsfDpaKind kind = TLSF_DPA_PARITY; kind <= TLSF_DPA_BUCHI; ++kind) {
    TlsfDpa *c;
    for (size_t i = 0; i < sizeof bad / sizeof *bad; ++i) {
      c = (void *)1;
      assert(tlsf_dpa_create_from_dag(&truth, 1, 0, bad[i], 2, outputs, 1, kind,
                                      nullptr, &c)
                 .code == TLSF_DPA_INVALID);
      assert(!c); // Even unused declarations must be nonempty and distinct.
    }
    assert(tlsf_dpa_create_from_dag(&truth, 1, 0, nullptr, 1, outputs, 1, kind,
                                    nullptr, &c)
                   .code == TLSF_DPA_INVALID &&
           !c);
    assert(tlsf_dpa_create_from_dag(&truth, 1, 0, inputs, 2, nullptr, 1, kind,
                                    nullptr, &c)
                   .code == TLSF_DPA_INVALID &&
           !c);
    assert(tlsf_dpa_create_from_dag(&truth, 1, 0, inputs, UINT32_MAX, outputs,
                                    1, kind, nullptr, &c)
                   .code == TLSF_DPA_INVALID &&
           !c);
    assert(tlsf_dpa_create_from_dag(&truth, 1, 0, nullptr, 0, nullptr, 0, kind,
                                    nullptr, &c)
               .code == TLSF_DPA_OK);
    tlsf_dpa_free(c);
    TlsfDpaFormulaNode atom = ATOM(0);
    assert(tlsf_dpa_create_from_dag(&atom, 1, 0, nullptr, 0, nullptr, 0, kind,
                                    nullptr, &c)
                   .code == TLSF_DPA_INVALID &&
           !c);
  }
  TlsfDpa *c = (void *)1;
  assert(create(&truth, 1, 0, (TlsfDpaKind)2, nullptr, &c).code ==
             TLSF_DPA_INVALID &&
         !c);
}
int main(void) {
  record_contract();
  declaration_contract();
  // Shared GF(A) is referenced twice. Input data may disappear before
  // expansion.
  const TlsfDpaFormulaNode formula[] = {ATOM(0), UNARY(TLSF_AST_F, 0),
                                        UNARY(TLSF_AST_G, 1),
                                        BINARY(TLSF_AST_AND, 2, 2)};
  for (TlsfDpaKind kind = TLSF_DPA_PARITY; kind <= TLSF_DPA_BUCHI; ++kind) {
    TlsfDpaFormulaNode *copy = malloc(sizeof formula);
    memcpy(copy, formula, sizeof formula);
    char name[] = "A";
    const char *names[] = {name, "unused"};
    TlsfDpa *c = nullptr;
    assert(tlsf_dpa_create_from_dag(copy, 4, 3, names, 2, outputs, 1, kind,
                                    nullptr, &c)
               .code == TLSF_DPA_OK);
    memset(copy, 0xff, sizeof formula);
    free(copy);
    name[0] = 'z';
    assert(!strcmp(tlsf_dpa_ap_name(c, 0), "A"));
    assert(!strcmp(tlsf_dpa_ap_name(c, 1), "unused"));
    assert(!strcmp(tlsf_dpa_ap_name(c, 2), "B"));
    assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
    const unsigned yes[] = {0, 1}, no[] = {0, 4};
    assert(repeats(c, yes, 2) && !repeats(c, no, 2));
    tlsf_dpa_free(c);
  }
  TlsfDpa *c = (void *)1;
  TlsfDpaBudget budget = {.max_host_bytes = 128};
  assert(create(formula, 4, 3, TLSF_DPA_PARITY, &budget, &c).reason ==
             TLSF_DPA_HOST_LIMIT &&
         !c);
  budget = (TlsfDpaBudget){.deadline_mono_ns = 1};
  assert(create(formula, 4, 3, TLSF_DPA_PARITY, &budget, &c).reason ==
             TLSF_DPA_DEADLINE &&
         !c);
  budget = (TlsfDpaBudget){.cancelled = cancelled};
  for (cancel_at = 1; cancel_at <= 60; ++cancel_at) {
    polls = 0;
    TlsfDpaStatus status = create(formula, 4, 3, TLSF_DPA_PARITY, &budget, &c);
    assert(status.reason == TLSF_DPA_CANCELLED && !c);
  }
  const TlsfDpaFormulaNode sigma[] = {ATOM(0), UNARY(TLSF_AST_G, 0),
                                      UNARY(TLSF_AST_F, 1)};
  assert(create(sigma, 3, 2, TLSF_DPA_BUCHI, nullptr, &c).reason ==
             TLSF_DPA_UNSUPPORTED &&
         !c);
  budget = (TlsfDpaBudget){.cancelled = cancel_published, .cancel_ctx = &c};
  c = nullptr;
  assert(create(formula, 4, 3, TLSF_DPA_PARITY, &budget, &c).reason ==
             TLSF_DPA_CANCELLED &&
         !c);
  scratch_budget();
  return 0;
}
