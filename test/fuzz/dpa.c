#define _POSIX_C_SOURCE 200809L
#include "check.h"
#include "decode.h"
#include "dpa_checks.h"
#include "tlsf/convert.h"
#include "tlsf/dpa.h"
#include "tlsf/print_tlsf.h"

#include <stdlib.h>
#include <string.h>

static bool ok(TlsfDpaStatus status) {
  // D1: Only documented reasons for these budgets may decline valid LTL.
  CHECK(D1, fuzz_dpa_reason(status, true));
  return status.code == TLSF_DPA_OK;
}

/* No ordering is promised for label IDs. Three colors detect cycles and
 * memoize shared children; each node is validated once per context. */
static bool label_valid(FuzzDpaChecks *c, TlsfDpaLabel label, uint32_t aps,
                        size_t depth) {
  const TlsfDpaLabelNode *node = tlsf_dpa_label_node(c->dpa, label);
  // D3: Every exposed label and child must name a Boolean/decision node.
  CHECK(D3,
        node && (node->kind == TLSF_DPA_FALSE || node->kind == TLSF_DPA_TRUE ||
                 node->kind == TLSF_DPA_DECISION));
  if (!fuzz_dpa_label(c, label))
    return false;
  // D2: A visiting node cannot be its own descendant in a label DAG.
  CHECK(D2, c->labels[label].visit != 1);
  if (c->labels[label].visit == 2)
    return true;
  if (depth == 256)
    return false;
  c->labels[label].visit = 1;
  if (node->kind == TLSF_DPA_DECISION) {
    // D4: Decisions address the copied input-then-output alphabet (dpa.h:62).
    CHECK(D4, node->ap < aps);
    if (!label_valid(c, node->low, aps, depth + 1) ||
        !label_valid(c, node->high, aps, depth + 1))
      return false;
  }
  c->labels[label].visit = 2;
  return true;
}

/* Memoize values too: every label is evaluated at most once per assignment. */
static bool holds(FuzzDpaChecks *c, TlsfDpaLabel label, unsigned letter) {
  FuzzLabel *entry = &c->labels[label];
  if (entry->assignment != c->assignment) {
    const TlsfDpaLabelNode *node = entry->borrowed;
    bool value =
        node->kind == TLSF_DPA_DECISION
            ? holds(c, letter & (1u << node->ap) ? node->high : node->low,
                    letter)
            : node->kind == TLSF_DPA_TRUE;
    entry->value = value ? 2 : 1;
    entry->assignment = c->assignment;
  }
  return entry->value == 2;
}

static void inspect(TlsfDpa *dpa, const TlsfConversionResult *spec,
                    const TlsfDpaBudget *budget) {
  FuzzDpaChecks checks;
  fuzz_dpa_checks_init(&checks, dpa, spec, budget->max_states);
  uint32_t aps = tlsf_dpa_ap_count(dpa);
  TlsfDpaState queue[64] = {tlsf_dpa_initial(dpa)};
  size_t count = 1;
  for (size_t at = 0; at < count; ++at) {
    const TlsfDpaEdge *edges = (const TlsfDpaEdge *)(uintptr_t)1;
    size_t n = SIZE_MAX;
    TlsfDpaStatus status = tlsf_dpa_successors(dpa, queue[at], &edges, &n);
    bool success = ok(status);
    if (!success) {
      // D6: Declined expansion must publish no partial row (dpa.h:107-110).
      CHECK(D6, !edges && !n);
      fuzz_dpa_post(&checks, status, queue[at], edges, n);
      break;
    }
    // D7: Successful successor requests return a nonempty whole row.
    CHECK(D7, edges && n);
    fuzz_dpa_post(&checks, status, queue[at], edges, n);
    for (size_t e = 0; e < n; ++e) {
      if (!label_valid(&checks, edges[e].label, aps, 0))
        goto done;
      // D8: Edge priorities cannot exceed the advertised global maximum.
      CHECK(D8, edges[e].priority <= tlsf_dpa_max_priority(dpa));
      // D9: Successor IDs must index discovered states, never a missing state.
      CHECK(D9, edges[e].successor < tlsf_dpa_state_count(dpa));
      size_t i = 0;
      while (i < count && queue[i] != edges[e].successor)
        ++i;
      if (i == count)
        queue[count++] = edges[e].successor;
    }
    for (unsigned letter = 0; letter < (1u << aps); ++letter) {
      ++checks.assignment; // At most 64 rows * 256 letters per context.
      size_t matches = 0;
      for (size_t e = 0; e < n; ++e)
        matches += holds(&checks, edges[e].label, letter);
      // D10: Disjoint labels covering true match every letter exactly once.
      CHECK(D10, matches == 1);
    }
  }
done:
  fuzz_dpa_checks_free(&checks);
}

/* There is no library AST->neutral-DAG exporter. A postorder tree is also a
 * valid DAG; capacity/depth exhaustion is a harness resource limit. */
static uint32_t dag_node(const TlsfAstNode *node,
                         const TlsfConversionResult *spec,
                         TlsfDpaFormulaNode nodes[4096], uint32_t *count,
                         unsigned depth) {
  if (depth == 256 || *count == 4096)
    return UINT32_MAX;
  TlsfDpaFormulaNode record = {tlsf_ast_node_kind(node), UINT32_MAX, UINT32_MAX,
                               UINT32_MAX};
  uint32_t children = tlsf_ast_node_child_count(node);
  if (children) {
    record.left =
        dag_node(tlsf_ast_node_child(node, 0), spec, nodes, count, depth + 1);
    if (record.left == UINT32_MAX)
      return UINT32_MAX;
  }
  if (children == 2) {
    record.right =
        dag_node(tlsf_ast_node_child(node, 1), spec, nodes, count, depth + 1);
    if (record.right == UINT32_MAX)
      return UINT32_MAX;
  }
  if (record.kind == TLSF_AST_AP) {
    const char *name = tlsf_ast_node_ap_name(node);
    for (uint32_t i = 0; i < spec->n_inputs + spec->n_outputs; ++i) {
      const char *candidate = i < spec->n_inputs
                                  ? spec->inputs[i]
                                  : spec->outputs[i - spec->n_inputs];
      if (!strcmp(name, candidate)) {
        record.ap = i;
        break;
      }
    }
  }
  if (*count == 4096)
    return UINT32_MAX;
  nodes[*count] = record;
  return (*count)++;
}

static void construct(const TlsfConversionResult *spec,
                      const TlsfDpaBudget *budget, bool from_dag) {
  TlsfDpa *dpa =
      (TlsfDpa *)(uintptr_t)1; // Failure must overwrite the sentinel.
  TlsfDpaStatus status;
  const char *const *inputs = (const char *const *)spec->inputs;
  const char *const *outputs = (const char *const *)spec->outputs;
  if (from_dag) {
    TlsfDpaFormulaNode nodes[4096];
    uint32_t count = 0;
    uint32_t root = dag_node(tlsf_ast_root(spec->ast), spec, nodes, &count, 0);
    if (root == UINT32_MAX)
      return;
    status = tlsf_dpa_create_from_dag(nodes, count, root, inputs,
                                      spec->n_inputs, outputs, spec->n_outputs,
                                      TLSF_DPA_PARITY, budget, &dpa);
  } else {
    status = tlsf_dpa_create(tlsf_ast_root(spec->ast), inputs, spec->n_inputs,
                             outputs, spec->n_outputs, budget, &dpa);
  }
  if (ok(status))
    inspect(dpa, spec, budget);
  else {
    // D11: Both constructors promise NULL output after any failure (dpa.h:66).
    CHECK(D11, !dpa);
  }
  tlsf_dpa_free(dpa);
}

static TlsfSpec *parse(char *text, size_t length) {
  FILE *stream = fmemopen(text, length, "r");
  if (!stream)
    return NULL;
  TlsfSpec *spec = spec_parse(stream, "fuzz-dpa");
  fclose(stream);
  // D12: Decoder and printer text must parse; neither may introduce bad syntax.
  CHECK(D12, spec);
  return spec;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  TlsfDpaBudget budget = {.max_states = 64,
                          .max_host_bytes = 4u << 20,
                          .bdd_nodes = 4096,
                          .bdd_cache = 1024,
                          .allow_unproved = size && (data[0] & 1)};
  char text[TLSF_FUZZ_TEXT_CAPACITY];
  size_t length =
      tlsf_fuzz_decode(size ? data + 1 : data, size ? size - 1 : 0, text);
  TlsfSpec *parsed = parse(text, length);
  if (!parsed)
    return 0;
  size_t printed_size = 0;
  char *printed = NULL;
  FILE *stream = open_memstream(&printed, &printed_size);
  if (!stream) {
    spec_free(parsed);
    return 0;
  }
  print_tlsf(stream, parsed, true);
  spec_free(parsed);
  if (fclose(stream)) {
    free(printed);
    return 0;
  }
  parsed = parse(printed, printed_size);
  if (!parsed) {
    free(printed);
    return 0;
  }
  spec_free(parsed);
  TlsfConversionResult *first = tlsf_convert(text, NULL);
  TlsfConversionResult *second = tlsf_convert(printed, NULL);
  free(printed);
  /* dpa.h:61-76,85-93 guarantee languages and stable IDs within one context,
   * not equal/isomorphic graphs, row order or priorities across constructions.
   * Thus we self-check all three paths but deliberately do not compare their
   * structure, even with BFS renaming. Language equivalence needs an oracle. */
  if (first) {
    construct(first, &budget, false);
    construct(first, &budget, true);
  }
  if (second)
    construct(second, &budget, false);
  tlsf_conversion_result_free(first);
  tlsf_conversion_result_free(second);
  return 0;
}
