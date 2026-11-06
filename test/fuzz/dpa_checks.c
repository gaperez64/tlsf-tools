#include "check.h"
#include "dpa_checks.h"
#include <stdlib.h>
#include <string.h>

bool fuzz_dpa_reason(TlsfDpaStatus status, bool host_limit) {
  if (status.code == TLSF_DPA_OK)
    return status.reason == TLSF_DPA_NONE;
  return status.code == TLSF_DPA_DECLINED &&
         (status.reason == TLSF_DPA_UNSUPPORTED ||
          status.reason == TLSF_DPA_STATE_LIMIT ||
          (status.reason == TLSF_DPA_HOST_LIMIT && host_limit) ||
          status.reason == TLSF_DPA_BDD_LIMIT ||
          status.reason == TLSF_DPA_PRIORITY_LIMIT);
}

static void alphabet(FuzzDpaChecks *c) {
  uint32_t count = c->spec->n_inputs + c->spec->n_outputs;
  // C1: The copied partition includes unused APs, inputs before outputs.
  CHECK(C1, tlsf_dpa_ap_count(c->dpa) == count && count <= 8);
  for (uint32_t i = 0; i < count; ++i) {
    const char *expected = i < c->spec->n_inputs
                               ? c->spec->inputs[i]
                               : c->spec->outputs[i - c->spec->n_inputs];
    const char *name = tlsf_dpa_ap_name(c->dpa, i);
    // C2: Each copied name and each previously borrowed name stays readable.
    CHECK(C2, name && !strcmp(name, expected) &&
                  (!c->names[i] || !strcmp(c->names[i], expected)));
    c->names[i] = name;
  }
}

void fuzz_dpa_checks_init(FuzzDpaChecks *c, TlsfDpa *dpa,
                          const TlsfConversionResult *spec, size_t max_states) {
  *c = (FuzzDpaChecks){.dpa = dpa, .spec = spec, .max_states = max_states};
  alphabet(c);
}

bool fuzz_dpa_label(FuzzDpaChecks *c, TlsfDpaLabel id) {
  const TlsfDpaLabelNode *node = tlsf_dpa_label_node(c->dpa, id);
  // C3: Every borrowed label, including a row's root, must resolve.
  CHECK(C3, node);
  if (id >= c->label_capacity) {
    size_t capacity = c->label_capacity ? c->label_capacity : 16;
    while (capacity <= id)
      capacity *= 2;
    FuzzLabel *labels = realloc(c->labels, capacity * sizeof *labels);
    if (!labels)
      return false; // Harness storage exhaustion ends inspection.
    memset(labels + c->label_capacity, 0,
           (capacity - c->label_capacity) * sizeof *labels);
    c->labels = labels;
    c->label_capacity = capacity;
  }
  if (!c->labels[id].borrowed) {
    c->labels[id].borrowed = node;
    c->labels[id].copy = *node;
  }
  return true;
}

static void borrowed(FuzzDpaChecks *c) {
  alphabet(c);
  for (size_t r = 0; r < c->row_count; ++r)
    for (size_t e = 0; e < c->rows[r].count; ++e) {
      const TlsfDpaEdge *old = &c->rows[r].copy[e];
      const TlsfDpaEdge *now = &c->rows[r].borrowed[e];
      // C4: Previously borrowed whole rows remain inspectable until free.
      CHECK(C4, now->label == old->label && now->successor == old->successor &&
                    now->priority == old->priority);
    }
  for (size_t i = 0; i < c->label_capacity; ++i) {
    const FuzzLabel *label = &c->labels[i];
    if (!label->borrowed)
      continue;
    const TlsfDpaLabelNode *now = label->borrowed, *old = &label->copy;
    // C5: Borrowed label nodes and their IDs survive later work, even decline.
    CHECK(C5, tlsf_dpa_label_node(c->dpa, (TlsfDpaLabel)i) == now &&
                  now->kind == old->kind && now->ap == old->ap &&
                  now->low == old->low && now->high == old->high);
  }
}

void fuzz_dpa_post(FuzzDpaChecks *c, TlsfDpaStatus status, TlsfDpaState state,
                   const TlsfDpaEdge *edges, size_t count) {
  // C6: Every successor request, including a decline, respects max_states.
  CHECK(C6, tlsf_dpa_state_count(c->dpa) <= c->max_states);
  borrowed(c);
  if (status.code != TLSF_DPA_OK) {
    TlsfDpaStatus saved = tlsf_dpa_status(c->dpa);
    // C7: Failed expansion permanently declines the context (dpa.h:109).
    CHECK(C7, saved.code == status.code && saved.reason == status.reason);
    const TlsfDpaEdge *again = (const TlsfDpaEdge *)(uintptr_t)1;
    size_t n = SIZE_MAX;
    saved = tlsf_dpa_successors(c->dpa, state, &again, &n);
    // C8: Later work returns the same nonconclusive status and no partial row.
    CHECK(C8, saved.code == status.code && saved.reason == status.reason &&
                  !again && !n &&
                  tlsf_dpa_state_count(c->dpa) <= c->max_states);
    borrowed(c);
    return;
  }
  if (c->row_count == sizeof c->rows / sizeof *c->rows)
    return;
  TlsfDpaEdge *copy = malloc(count * sizeof *copy);
  if (!copy)
    return;
  memcpy(copy, edges, count * sizeof *copy);
  c->rows[c->row_count++] = (FuzzRow){edges, copy, count};
  for (size_t e = 0; e < count; ++e)
    if (!fuzz_dpa_label(c, edges[e].label))
      return;
}

void fuzz_dpa_checks_free(FuzzDpaChecks *c) {
  for (size_t r = 0; r < c->row_count; ++r)
    free(c->rows[r].copy);
  free(c->labels);
}
