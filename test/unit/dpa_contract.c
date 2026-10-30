#include "dpa_internal.h"
#include "tlsf/ast.h"
#include <assert.h>
#include <stdio.h>

static size_t host_count, host_at, bdd_count, bdd_at;
static bool armed, fired;
static int poll_count, cancel_at;
static int cancel_callback(void *unused) {
  (void)unused;
  return ++poll_count == cancel_at;
}
void *__real_oxidd_host_calloc(size_t, size_t);
void *__wrap_oxidd_host_calloc(size_t n, size_t size);
void *__wrap_oxidd_host_calloc(size_t n, size_t size) {
  if (armed && ++host_count == host_at) {
    fired = true;
    return nullptr;
  }
  return __real_oxidd_host_calloc(n, size);
}
Bdd __real_oxidd_bdd_ite(Bdd, Bdd, Bdd);
Bdd __wrap_oxidd_bdd_ite(Bdd, Bdd, Bdd);
Bdd __wrap_oxidd_bdd_ite(Bdd a, Bdd b, Bdd d) {
  if (armed && ++bdd_count == bdd_at) {
    fired = true;
    return (Bdd){0};
  }
  return __real_oxidd_bdd_ite(a, b, d);
}

// All BDD operations newly used by the global acceptance/tree participate.
#define WRAP_BDD1(name)                                                        \
  Bdd __real_##name(Bdd);                                                      \
  Bdd __wrap_##name(Bdd);                                                      \
  Bdd __wrap_##name(Bdd a) {                                                   \
    if (armed && ++bdd_count == bdd_at) {                                      \
      fired = true;                                                            \
      return (Bdd){0};                                                         \
    }                                                                          \
    return __real_##name(a);                                                   \
  }
#define WRAP_BDD2(name)                                                        \
  Bdd __real_##name(Bdd, Bdd);                                                 \
  Bdd __wrap_##name(Bdd, Bdd);                                                 \
  Bdd __wrap_##name(Bdd a, Bdd b) {                                            \
    if (armed && ++bdd_count == bdd_at) {                                      \
      fired = true;                                                            \
      return (Bdd){0};                                                         \
    }                                                                          \
    return __real_##name(a, b);                                                \
  }
WRAP_BDD1(oxidd_bdd_not)
WRAP_BDD1(oxidd_bdd_cofactor_false)
WRAP_BDD1(oxidd_bdd_cofactor_true)
WRAP_BDD2(oxidd_bdd_and)
WRAP_BDD2(oxidd_bdd_or)

static const char *const names[] = {"a", "b"};
static TlsfDpaStatus create(Node *f, const TlsfDpaBudget *budget, TlsfDpa **c) {
  return tlsf_dpa_create((const TlsfAstNode *)f, names, 2, nullptr, 0, budget,
                         c);
}
static void reset(size_t host, size_t bdd) {
  host_count = bdd_count = 0;
  host_at = host;
  bdd_at = bdd;
  fired = false;
  armed = true;
}
static void no_row(TlsfDpa *c, uint32_t id, TlsfDpaReason reason) {
  const TlsfDpaEdge *row = (void *)1;
  size_t count = 17;
  TlsfDpaStatus status = tlsf_dpa_successors(c, id, &row, &count);
  assert(status.code == TLSF_DPA_DECLINED && status.reason == reason);
  assert(!row && !count);
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_DECLINED);
}
static void stability(Node *f) {
  TlsfDpa *c;
  assert(create(f, nullptr, &c).code == TLSF_DPA_OK);
  uint32_t initial = tlsf_dpa_initial(c);
  assert(tlsf_dpa_state_count(c) == 1);
  const TlsfDpaEdge *row, *again;
  size_t count, n;
  assert(tlsf_dpa_successors(c, initial, &row, &count).code == TLSF_DPA_OK);
  TlsfDpaEdge saved = row[0];
  const TlsfDpaLabelNode *label = tlsf_dpa_label_node(c, saved.label);
  TlsfDpaLabelNode description = *label;
  oxidd_bdd_manager_gc(c->manager);
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  assert(c->states.n > 16); // grow the state vector after publishing row
  assert(tlsf_dpa_initial(c) == initial);
  assert(tlsf_dpa_successors(c, initial, &again, &n).code == TLSF_DPA_OK);
  assert(row == again && count == n && !memcmp(&saved, row, sizeof saved));
  assert(label == tlsf_dpa_label_node(c, saved.label));
  assert(!memcmp(label, &description, sizeof description));
  tlsf_dpa_free(c);
}
static void declines(Arena *a, Node *p) {
  Node *f = node_x(a, node_x(a, node_x(a, p)));
  TlsfDpaBudget budget = {.max_states = 2};
  TlsfDpa *c = (void *)1;
  assert(create(f, &budget, &c).code == TLSF_DPA_OK);
  const TlsfDpaEdge *first;
  size_t n;
  assert(tlsf_dpa_successors(c, 0, &first, &n).code == TLSF_DPA_OK && n == 1);
  TlsfDpaEdge saved = first[0];
  no_row(c, first[0].successor, TLSF_DPA_STATE_LIMIT);
  assert(!memcmp(first, &saved, sizeof saved));
  assert(tlsf_dpa_label_node(c, saved.label));
  tlsf_dpa_free(c);
  budget.max_states = 1;
  assert(create(f, &budget, &c).code == TLSF_DPA_OK);
  no_row(c, 0, TLSF_DPA_STATE_LIMIT);
  tlsf_dpa_free(c);

  budget = (TlsfDpaBudget){.cancelled = cancel_callback};
  cancel_at = 17;
  poll_count = 0;
  assert(create(f, &budget, &c).reason == TLSF_DPA_CANCELLED && !c);
  cancel_at = 0;
  poll_count = 0;
  assert(create(f, &budget, &c).code == TLSF_DPA_OK);
  assert(tlsf_dpa_successors(c, 0, &first, &n).code == TLSF_DPA_OK);
  saved = first[0];
  cancel_at = poll_count + 9; // cancellation inside expansion, not on entry
  no_row(c, saved.successor, TLSF_DPA_CANCELLED);
  assert(!memcmp(first, &saved, sizeof saved));
  tlsf_dpa_free(c);

  volatile bool cancel = true;
  budget = (TlsfDpaBudget){.cancel = &cancel};
  assert(create(f, &budget, &c).reason == TLSF_DPA_CANCELLED && !c);
  cancel = false;
  assert(create(f, &budget, &c).code == TLSF_DPA_OK);
  assert(tlsf_dpa_successors(c, 0, &first, &n).code == TLSF_DPA_OK);
  saved = first[0];
  cancel = true;
  no_row(c, saved.successor, TLSF_DPA_CANCELLED);
  assert(!memcmp(first, &saved, sizeof saved));
  cancel = false;
  no_row(c, 0, TLSF_DPA_CANCELLED); // permanent even if flag is cleared
  tlsf_dpa_free(c);

  budget = (TlsfDpaBudget){.deadline_mono_ns = 1};
  assert(create(f, &budget, &c).reason == TLSF_DPA_DEADLINE && !c);
  budget = (TlsfDpaBudget){.max_host_bytes = 1};
  assert(create(f, &budget, &c).reason == TLSF_DPA_HOST_LIMIT && !c);
  budget = (TlsfDpaBudget){.bdd_nodes = 1};
  assert(create(f, &budget, &c).reason == TLSF_DPA_BDD_LIMIT && !c);
  assert(create(node_f(a, node_g(a, node_f(a, p))), nullptr, &c).reason ==
             TLSF_DPA_UNSUPPORTED &&
         !c);
  assert(create(node_x_strong(a, p), nullptr, &c).reason ==
             TLSF_DPA_UNSUPPORTED &&
         !c);
  const char *bad[] = {"a", "a"};
  assert(
      tlsf_dpa_create((TlsfAstNode *)p, bad, 2, nullptr, 0, nullptr, &c).code ==
          TLSF_DPA_INVALID &&
      !c);
  assert(create(node_ap(a, "missing"), nullptr, &c).code == TLSF_DPA_INVALID &&
         !c);
  tlsf_dpa_free(nullptr);
}

static bool label_value(TlsfDpa *c, uint32_t label, unsigned valuation) {
  const TlsfDpaLabelNode *n = tlsf_dpa_label_node(c, label);
  assert(n);
  if (n->kind != TLSF_DPA_DECISION)
    return n->kind == TLSF_DPA_TRUE;
  return label_value(c, (valuation & (1u << n->ap)) ? n->high : n->low,
                     valuation);
}
static bool lasso(TlsfDpa *c, const unsigned *word, unsigned length) {
  size_t size = tlsf_dpa_state_count(c) * length;
  int *seen = malloc(size * sizeof *seen);
  uint32_t *priorities = malloc(size * sizeof *priorities);
  assert(seen && priorities);
  for (size_t i = 0; i < size; ++i)
    seen[i] = -1;
  uint32_t state = tlsf_dpa_initial(c), step = 0;
  while (seen[state * length + step % length] < 0) {
    seen[state * length + step % length] = (int)step;
    const TlsfDpaEdge *row;
    size_t count;
    assert(tlsf_dpa_successors(c, state, &row, &count).code == TLSF_DPA_OK);
    unsigned matches = 0;
    for (size_t i = 0; i < count; ++i)
      if (label_value(c, row[i].label, word[step % length])) {
        state = row[i].successor;
        priorities[step] = row[i].priority;
        ++matches;
      }
    assert(matches == 1);
    ++step;
  }
  uint32_t maximum = 0;
  for (uint32_t i = (uint32_t)seen[state * length + step % length]; i < step;
       ++i)
    if (priorities[i] > maximum)
      maximum = priorities[i];
  free(seen);
  free(priorities);
  return maximum % 2;
}
static void recurrence(Arena *a, Node *p, Node *q) {
  const unsigned overlap[] = {3}, witness[] = {1, 2}, absent[] = {1};
  const unsigned delayed[] = {1, 0, 2}, wrong_delay[] = {1, 2, 0};
  for (unsigned delay = 1; delay <= 2; ++delay) {
    Node *window =
        node_and(a, p, delay == 1 ? node_x(a, q) : node_x(a, node_x(a, q)));
    Node *f = node_g(a, node_f(a, window));
    for (unsigned neg = 0; neg < 2; ++neg) {
      TlsfDpa *c;
      assert(create(neg ? node_not(a, f) : f, nullptr, &c).code == TLSF_DPA_OK);
      assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
      assert(lasso(c, overlap, 1) == !neg);
      assert(lasso(c, absent, 1) == (bool)neg);
      if (delay == 1)
        assert(lasso(c, witness, 2) == !neg);
      else {
        assert(lasso(c, delayed, 3) == !neg);
        assert(lasso(c, wrong_delay, 3) == (bool)neg);
      }
      tlsf_dpa_free(c);
    }
  }
}

static void sweeps(Node *f, bool allow_unproved) {
  TlsfDpaBudget budget = {.allow_unproved = allow_unproved};
  TlsfDpa *c;
  reset(0, 0);
  assert(create(f, &budget, &c).code == TLSF_DPA_OK);
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  size_t hosts = host_count, bdds = bdd_count;
  size_t total_hosts = hosts;
  armed = false;
  tlsf_dpa_free(c);
  for (unsigned type = 0; type < 2; ++type) {
    size_t limit = type ? bdds : hosts;
    assert(limit);
    for (size_t i = 1; i <= limit; ++i) {
      reset(type ? 0 : i, type ? i : 0);
      TlsfDpaStatus status = create(f, &budget, &c);
      if (c)
        status = tlsf_dpa_expand(c);
      assert(fired && status.code == TLSF_DPA_DECLINED);
      assert(status.reason ==
             (type ? TLSF_DPA_BDD_LIMIT : TLSF_DPA_HOST_LIMIT));
      armed = false;
      tlsf_dpa_free(c);
    }
  }
  // Fault every allocation in a later expansion after a published row.
  reset(0, 0);
  assert(create(f, &budget, &c).code == TLSF_DPA_OK);
  const TlsfDpaEdge *first;
  size_t count;
  assert(tlsf_dpa_successors(c, 0, &first, &count).code == TLSF_DPA_OK);
  reset(0, 0);
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  hosts = host_count;
  size_t later_bdds = bdd_count;
  armed = false;
  tlsf_dpa_free(c);
  for (unsigned type = 0; type < 2; ++type) {
    size_t limit = type ? later_bdds : hosts;
    for (size_t i = 1; i <= limit; ++i) {
      assert(create(f, &budget, &c).code == TLSF_DPA_OK);
      assert(tlsf_dpa_successors(c, 0, &first, &count).code == TLSF_DPA_OK);
      TlsfDpaEdge saved = first[0];
      reset(type ? 0 : i, type ? i : 0);
      assert(tlsf_dpa_expand(c).code == TLSF_DPA_DECLINED && fired);
      assert(!memcmp(first, &saved, sizeof saved));
      assert(tlsf_dpa_label_node(c, saved.label));
      no_row(c, 0, type ? TLSF_DPA_BDD_LIMIT : TLSF_DPA_HOST_LIMIT);
      armed = false;
      tlsf_dpa_free(c);
    }
  }
  assert(create(f, &budget, &c).code == TLSF_DPA_OK);
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  tlsf_dpa_free(c);
  printf("allocation sweep: %zu host, %zu BDD operations, %zu later host "
         "failures\n",
         total_hosts, bdds, hosts);
}

static void symbolic(Arena *a) {
  // Parity of 28 APs has a linear shared decision DAG, but 2^28 letters.
  const char *aps[128];
  char storage[128][16];
  Node *f = node_false(a);
  for (unsigned i = 0; i < 128; ++i) {
    snprintf(storage[i], sizeof storage[i], "p%u", i);
    aps[i] = storage[i];
    if (i < 28)
      f = node_equiv(a, f, node_ap(a, aps[i]));
  }
  TlsfDpaBudget budget = {.max_states = 4, .max_host_bytes = 8u << 20};
  TlsfDpa *c;
  assert(tlsf_dpa_create((TlsfAstNode *)f, aps, 128, nullptr, 0, &budget, &c)
             .code == TLSF_DPA_OK);
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  assert(c->dags.n < 256 && c->states.n == 3);
  tlsf_dpa_free(c);
}

static void canonical(Arena *a, Node *p, Node *q) {
  TlsfDpa *c;
  assert(create(node_true(a), nullptr, &c).code == TLSF_DPA_OK);
  uint32_t conjunction =
      dpa_formula(c, (TlsfAstNode *)node_and(a, p, q), false, 0);
  uint32_t reversed =
      dpa_formula(c, (TlsfAstNode *)node_and(a, q, p), false, 0);
  assert(conjunction == reversed);
  uint32_t shifted =
      dpa_formula(c, (TlsfAstNode *)node_x(a, node_and(a, p, q)), false, 0);
  uint32_t distributed = dpa_formula(
      c, (TlsfAstNode *)node_and(a, node_x(a, p), node_x(a, q)), false, 0);
  assert(shifted == distributed);
  uint32_t eventual = dpa_formula(c, (TlsfAstNode *)node_f(a, p), false, 0);
  uint32_t dual =
      dpa_formula(c, (TlsfAstNode *)node_g(a, node_not(a, p)), false, 0);
  // AP_COMBINED: temporal duals are independent propositional atoms.
  assert(dpa_boolean(c, true, eventual, dual) != 0);
  tlsf_dpa_free(c);
  assert(tlsf_dpa_create((TlsfAstNode *)node_false(a), nullptr, 0, nullptr, 0,
                         nullptr, &c)
             .code == TLSF_DPA_OK);
  assert(tlsf_dpa_ap_count(c) == 0 && tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  const TlsfDpaEdge *row = (void *)1;
  size_t count = 7;
  assert(tlsf_dpa_successors(c, UINT32_MAX, &row, &count).code ==
         TLSF_DPA_INVALID);
  assert(!row && !count && tlsf_dpa_status(c).code == TLSF_DPA_OK);
  tlsf_dpa_free(c);
}

static void bounds(Arena *a, Node *p, Node *q) {
  TlsfDpa *c;
  assert(create(node_true(a), nullptr, &c).code == TLSF_DPA_OK);
  c->started = true;
  // Syntax cannot establish safety here. Canonical absorption inside the
  // frozen X operand can; the ambiguous bound must use the exact fallback.
  Node *body = node_or(a, p, node_and(a, p, node_f(a, node_g(a, q))));
  uint32_t f =
      dpa_formula(c, (TlsfAstNode *)node_x(a, node_g(a, body)), false, 0);
  assert(dpa_children(c, f));
  DpaAtom *atom = c->atoms.items[dpa_cls(c, f)->var];
  assert(!(atom->tags & DPA_SAFETY) && !atom->exact_tags);
  assert(dpa_has_tags(c, f, DPA_SAFETY) && atom->exact_tags);
  for (unsigned mask = 0; mask <= DPA_ALL; ++mask)
    assert(dpa_has_tags(c, f, mask) == !!(dpa_tags(c, f) & mask));
  tlsf_dpa_free(c);
}

int main(void) {
  Arena *a = arena_new(4096);
  Node *p = node_ap(a, "a"), *q = node_ap(a, "b");
  Node *delayed = p;
  for (unsigned i = 0; i < 24; ++i)
    delayed = node_x(a, delayed);
  stability(delayed);
  declines(a, p);
  recurrence(a, p, q);
  sweeps(node_g(a, node_f(a, node_and(a, p, node_x(a, q)))), false);
  sweeps(node_g(a, node_f(a, node_and(a, p, node_x(a, node_x(a, q))))), false);
  sweeps(delayed, false); // include vector/hash growth in the failure sweep
  Node *pi = node_g(a, node_f(a, node_and(a, p, node_x(a, q))));
  Node *sigma = node_f(a, node_g(a, node_and(a, q, node_x(a, p))));
  sweeps(node_and(a, pi, sigma), false);
  sweeps(node_equiv(a, pi, sigma), false);
  sweeps(node_g(a, node_u(a, p, node_and(a, q, node_x(a, p)))), true);
  sweeps(node_g(a, node_or(a, p, node_f(a, node_and(a, q, node_x(a, p))))),
         false);
  // Group a finite initial constraint with co-safety siblings, distribute G
  // and F, constrain their unfolding, and reach both terminal product sinks.
  sweeps(node_and(a, node_not(a, p),
                  node_and(a, node_f(a, p),
                           node_and(a, node_f(a, node_x(a, q)), pi))),
         false);
  Node *bundle = node_g(a, node_and(a, node_impl(a, p, node_x(a, q)),
                                    node_f(a, node_or(a, p, q))));
  sweeps(bundle, false);
  sweeps(node_not(a, bundle), false);
  sweeps(node_x(a, node_g(a, node_or(a, p, node_and(a, p, sigma)))), true);
  symbolic(a);
  canonical(a, p, q);
  bounds(a, p, q);
  arena_free(a);
  puts("DPA contract passed");
}
