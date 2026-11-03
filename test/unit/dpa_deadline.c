#define _POSIX_C_SOURCE 200809L
#include "dpa_internal.h"
#include "dpa_buchi.h"
#include "tlsf/ast.h"
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <time.h>

// No sleeps: a wrapped foreign allocation/free or callback advances the clock.
// Thread-local state excludes OxiDD's background workers from these fixtures.
static _Thread_local bool mock, clock_failure, cancel_callback;
static _Thread_local uint64_t now;
static _Thread_local unsigned clocks, callbacks, expire_at, cancel_at;
static _Thread_local bool slow_alloc, slow_manager, slow_syntax_free;
static _Thread_local unsigned context_frees, expire_context_free;
static _Thread_local TlsfDpa *tracked;
static _Thread_local TlsfDpa **published;
enum { DEADLINE = 1000 };

int __real_clock_gettime(clockid_t, struct timespec *);
int __wrap_clock_gettime(clockid_t, struct timespec *);
int __wrap_clock_gettime(clockid_t id, struct timespec *t) {
  if (!mock || id != CLOCK_MONOTONIC)
    return __real_clock_gettime(id, t);
  ++clocks;
  if (clock_failure) {
    errno = EIO;
    return -1;
  }
  *t = (struct timespec){.tv_nsec = (long)now};
  return 0;
}
// Supply these tiny project-owned seams in the test so their production
// archive objects are not extracted/inlined under LTO. Allocation and manager
// semantics match oxidd_host.c/oxidd_runtime.c; only the observers differ.
void *oxidd_host_realloc(void *p, size_t size) { return realloc(p, size); }
void *oxidd_host_calloc(size_t n, size_t size) {
  void *p = calloc(n, size);
  if (mock) {
    if (n == 1 && size == sizeof(TlsfDpa))
      tracked = p;
    if (slow_alloc)
      now = DEADLINE;
  }
  return p;
}
oxidd_bdd_manager_t tlsf_oxidd_manager_new(size_t nodes, size_t cache) {
  oxidd_bdd_manager_t manager = oxidd_bdd_manager_new(nodes, cache, 1);
  if (mock && slow_manager)
    now = DEADLINE;
  return manager;
}
void __real_free(void *);
void __wrap_free(void *);
void __wrap_free(void *p) {
  if (mock && p) {
    if (slow_syntax_free && tracked && tracked->states.n && tracked->syntax.n &&
        !tracked->started)
      now = DEADLINE;
    if (published && *published && p != *published)
      now = DEADLINE;
    if (p == tracked) {
      tracked = nullptr;
      if (++context_frees == expire_context_free)
        now = DEADLINE;
    }
  }
  __real_free(p);
}
static int cancelled(void *unused) {
  (void)unused;
  if (++callbacks == expire_at)
    now = DEADLINE;
  return cancel_callback || callbacks == cancel_at;
}
static void reset(void) {
  now = clocks = callbacks = expire_at = cancel_at = 0;
  context_frees = expire_context_free = 0;
  clock_failure = cancel_callback = slow_alloc = slow_manager =
      slow_syntax_free = false;
  tracked = nullptr;
  published = nullptr;
}
static TlsfDpaBudget budget(void) {
  return (TlsfDpaBudget){.deadline_mono_ns = DEADLINE, .cancelled = cancelled};
}
static void stopped(TlsfDpaStatus status, TlsfDpaReason reason) {
  assert(status.code == TLSF_DPA_DECLINED && status.reason == reason);
}
static void polling(void) {
  reset();
  TlsfDpa c = {.budget = budget()};
  for (unsigned i = 0; i < 512; ++i) {
    assert(dpa_poll(&c));
    assert(callbacks == i + 1 && clocks == i / 256 + 1);
  }
  assert(dpa_poll_now(&c) && clocks == 3 && callbacks == 513);
  now = DEADLINE;
  for (unsigned i = 0; i < 255; ++i)
    assert(dpa_poll(&c));
  assert(!dpa_poll(&c) && clocks == 4);
  stopped(c.status, TLSF_DPA_DEADLINE);
  now = 0;
  unsigned saved = callbacks;
  assert(!dpa_poll_now(&c) && callbacks == saved && clocks == 4);

  // Cancellation still runs at every skipped clock site.
  for (unsigned i = 1; i < 256; ++i) {
    reset();
    c = (TlsfDpa){.budget = budget()};
    assert(dpa_poll(&c));
    cancel_at = i + 1;
    for (unsigned j = 1; j < i; ++j)
      assert(dpa_poll(&c));
    assert(!dpa_poll(&c) && callbacks == i + 1 && clocks == 1);
    stopped(c.status, TLSF_DPA_CANCELLED);
    cancel_at = 0;
    assert(!dpa_poll_now(&c));
  }
  reset();
  c = (TlsfDpa){.budget = budget(), .deadline_polls = UINT32_MAX};
  assert(dpa_poll(&c) && !clocks);
  assert(dpa_poll(&c) && clocks == 1); // Unsigned wrap preserves the bound.
  volatile bool flag = true;
  c.budget.cancel = &flag;
  unsigned saved_callbacks = callbacks;
  assert(!dpa_poll(&c) && callbacks == saved_callbacks && clocks == 1);
  stopped(c.status, TLSF_DPA_CANCELLED);
  // Preserve legacy precedence on an actual clock read: cancellation beats
  // expiry; clock failure changes code to INTERNAL but retains first reason.
  reset();
  c = (TlsfDpa){.budget = budget()};
  cancel_callback = true;
  now = DEADLINE;
  assert(!dpa_poll_now(&c));
  stopped(c.status, TLSF_DPA_CANCELLED);
  c.status = (TlsfDpaStatus){0};
  clock_failure = true;
  assert(!dpa_poll_now(&c) && c.status.code == TLSF_DPA_INTERNAL &&
         c.status.reason == TLSF_DPA_CANCELLED);
  c.status = (TlsfDpaStatus){0};
  cancel_callback = false;
  assert(!dpa_poll_now(&c) && c.status.code == TLSF_DPA_INTERNAL &&
         c.status.reason == TLSF_DPA_NONE);
  c.status = (TlsfDpaStatus){TLSF_DPA_DECLINED, TLSF_DPA_HOST_LIMIT};
  saved = callbacks;
  unsigned saved_clocks = clocks;
  assert(!dpa_poll_now(&c) && callbacks == saved && clocks == saved_clocks);
  stopped(c.status, TLSF_DPA_HOST_LIMIT);
}

static const char *const names[] = {"a", "b"};
static Node *p, *q, *gf, *eventual, *unfolded, *unsupported;
static TlsfDpaStatus create(Node *f, TlsfDpa **out) {
  TlsfDpaBudget b = budget();
  return tlsf_dpa_create((TlsfAstNode *)f, names, 2, nullptr, 0, &b, out);
}
enum Operation {
  CREATE,
  DAG,
  BUCHI,
  EQUAL,
  BOOLEAN_DIFFERENT,
  TEMPORAL,
  UNKNOWN,
  ROW,
  CACHED,
  TRAP,
  EXPAND,
  PARTITION,
  OPERATIONS
};
static TlsfDpa *prepare(enum Operation op, uint32_t *id) {
  TlsfDpa *c = nullptr;
  *id = 0;
  if (op < ROW)
    return nullptr;
  assert(create(op == TRAP ? p : gf, &c).code == TLSF_DPA_OK);
  if (op == CACHED || op == TRAP || op == PARTITION) {
    const TlsfDpaEdge *edges;
    size_t count;
    assert(tlsf_dpa_successors(c, 0, &edges, &count).code == TLSF_DPA_OK);
    if (op == TRAP) {
      assert(count == 2);
      *id = edges[0].successor;
      DpaState *s = c->states.items[*id];
      assert(s->tuple == DPA_BAD && s->leaf < 2 && !s->edges);
    }
  }
  return c;
}
static TlsfDpaStatus operate(enum Operation op, TlsfDpa **c, uint32_t id) {
  TlsfDpaBudget b = budget();
  bool equal = true;
  char klass = '?';
  TlsfDpaStatus status;
  switch (op) {
  case CREATE:
    return create(gf, c);
  case DAG: {
    const TlsfDpaFormulaNode dag[] = {{TLSF_AST_AP, DPA_BAD, DPA_BAD, 0},
                                      {TLSF_AST_F, 0, DPA_BAD, DPA_BAD},
                                      {TLSF_AST_G, 1, DPA_BAD, DPA_BAD}};
    return tlsf_dpa_create_from_dag(dag, 3, 2, names, 2, nullptr, 0,
                                    TLSF_DPA_PARITY, &b, c);
  }
  case BUCHI:
    status = dpa_buchi_create((TlsfAstNode *)gf, names, 2, &b, c, &klass);
    assert(status.code != TLSF_DPA_OK || klass == 'R');
    return status;
  case EQUAL:
  case BOOLEAN_DIFFERENT:
  case TEMPORAL:
  case UNKNOWN:
    status = dpa_formula_equal(
        (TlsfAstNode *)(op == UNKNOWN ? unsupported : eventual),
        (TlsfAstNode *)(op == EQUAL                                ? eventual
                        : op == UNKNOWN || op == BOOLEAN_DIFFERENT ? q
                                                                   : unfolded),
        names, 2, &b, op != BOOLEAN_DIFFERENT, &equal);
    assert(equal ==
           (status.code == TLSF_DPA_OK && (op == EQUAL || op == TEMPORAL)));
    return status;
  case ROW:
  case CACHED:
  case TRAP: {
    const TlsfDpaEdge *edges = (void *)1;
    size_t count = 17;
    status = tlsf_dpa_successors(*c, id, &edges, &count);
    assert(status.code == TLSF_DPA_OK ? edges && count : !edges && !count);
    return status;
  }
  case EXPAND:
    return tlsf_dpa_expand(*c);
  case PARTITION: {
    uint32_t labels[] = {1};
    bool partition = dpa_labels_partition(*c, labels, 1);
    status = tlsf_dpa_status(*c);
    assert(partition == (status.code == TLSF_DPA_OK));
    return status;
  }
  default:
    abort();
  }
}
static void boundaries(void) {
  for (enum Operation op = CREATE; op < OPERATIONS; ++op) {
    reset();
    uint32_t id;
    TlsfDpa *c = prepare(op, &id);
    callbacks = 0;
    assert(operate(op, &c, id).code == TLSF_DPA_OK);
    unsigned last = callbacks;
    assert(last >= 2);
    tlsf_dpa_free(c);
    reset();
    c = prepare(op, &id);
    now = DEADLINE;
    stopped(operate(op, &c, id), TLSF_DPA_DEADLINE);
    if (op < EQUAL)
      assert(!c);
    tlsf_dpa_free(c);
    for (unsigned cancel = 0; cancel < 2; ++cancel) {
      reset();
      c = prepare(op, &id);
      callbacks = 0;
      if (cancel)
        cancel_at = last;
      else
        expire_at = last;
      stopped(operate(op, &c, id),
              cancel ? TLSF_DPA_CANCELLED : TLSF_DPA_DEADLINE);
      if (op < EQUAL)
        assert(!c);
      if (c) {
        now = cancel_at = expire_at = 0;
        stopped(tlsf_dpa_expand(c),
                cancel ? TLSF_DPA_CANCELLED : TLSF_DPA_DEADLINE);
      }
      tlsf_dpa_free(c);
    }
  }
}
static void slow_operations(void) {
  reset();
  TlsfDpa *c;
  slow_manager = true;
  stopped(create(gf, &c), TLSF_DPA_DEADLINE);
  assert(!c && now == DEADLINE);
  reset();
  assert(create(gf, &c).code == TLSF_DPA_OK);
  slow_alloc = true;
  stopped(operate(ROW, &c, 0), TLSF_DPA_DEADLINE);
  slow_alloc = false;
  tlsf_dpa_free(c);
  reset();
  slow_syntax_free = true;
  stopped(create(gf, &c), TLSF_DPA_DEADLINE);
  assert(!c && now == DEADLINE);
  reset();
  published = &c;
  c = nullptr;
  stopped(operate(DAG, &c, 0), TLSF_DPA_DEADLINE);
  assert(!c && now == DEADLINE);
  for (enum Operation op = EQUAL; op <= UNKNOWN; ++op) {
    reset();
    expire_context_free = op == EQUAL || op == BOOLEAN_DIFFERENT ? 1 : 2;
    stopped(operate(op, &c, 0), TLSF_DPA_DEADLINE);
    assert(context_frees == expire_context_free);
  }
}
int main(void) {
  Arena *a = arena_new(4096);
  p = node_ap(a, "a");
  q = node_ap(a, "b");
  eventual = node_f(a, p);
  unfolded = node_or(a, p, node_x(a, eventual));
  gf = node_g(a, eventual);
  unsupported = node_g(a, node_f(a, node_u(a, p, q)));
  mock = true;
  polling();
  boundaries();
  slow_operations();
  mock = false;
  arena_free(a);
  puts("DPA sampled deadlines and exact API boundaries passed");
}
