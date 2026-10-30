#define _POSIX_C_SOURCE 200809L
#include "dpa_internal.h"
#include <time.h>
#include <stdalign.h>

struct DpaAllocation {
  DpaAllocation *next, *prev;
  size_t size;
  max_align_t payload[];
};

uint32_t dpa_decline(TlsfDpa *c, TlsfDpaReason reason) {
  if (c->status.code == TLSF_DPA_OK)
    c->status = (TlsfDpaStatus){TLSF_DPA_DECLINED, reason};
  return DPA_BAD;
}

bool dpa_poll(TlsfDpa *c) {
  if (c->status.code != TLSF_DPA_OK)
    return false;
  if ((c->budget.cancel && *c->budget.cancel) ||
      (c->budget.cancelled && c->budget.cancelled(c->budget.cancel_ctx)))
    dpa_decline(c, TLSF_DPA_CANCELLED);
  if (c->budget.deadline_mono_ns) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t) != 0)
      c->status.code = TLSF_DPA_INTERNAL;
    else if ((uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec >=
             c->budget.deadline_mono_ns)
      dpa_decline(c, TLSF_DPA_DEADLINE);
  }
  return c->status.code == TLSF_DPA_OK;
}

bool dpa_enter(TlsfDpa *c) {
  if (!dpa_poll(c))
    return false;
  if (c->recursion == 512) {
    dpa_decline(c, TLSF_DPA_HOST_LIMIT);
    return false;
  }
  ++c->recursion;
  return true;
}

void *dpa_alloc(TlsfDpa *c, size_t count, size_t size) {
  if (!dpa_poll(c))
    return nullptr;
  if (size && count > (SIZE_MAX - sizeof(DpaAllocation)) / size)
    goto fail;
  size_t bytes = sizeof(DpaAllocation) + count * size;
  if (bytes > SIZE_MAX - c->bytes ||
      (c->budget.max_host_bytes && bytes > c->budget.max_host_bytes - c->bytes))
    goto fail;
  DpaAllocation *a = oxidd_host_calloc(1, bytes);
  if (!a)
    goto fail;
  a->size = bytes;
  a->next = c->allocations;
  if (a->next)
    a->next->prev = a;
  c->allocations = a;
  c->bytes += bytes;
  return a->payload;
fail:
  dpa_decline(c, TLSF_DPA_HOST_LIMIT);
  return nullptr;
}

void dpa_release(TlsfDpa *c, void *ptr) {
  if (!ptr)
    return;
  DpaAllocation *a = (void *)((char *)ptr - sizeof(DpaAllocation));
  if (a->prev)
    a->prev->next = a->next;
  else
    c->allocations = a->next;
  if (a->next)
    a->next->prev = a->prev;
  c->bytes -= a->size;
  free(a);
}

uint64_t dpa_hash(uint32_t a, uint32_t b, uint32_t d, uint32_t e) {
  uint64_t h = UINT64_C(1469598103934665603);
  uint32_t words[] = {a, b, d, e};
  for (unsigned i = 0; i < 4; ++i)
    h = (h ^ words[i]) * UINT64_C(1099511628211);
  return h ^ (h >> 32);
}

uint32_t dpa_bucket(DpaTable *t, uint64_t hash) {
  return t->bins ? t->buckets[hash & (t->bins - 1)] : DPA_BAD;
}

bool dpa_insert(TlsfDpa *c, DpaTable *t, void *item) {
  if (!dpa_poll(c))
    return false;
  if (t->n == DPA_BAD) {
    dpa_decline(c, TLSF_DPA_HOST_LIMIT);
    return false;
  }
  if (t->n == t->cap) {
    uint32_t cap = t->cap ? t->cap * 2 : 16;
    if (cap <= t->cap) {
      dpa_decline(c, TLSF_DPA_HOST_LIMIT);
      return false;
    }
    void **items = dpa_alloc(c, cap, sizeof *items);
    if (!items)
      return false;
    if (t->n)
      memcpy(items, t->items, t->n * sizeof *items);
    dpa_release(c, t->items);
    t->items = items;
    t->cap = cap;
  }
  if (t->n >= t->bins) {
    uint32_t bins = t->cap * 2;
    if (bins <= t->cap) {
      dpa_decline(c, TLSF_DPA_HOST_LIMIT);
      return false;
    }
    uint32_t *buckets = dpa_alloc(c, bins, sizeof *buckets);
    if (!buckets)
      return false;
    for (uint32_t i = 0; i < bins; ++i)
      buckets[i] = DPA_BAD;
    for (uint32_t i = 0; i < t->n; ++i) {
      if (!dpa_poll(c)) {
        dpa_release(c, buckets);
        return false;
      }
      DpaKey *key = t->items[i];
      uint32_t b = (uint32_t)(key->hash & (bins - 1));
      key->next = buckets[b];
      buckets[b] = i;
    }
    dpa_release(c, t->buckets);
    t->buckets = buckets;
    t->bins = bins;
  }
  DpaKey *key = item;
  uint32_t b = (uint32_t)(key->hash & (t->bins - 1));
  key->next = t->buckets[b];
  t->buckets[b] = t->n;
  t->items[t->n++] = item;
  return true;
}

uint32_t dpa_state(TlsfDpa *c, uint32_t a, uint32_t r, uint32_t leaf) {
  if (!dpa_poll(c))
    return DPA_BAD;
  uint64_t h = dpa_hash(a, r, leaf, 0);
  for (uint32_t i = dpa_bucket(&c->states, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaState *s = c->states.items[i];
    if (s->all == a && s->rejecting == r && s->leaf == leaf)
      return i;
    i = s->key.next;
  }
  if (c->budget.max_states && c->states.n >= c->budget.max_states)
    return dpa_decline(c, TLSF_DPA_STATE_LIMIT);
  DpaState *s = dpa_alloc(c, 1, sizeof *s);
  if (!s)
    return DPA_BAD;
  *s = (DpaState){.key.hash = h, .all = a, .rejecting = r, .leaf = leaf};
  return dpa_insert(c, &c->states, s) ? c->states.n - 1 : DPA_BAD;
}

TlsfDpaStatus tlsf_dpa_create(const TlsfAstNode *root,
                              const char *const *inputs, uint32_t ni,
                              const char *const *outputs, uint32_t no,
                              const TlsfDpaBudget *budget, TlsfDpa **out) {
  TlsfDpaStatus invalid = {TLSF_DPA_INVALID, TLSF_DPA_NONE};
  if (!out)
    return invalid;
  *out = nullptr;
  if (!root || (ni && !inputs) || (no && !outputs) || no > UINT32_MAX - ni)
    return invalid;
  if (budget && budget->max_host_bytes &&
      budget->max_host_bytes < sizeof(TlsfDpa))
    return (TlsfDpaStatus){TLSF_DPA_DECLINED, TLSF_DPA_HOST_LIMIT};
  TlsfDpa *c = oxidd_host_calloc(1, sizeof *c);
  if (!c)
    return (TlsfDpaStatus){TLSF_DPA_DECLINED, TLSF_DPA_HOST_LIMIT};
  c->bytes = sizeof *c;
  if (budget)
    c->budget = *budget;
  c->aps = ni + no;
  if (!dpa_poll(c))
    goto fail;
  size_t nodes = c->budget.bdd_nodes ? c->budget.bdd_nodes : (1u << 18);
  size_t cache = c->budget.bdd_cache ? c->budget.bdd_cache : (1u << 16);
  if (nodes < 256 || nodes >= UINT32_MAX || cache < 16 ||
      cache > SIZE_MAX / 64) {
    dpa_decline(c, TLSF_DPA_BDD_LIMIT);
    goto fail;
  }
  c->manager = tlsf_oxidd_manager_new(nodes, cache);
  if (!c->manager._p) {
    dpa_decline(c, TLSF_DPA_BDD_LIMIT);
    goto fail;
  }
  if (dpa_class(c, oxidd_bdd_false(c->manager)) != 0 ||
      dpa_class(c, oxidd_bdd_true(c->manager)) != 1)
    goto fail;
  c->names = dpa_alloc(c, c->aps, sizeof *c->names);
  if (!c->names)
    goto fail;
  for (uint32_t i = 0; i < c->aps; ++i) {
    const char *name = i < ni ? inputs[i] : outputs[i - ni];
    if (!name || !*name) {
      c->status = invalid;
      goto fail;
    }
    for (uint32_t j = 0; j < i; ++j) {
      if (!dpa_poll(c))
        goto fail;
      if (!strcmp(c->names[j], name)) {
        c->status = invalid;
        goto fail;
      }
    }
    c->names[i] = dpa_alloc(c, strlen(name) + 1, 1);
    if (!c->names[i])
      goto fail;
    strcpy(c->names[i], name);
    if (dpa_atom(c, TLSF_AST_AP, i, 0) == DPA_BAD)
      goto fail;
  }
  uint32_t f = dpa_formula(c, root, false, 0);
  if (!dpa_poll(c))
    goto fail;
  unsigned tags = dpa_tags(c, f);
  if (!(tags & (DPA_SAFETY | DPA_COSAFETY))) {
    // Recognize precisely G F finite or its NNF dual F G finite. Boolean
    // products and arbitrary Pi_2 components require the later proof gate.
    if (!dpa_children(c, f))
      goto fail;
    DpaClass *cl = dpa_cls(c, f);
    if (cl->low != 0 || cl->high != 1)
      goto unsupported;
    DpaAtom *outer = c->atoms.items[cl->var];
    c->complement = outer->op == TLSF_AST_F;
    if (outer->op != TLSF_AST_G && !c->complement)
      goto unsupported;
    uint32_t inner_id = outer->lhs;
    if (!dpa_children(c, inner_id))
      goto fail;
    DpaClass *inner_class = dpa_cls(c, inner_id);
    if (inner_class->low != 0 || inner_class->high != 1)
      goto unsupported;
    DpaAtom *inner = c->atoms.items[inner_class->var];
    if (inner->op != (c->complement ? TLSF_AST_G : TLSF_AST_F) ||
        !(dpa_tags(c, inner->lhs) & DPA_FINITE))
      goto unsupported;
    if (c->complement)
      f = dpa_formula(c, root, true, 0);
  }
  dpa_tree_init(c);
  uint32_t all = dpa_unfold(c, f);
  uint32_t r = (dpa_tags(c, all) & (DPA_SAFETY | DPA_COSAFETY))
                   ? 0
                   : dpa_remainder(c, f);
  c->initial = dpa_state(c, all, r, 1);
  if (!dpa_poll(c))
    goto fail;
  for (uint32_t i = 0; i < c->syntax.n; ++i)
    dpa_release(c, c->syntax.items[i]);
  dpa_release(c, c->syntax.items);
  dpa_release(c, c->syntax.buckets);
  c->syntax = (DpaTable){0};
  *out = c;
  return c->status;
unsupported:
  dpa_decline(c, TLSF_DPA_UNSUPPORTED);
fail:;
  TlsfDpaStatus status = c->status;
  tlsf_dpa_free(c);
  return status;
}

void tlsf_dpa_free(TlsfDpa *c) {
  if (!c)
    return;
  for (uint32_t i = 0; i < c->classes.n; ++i)
    oxidd_bdd_unref(dpa_cls(c, i)->bdd);
  if (c->manager._p)
    oxidd_bdd_manager_unref(c->manager);
  while (c->allocations)
    dpa_release(c, c->allocations->payload);
  free(c);
}

TlsfDpaStatus tlsf_dpa_status(const TlsfDpa *c) {
  return c ? c->status : (TlsfDpaStatus){TLSF_DPA_INVALID, TLSF_DPA_NONE};
}
TlsfDpaState tlsf_dpa_initial(const TlsfDpa *c) {
  return c ? c->initial : DPA_BAD;
}
uint32_t tlsf_dpa_ap_count(const TlsfDpa *c) { return c ? c->aps : 0; }
const char *tlsf_dpa_ap_name(const TlsfDpa *c, uint32_t ap) {
  return c && ap < c->aps ? c->names[ap] : nullptr;
}
uint32_t tlsf_dpa_max_priority(const TlsfDpa *c) { return c ? 3 : 0; }
size_t tlsf_dpa_state_count(const TlsfDpa *c) { return c ? c->states.n : 0; }

static uint32_t export_impl(TlsfDpa *c, uint32_t f) {
  if (!dpa_poll(c))
    return DPA_BAD;
  DpaClass *cl = dpa_cls(c, f);
  if (cl->label != DPA_BAD)
    return f;
  if (!dpa_children(c, f))
    return DPA_BAD;
  if (f > 1) {
    if (cl->var >= c->aps) {
      c->status.code = TLSF_DPA_INTERNAL;
      return DPA_BAD;
    }
    if (dpa_export(c, cl->low) == DPA_BAD || dpa_export(c, cl->high) == DPA_BAD)
      return DPA_BAD;
  }
  cl->description = (TlsfDpaLabelNode){
      f < 2 ? (f ? TLSF_DPA_TRUE : TLSF_DPA_FALSE) : TLSF_DPA_DECISION, cl->var,
      cl->low, cl->high};
  cl->label = f;
  return f;
}

uint32_t dpa_export(TlsfDpa *c, uint32_t f) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint32_t result = export_impl(c, f);
  --c->recursion;
  return result;
}

const TlsfDpaLabelNode *tlsf_dpa_label_node(const TlsfDpa *c, uint32_t f) {
  // Descriptions are embedded in each separately allocated class.
  if (!c || f >= c->classes.n)
    return nullptr;
  DpaClass *cl = c->classes.items[f];
  return cl->label == DPA_BAD ? nullptr : &cl->description;
}

TlsfDpaStatus tlsf_dpa_successors(TlsfDpa *c, uint32_t id,
                                  const TlsfDpaEdge **edges, size_t *count) {
  if (edges)
    *edges = nullptr;
  if (count)
    *count = 0;
  if (!c || !edges || !count || id >= c->states.n)
    return (TlsfDpaStatus){TLSF_DPA_INVALID, TLSF_DPA_NONE};
  if (!dpa_poll(c))
    return c->status;
  DpaState *s = c->states.items[id];
  if (!s->edges) {
    uint32_t a = dpa_step_dag(c, s->all), r = dpa_step_dag(c, s->rejecting);
    uint32_t root = dpa_product(c, a, r);
    if (!dpa_poll(c))
      return c->status;
    // DAG children precede parents. Propagate and OR guards once per shared
    // node, rather than expanding root-to-leaf paths or alphabet letters.
    uint32_t n = c->dags.n;
    uint32_t *guards = dpa_alloc(c, n, sizeof *guards);
    TlsfDpaEdge *row = nullptr;
    if (!guards)
      return c->status;
    guards[root] = 1;
    size_t leaves = 0;
    for (uint32_t i = root + 1; i-- > 0 && dpa_poll(c);) {
      if (!guards[i])
        continue;
      DpaDag *d = c->dags.items[i];
      if (d->kind == 2) {
        ++leaves;
        continue;
      }
      DpaAtom *atom = c->atoms.items[d->var];
      uint32_t low = dpa_ite(c, atom->cls, 0, guards[i]);
      uint32_t high = dpa_ite(c, atom->cls, guards[i], 0);
      guards[d->low] = dpa_boolean(c, false, guards[d->low], low);
      guards[d->high] = dpa_boolean(c, false, guards[d->high], high);
    }
    if (dpa_poll(c))
      row = dpa_alloc(c, leaves, sizeof *row);
    size_t at = 0;
    for (uint32_t i = 0; row && i <= root && dpa_poll(c); ++i) {
      DpaDag *d = c->dags.items[i];
      if (guards[i] && d->kind == 2) {
        uint32_t label = dpa_export(c, guards[i]);
        row[at++] = (TlsfDpaEdge){label, d->low, d->high};
      }
    }
    dpa_release(c, guards);
    if (!dpa_poll(c)) {
      dpa_release(c, row);
      return c->status;
    }
    s->edges = row;
    s->count = at;
  }
  *edges = s->edges;
  *count = s->count;
  return c->status;
}

TlsfDpaStatus tlsf_dpa_expand(TlsfDpa *c) {
  if (!c)
    return tlsf_dpa_status(c);
  // States are interned on discovery: their IDs are the FIFO work queue.
  for (uint32_t i = 0; i < c->states.n && dpa_poll(c); ++i) {
    const TlsfDpaEdge *edges;
    size_t count;
    if (tlsf_dpa_successors(c, i, &edges, &count).code != TLSF_DPA_OK)
      break;
  }
  return c->status;
}
