#include "dpa_internal.h"

// The ordered conservative breakpoint table. In particular, renewal retains
// the finite remainder, and extracts R from raw a rather than unfolded a.
static uint32_t transition(TlsfDpa *c, uint32_t a, uint32_t r) {
  uint32_t next = dpa_unfold(c, a), rejecting = 0;
  unsigned tags = dpa_tags(c, next);
  bool mark = false;
  if (next == 0) {
    // rejecting sink
  } else if (next == 1 || (tags & DPA_SAFETY)) {
    mark = true;
  } else if (tags & DPA_COSAFETY) {
    // suspended until a finite witness reaches true
  } else {
    rejecting = dpa_unfold(c, r);
    if (rejecting == 0)
      rejecting = dpa_remainder(c, a);
    else if (dpa_tags(c, rejecting) & DPA_FINITE) {
      rejecting = dpa_boolean(c, true, rejecting, dpa_remainder(c, a));
      if (rejecting == 0)
        next = 0;
      else
        mark = true;
    }
  }
  if (!dpa_poll(c))
    return DPA_BAD;
  // A one-set tree has exactly one leaf/path, shared by all DELA states.
  uint32_t leaf = 1;
  uint32_t priority = dpa_tree_step(c, &leaf, mark ? 1u : 0u);
  uint32_t target = dpa_state(c, next, rejecting, leaf);
  return dpa_dag(c, 2, 0, target, priority);
}

static uint32_t product_impl(TlsfDpa *c, uint32_t a, uint32_t r) {
  if (!dpa_poll(c))
    return DPA_BAD;
  uint64_t h = dpa_hash(a, r, 0, 0);
  for (uint32_t i = dpa_bucket(&c->products, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaProduct *p = c->products.items[i];
    if (p->lhs == a && p->rhs == r)
      return p->dag;
    i = p->key.next;
  }
  DpaDag *x = c->dags.items[a], *y = c->dags.items[r];
  uint32_t result;
  if (x->kind == 0 && y->kind == 0)
    result = transition(c, x->low, y->low);
  else {
    uint32_t xv = x->kind == 1 ? x->var : DPA_BAD;
    uint32_t yv = y->kind == 1 ? y->var : DPA_BAD;
    uint32_t var = xv < yv ? xv : yv;
    uint32_t low =
        dpa_product(c, xv == var ? x->low : a, yv == var ? y->low : r);
    uint32_t high =
        dpa_product(c, xv == var ? x->high : a, yv == var ? y->high : r);
    result = dpa_dag(c, 1, var, low, high);
  }
  DpaProduct *p = dpa_alloc(c, 1, sizeof *p);
  if (!p)
    return DPA_BAD;
  *p = (DpaProduct){.key.hash = h, .lhs = a, .rhs = r, .dag = result};
  return dpa_insert(c, &c->products, p) ? result : DPA_BAD;
}

uint32_t dpa_product(TlsfDpa *c, uint32_t a, uint32_t r) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint32_t result = product_impl(c, a, r);
  --c->recursion;
  return result;
}
