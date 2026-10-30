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
  return dpa_dag(c, 3, 0, dpa_pair(c, next, rejecting), mark);
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

uint32_t dpa_pair(TlsfDpa *c, uint32_t a, uint32_t r) {
  if (!dpa_poll(c))
    return DPA_BAD;
  uint64_t h = dpa_hash(a, r, 0, 0);
  for (uint32_t i = dpa_bucket(&c->pairs, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaPair *p = c->pairs.items[i];
    if (p->all == a && p->rejecting == r)
      return i;
    i = p->key.next;
  }
  DpaPair *p = dpa_alloc(c, 1, sizeof *p);
  if (!p)
    return DPA_BAD;
  *p = (DpaPair){.key.hash = h, .all = a, .rejecting = r, .dag = DPA_BAD};
  return dpa_insert(c, &c->pairs, p) ? c->pairs.n - 1 : DPA_BAD;
}

// A component and its NNF complement have the same complete run. Only the
// fixed acceptance literal changes; terminal pairs stay in every tuple.
static uint32_t component(TlsfDpa *c, uint32_t f) {
  uint32_t dual = dpa_dual(c, f);
  for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i) {
    DpaComponent *p = c->components.items[i];
    if (p->formula == f)
      return p->colour;
    if (p->dual == f)
      return dpa_class(c, oxidd_bdd_not(dpa_cls(c, p->colour)->bdd));
  }
  bool neg = !(dpa_tags(c, f) & DPA_PI2);
  uint32_t formula = neg ? dual : f;
  DpaComponent *p = dpa_alloc(c, 1, sizeof *p);
  if (!p)
    return DPA_BAD;
  uint32_t colour = dpa_atom(c, TLSF_AST_KIND_COUNT, c->components.n, 0);
  *p = (DpaComponent){.key.hash = dpa_hash(formula, 0, 0, 0),
                      .formula = formula,
                      .dual = neg ? f : dual,
                      .colour = colour};
  if (!dpa_insert(c, &c->components, p))
    return DPA_BAD;
  return neg ? dpa_class(c, oxidd_bdd_not(dpa_cls(c, colour)->bdd)) : colour;
}

uint32_t dpa_acceptance(TlsfDpa *c, uint32_t f) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint32_t result = DPA_BAD;
  if (f < 2)
    result = f;
  else if (dpa_cls(c, f)->acceptance != DPA_BAD)
    result = dpa_cls(c, f)->acceptance;
  else if (dpa_admitted(c, f))
    result = component(c, f);
  else if (dpa_children(c, f)) {
    DpaClass *cl = dpa_cls(c, f);
    DpaAtom *atom = c->atoms.items[cl->var];
    if (!dpa_admitted(c, atom->cls))
      dpa_decline(c, TLSF_DPA_UNSUPPORTED);
    else {
      uint32_t v = component(c, atom->cls);
      result = dpa_ite(c, v, dpa_acceptance(c, cl->high),
                       dpa_acceptance(c, cl->low));
    }
  }
  if (dpa_poll(c))
    dpa_cls(c, f)->acceptance = result;
  --c->recursion;
  return result;
}

uint32_t dpa_tuple(TlsfDpa *c, const uint32_t *values) {
  if (!dpa_poll(c))
    return DPA_BAD;
  uint64_t h = 0;
  for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i)
    h = dpa_hash((uint32_t)h, (uint32_t)(h >> 32), values[i], i);
  size_t bytes = (size_t)c->components.n * sizeof *values;
  for (uint32_t i = dpa_bucket(&c->tuples, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaTuple *t = c->tuples.items[i];
    if (!memcmp(t->values, values, bytes))
      return i;
    i = t->key.next;
  }
  if (bytes > SIZE_MAX - sizeof(DpaTuple))
    return dpa_decline(c, TLSF_DPA_HOST_LIMIT);
  DpaTuple *t = dpa_alloc(c, 1, sizeof *t + bytes);
  if (!t)
    return DPA_BAD;
  t->key.hash = h;
  memcpy(t->values, values, bytes);
  return dpa_insert(c, &c->tuples, t) ? c->tuples.n - 1 : DPA_BAD;
}

static uint32_t joint(TlsfDpa *c, uint32_t tuple, uint32_t leaf) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint64_t h = dpa_hash(tuple, leaf, 0, 0);
  uint32_t result = DPA_BAD;
  uint32_t *values = nullptr;
  for (uint32_t i = dpa_bucket(&c->joints, h); i != DPA_BAD;) {
    DpaProduct *p = c->joints.items[i];
    if (p->lhs == tuple && p->rhs == leaf) {
      result = p->dag;
      goto done;
    }
    if (!dpa_poll(c))
      goto done;
    i = p->key.next;
  }
  DpaTuple *t = c->tuples.items[tuple];
  uint32_t var = DPA_BAD;
  for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i) {
    DpaDag *d = c->dags.items[t->values[i]];
    if (d->kind == 1 && d->var < var)
      var = d->var;
  }
  values = dpa_alloc(c, c->components.n, sizeof *values);
  if (!values)
    goto done;
  if (var == DPA_BAD) {
    uint64_t *colours = dpa_alloc(c, c->colour_words, sizeof *colours);
    if (!colours)
      goto done;
    for (uint32_t i = 0; i < c->components.n; ++i) {
      DpaDag *d = c->dags.items[t->values[i]];
      values[i] = d->low;
      if (d->high)
        dpa_set_colour(colours, i);
    }
    uint32_t next_leaf = leaf;
    uint32_t priority = dpa_tree_step(c, &next_leaf, colours);
    uint32_t target = dpa_state(c, dpa_tuple(c, values), next_leaf);
    result = dpa_dag(c, 2, 0, target, priority);
    dpa_release(c, colours);
  } else {
    uint32_t children[2];
    for (unsigned high = 0; high < 2; ++high) {
      for (uint32_t i = 0; i < c->components.n; ++i) {
        DpaDag *d = c->dags.items[t->values[i]];
        values[i] = d->kind == 1 && d->var == var ? (high ? d->high : d->low)
                                                  : t->values[i];
      }
      children[high] = joint(c, dpa_tuple(c, values), leaf);
    }
    result = dpa_dag(c, 1, var, children[0], children[1]);
  }
  DpaProduct *p = dpa_alloc(c, 1, sizeof *p);
  if (p) {
    *p = (DpaProduct){.key.hash = h, .lhs = tuple, .rhs = leaf, .dag = result};
    dpa_insert(c, &c->joints, p);
  }
done:
  dpa_release(c, values);
  --c->recursion;
  return dpa_poll(c) ? result : DPA_BAD;
}

uint32_t dpa_dela_step(TlsfDpa *c, uint32_t tuple, uint32_t leaf) {
  if (!dpa_poll(c))
    return DPA_BAD;
  DpaTuple *t = c->tuples.items[tuple];
  uint32_t *roots = dpa_alloc(c, c->components.n, sizeof *roots);
  if (!roots)
    return DPA_BAD;
  for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i) {
    DpaPair *p = c->pairs.items[t->values[i]];
    if (p->dag == DPA_BAD)
      p->dag = dpa_product(c, dpa_step_dag(c, p->all),
                           dpa_step_dag(c, p->rejecting));
    roots[i] = p->dag;
  }
  uint32_t result = joint(c, dpa_tuple(c, roots), leaf);
  dpa_release(c, roots);
  return result;
}

uint32_t dpa_dela_initial(TlsfDpa *c) {
  uint32_t *initial = dpa_alloc(c, c->components.n, sizeof *initial);
  if (!initial)
    return DPA_BAD;
  for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i) {
    DpaComponent *p = c->components.items[i];
    uint32_t all = dpa_unfold(c, p->formula);
    uint32_t r = (dpa_tags(c, all) & (DPA_SAFETY | DPA_COSAFETY))
                     ? 0
                     : dpa_remainder(c, p->formula);
    initial[i] = dpa_pair(c, all, r);
  }
  uint32_t result = dpa_tuple(c, initial);
  dpa_release(c, initial);
  return result;
}
