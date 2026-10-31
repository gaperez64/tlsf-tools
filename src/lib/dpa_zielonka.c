#include "dpa_internal.h"

static uint32_t literal(TlsfDpa *c, uint32_t i) {
  DpaComponent *p = c->components.items[i];
  return p->colour;
}
static uint32_t negate(TlsfDpa *c, uint32_t f) {
  return dpa_poll(c) ? dpa_class(c, oxidd_bdd_not(dpa_cls(c, f)->bdd))
                     : DPA_BAD;
}
static bool accepts(TlsfDpa *c, const uint64_t *set) {
  uint32_t f = c->acceptance;
  while (f > 1 && dpa_children(c, f)) {
    DpaClass *cl = dpa_cls(c, f);
    DpaAtom *atom = c->atoms.items[cl->var];
    f = dpa_colour(set, atom->lhs) ? cl->high : cl->low;
  }
  return f == 1;
}
static bool contains(TlsfDpa *c, const uint64_t *a, const uint64_t *b) {
  for (size_t i = 0; i < c->colour_words; ++i)
    if (b[i] & ~a[i])
      return false;
  return true;
}
// One model of a nonfalse colour BDD, with omitted variables false.
static void model(TlsfDpa *c, uint32_t f, uint64_t *set) {
  memset(set, 0, c->colour_words * sizeof *set);
  while (f > 1 && dpa_children(c, f)) {
    DpaClass *cl = dpa_cls(c, f);
    DpaAtom *atom = c->atoms.items[cl->var];
    if (cl->high) {
      dpa_set_colour(set, atom->lhs);
      f = cl->high;
    } else
      f = cl->low;
  }
}
static uint32_t outside(TlsfDpa *c, const uint64_t *set,
                        const uint64_t *subset) {
  uint32_t f = 0;
  for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i)
    if (dpa_colour(set, i) && !dpa_colour(subset, i))
      f = dpa_boolean(c, false, f, literal(c, i));
  return f;
}
// Lexicographic order of the sorted colour lists, including proper prefixes.
static bool before(TlsfDpa *c, const uint64_t *a, const uint64_t *b) {
  uint32_t i = 0, j = 0;
  for (;;) {
    while (i < c->components.n && !dpa_colour(a, i))
      ++i;
    while (j < c->components.n && !dpa_colour(b, j))
      ++j;
    if (i != j || i == c->components.n)
      return j != c->components.n && (i == c->components.n || i < j);
    ++i;
    ++j;
  }
}
typedef struct Child {
  struct Child *next;
  uint32_t node;
} Child;

static uint32_t tree(TlsfDpa *c, const uint64_t *set) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint64_t h = 0;
  for (size_t i = 0; i < c->colour_words && dpa_poll(c); ++i)
    h = dpa_hash((uint32_t)h, (uint32_t)(h >> 32), (uint32_t)set[i],
                 (uint32_t)(set[i] >> 32));
  uint32_t result = DPA_BAD;
  Child *children = nullptr;
  uint64_t *m = nullptr;
  for (uint32_t i = dpa_bucket(&c->trees, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      goto done;
    DpaTreeNode *t = c->trees.items[i];
    if (!memcmp(t->colours, set, c->colour_words * sizeof *set)) {
      result = i;
      goto done;
    }
    i = t->key.next;
  }
  uint32_t remaining =
      accepts(c, set) ? negate(c, c->acceptance) : c->acceptance;
  for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i)
    if (!dpa_colour(set, i))
      remaining = dpa_boolean(c, true, remaining, negate(c, literal(c, i)));
  m = dpa_alloc(c, c->colour_words, sizeof *m);
  if (!m)
    goto done;
  uint32_t count = 0;
  while (remaining && dpa_poll(c)) {
    model(c, remaining, m);
    // Ask for a strict satisfying superset, not a single-variable flip.
    // At most m successful queries: each adds at least one colour.
    for (;;) {
      uint32_t larger = dpa_boolean(c, true, remaining, outside(c, set, m));
      for (uint32_t i = 0; i < c->components.n && dpa_poll(c); ++i)
        if (dpa_colour(m, i))
          larger = dpa_boolean(c, true, larger, literal(c, i));
      if (!dpa_poll(c))
        goto done;
      if (!larger)
        break;
      model(c, larger, m);
    }
    uint32_t child = tree(c, m);
    Child *entry = dpa_alloc(c, 1, sizeof *entry);
    if (!entry)
      goto done;
    DpaTreeNode *node = c->trees.items[child];
    Child **at = &children;
    while (*at && dpa_poll(c)) {
      DpaTreeNode *other = c->trees.items[(*at)->node];
      if (before(c, node->colours, other->colours))
        break;
      at = &(*at)->next;
    }
    *entry = (Child){.next = *at, .node = child};
    *at = entry;
    ++count;
    remaining = dpa_boolean(c, true, remaining, outside(c, set, m));
  }
  DpaTreeNode *t = dpa_alloc(c, 1, sizeof *t);
  if (!t)
    goto done;
  t->key.hash = h;
  t->colours = dpa_alloc(c, c->colour_words, sizeof *set);
  t->children = dpa_alloc(c, count, sizeof *t->children);
  t->count = count;
  if (!dpa_poll(c))
    goto done;
  memcpy(t->colours, set, c->colour_words * sizeof *set);
  uint32_t n = 0;
  for (Child *p = children; p; p = p->next)
    t->children[n++] = p->node;
  if (dpa_insert(c, &c->trees, t))
    result = c->trees.n - 1;
done:
  while (children) {
    Child *next = children->next;
    dpa_release(c, children);
    children = next;
  }
  dpa_release(c, m);
  --c->recursion;
  return result;
}

static uint32_t path(TlsfDpa *c, uint32_t node, uint32_t parent, uint32_t pos) {
  if (!dpa_poll(c))
    return DPA_BAD;
  uint64_t h = dpa_hash(node, parent, pos, 0);
  for (uint32_t i = dpa_bucket(&c->paths, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaPath *p = c->paths.items[i];
    if (p->node == node && p->parent == parent && p->position == pos)
      return i;
    i = p->key.next;
  }
  DpaPath *p = dpa_alloc(c, 1, sizeof *p);
  if (!p)
    return DPA_BAD;
  uint32_t depth =
      parent == DPA_BAD ? 0 : ((DpaPath *)c->paths.items[parent])->depth + 1;
  *p = (DpaPath){.key.hash = h,
                 .node = node,
                 .parent = parent,
                 .position = pos,
                 .depth = depth};
  return dpa_insert(c, &c->paths, p) ? c->paths.n - 1 : DPA_BAD;
}
static uint32_t leftmost(TlsfDpa *c, uint32_t id) {
  while (dpa_poll(c)) {
    DpaPath *p = c->paths.items[id];
    DpaTreeNode *t = c->trees.items[p->node];
    if (!t->count)
      break;
    id = path(c, t->children[0], id, 0);
  }
  return id;
}
void dpa_tree_init(TlsfDpa *c) {
  uint64_t *set = dpa_alloc(c, c->colour_words, sizeof *set);
  if (!set)
    return;
  for (uint32_t i = 0; i < c->components.n; ++i)
    dpa_set_colour(set, i);
  c->root_accepts = accepts(c, set);
  c->root = tree(c, set);
  c->leftmost = leftmost(c, path(c, c->root, DPA_BAD, 0));
  dpa_release(c, set);
}
uint32_t dpa_tree_step(TlsfDpa *c, uint32_t *leaf, const uint64_t *colours) {
  if (!dpa_poll(c))
    return DPA_BAD;
  // Deepest containing anchor, exactly one sibling, then leftmost descent.
  // Paths carry depth/parent separately, so equal subtrees can be shared.
  uint32_t anchor = *leaf, child = *leaf;
  DpaPath *p;
  DpaTreeNode *t;
  for (;;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    p = c->paths.items[anchor];
    t = c->trees.items[p->node];
    if (contains(c, t->colours, colours))
      break;
    child = anchor;
    anchor = p->parent;
  }
  uint32_t priority = p->depth + !c->root_accepts;
  if (t->count) {
    DpaPath *previous = c->paths.items[child];
    uint32_t position = (previous->position + 1) % t->count;
    *leaf = leftmost(c, path(c, t->children[position], anchor, position));
  }
  // Eventually the prefix above the least recurring anchor is fixed. Every
  // recurring colour lies in that anchor's set; otherwise a shallower anchor
  // would recur. Rotation visits/exits every child infinitely, so the recurring
  // set fits no child. Opposite acceptance would put it inside a maximal
  // opposite subset (a child), a contradiction. Thus its acceptance equals
  // the anchor's, whose parity alternates with depth. Empty marks fit the
  // current leaf: the same argument covers the empty recurring set and a
  // root which is already a leaf (an empty path). Odd P converts min-even
  // to max-odd without dropping any priority.
  return c->max_priority - priority;
}
