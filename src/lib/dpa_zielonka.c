#include "dpa_internal.h"

void dpa_tree_init(TlsfDpa *c) {
  // Inf(0) and Fin(0) have the same tree shape; only the root parity differs.
  c->tree[0] = (DpaTreeNode){1, 0, DPA_BAD, 1, 1, 0};
  c->tree[1] = (DpaTreeNode){0, 1, 0, DPA_BAD, 1, 0};
}

uint32_t dpa_tree_step(TlsfDpa *c, uint32_t *leaf, unsigned colours) {
  // Ordinary Zielonka update: find the deepest containing anchor, rotate
  // exactly one sibling, then descend to the leftmost leaf. No stuttering,
  // local trees, lookahead, SCC exploration or resets.
  uint32_t anchor = *leaf;
  while (colours & ~c->tree[anchor].colours)
    anchor = c->tree[anchor].parent;
  uint32_t priority = c->tree[anchor].depth + (c->complement ? 1u : 0u);
  if (c->tree[anchor].first_child != DPA_BAD) {
    uint32_t child = *leaf;
    while (c->tree[child].parent != anchor)
      child = c->tree[child].parent;
    uint32_t position = (c->tree[child].position + 1) % c->tree[child].siblings;
    child = c->tree[anchor].first_child + position;
    while (c->tree[child].first_child != DPA_BAD)
      child = c->tree[child].first_child;
    *leaf = child;
  }
  // Minimum recurring anchor depth is 0 iff colour 0 recurs infinitely;
  // otherwise it is 1 (including the forever-empty mark sequence). Offsetting
  // a rejecting root swaps Inf/Fin. P=3 is odd and >m+1, so P-p converts
  // min-even to max-odd. Empty leaf paths use the same anchor rule.
  return 3 - priority;
}
