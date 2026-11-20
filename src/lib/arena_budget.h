#ifndef TLSF_ARENA_BUDGET_H
#define TLSF_ARENA_BUDGET_H

#include "tlsf/arena.h"

typedef struct ArenaSlab {
  struct ArenaSlab *next;
  size_t capacity, used;
  // Data follows immediately after this header.
} ArenaSlab;

struct ArenaSlabArena {
  ArenaSlab *head;
  size_t default_slab;
  bool failed;
  int (*cancelled)(void *, size_t);
  void *cancel_ctx;
  unsigned budget_steps;
};

bool arena_poll_budget(Arena *a, size_t bytes);

// No function call or counter update for ordinary, unbudgeted frontends.
static inline bool arena_check_budget(Arena *a, size_t bytes) {
  if (!a->cancelled)
    return true;
  if (a->failed)
    return false;
  if (!bytes && a->budget_steps) {
    --a->budget_steps;
    return true;
  }
  return arena_poll_budget(a, bytes);
}

static inline Arena *arena_new_child(Arena *parent, size_t size) {
  if (!arena_check_budget(parent, size + 4096))
    return nullptr;
  Arena *child = arena_new(size);
  if (child)
    arena_set_budget(child, parent->cancelled, parent->cancel_ctx);
  return child;
}

#endif
