#include "arena_budget.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifdef TLSF_ARENA_FAULT
bool tlsf_arena_fault(size_t size, bool slab);
#endif

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Round `v` up to the next multiple of `align` (must be power-of-two).
static inline size_t align_up(size_t v, size_t align) {
  assert((align & (align - 1u)) == 0u && "align must be power-of-two");
  return (v + align - 1u) & ~(align - 1u);
}

static ArenaSlab *slab_new(size_t capacity) {
  if (capacity > SIZE_MAX - sizeof(ArenaSlab))
    return nullptr;
#ifdef TLSF_ARENA_FAULT
  if (tlsf_arena_fault(capacity, true))
    return nullptr;
#endif
  // Allocate header + data in one block.
  ArenaSlab *s = malloc(sizeof(ArenaSlab) + capacity);
  if (!s)
    return nullptr;
  s->next = nullptr;
  s->capacity = capacity;
  s->used = 0;
  return s;
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

Arena *arena_new(size_t slab_size) {
  Arena *a = malloc(sizeof(Arena));
  if (!a)
    return nullptr;
  a->default_slab = slab_size;
  a->failed = false;
  a->cancelled = nullptr;
  a->cancel_ctx = nullptr;
  a->budget_steps = 0;
  a->head = slab_new(slab_size);
  if (!a->head) {
    free(a);
    return nullptr;
  }
  return a;
}

void *arena_alloc_aligned(Arena *a, size_t size, size_t align) {
  assert(a && "null arena");
  if (!arena_check_budget(a, 0))
    return nullptr;
#ifdef TLSF_ARENA_FAULT
  if (tlsf_arena_fault(size, false))
    goto fail;
#endif
  if (size == 0)
    size = 1; // guarantee non-null on success

  ArenaSlab *s = a->head;
  assert(align && (align & (align - 1u)) == 0u);
  if (s->used > SIZE_MAX - (align - 1u))
    goto fail;
  size_t offset = align_up(s->used, align);

  if (offset > s->capacity || size > s->capacity - offset) {
    // Current slab is exhausted — allocate a new one.
    size_t new_cap = a->default_slab;
    if (size > new_cap) {
      if (size > SIZE_MAX - 4095u)
        goto fail;
      new_cap = align_up(size, 4096u); // oversized single allocation
    }
    if (new_cap > SIZE_MAX - sizeof(ArenaSlab) ||
        !arena_check_budget(a, new_cap + sizeof(ArenaSlab)))
      goto fail;
    ArenaSlab *ns = slab_new(new_cap);
    if (!ns)
      goto fail;
    ns->next = s;
    a->head = ns;
    s = ns;
    offset = 0;
  }

  void *ptr = (char *)(s + 1) + offset;
  memset(ptr, 0, size);
  s->used = offset + size;
  return ptr;
fail:
  a->failed = true;
  return nullptr;
}

void *arena_alloc_array(Arena *a, size_t size, size_t count, size_t align) {
  if (size && count > SIZE_MAX / size) {
    a->failed = true;
    return nullptr;
  }
  return arena_alloc_aligned(a, size * count, align);
}

bool arena_failed(const Arena *a) { return a->failed; }

void arena_set_budget(Arena *a, int (*cancelled)(void *, size_t), void *ctx) {
  a->cancelled = cancelled;
  a->cancel_ctx = ctx;
  a->budget_steps = 0;
}

bool arena_poll_budget(Arena *a, size_t bytes) {
  a->budget_steps = 4095;
  if (a->cancelled(a->cancel_ctx, bytes))
    a->failed = true;
  return !a->failed;
}

void arena_mark_failed(Arena *a) { a->failed = true; }

void arena_free(Arena *a) {
  if (!a)
    return;
  ArenaSlab *s = a->head;
  while (s) {
    ArenaSlab *next = s->next;
    free(s);
    s = next;
  }
  free(a);
}
