#include "tlsf/arena.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

typedef struct ArenaSlab {
  struct ArenaSlab *next; ///< linked list of slabs
  size_t capacity;        ///< total usable bytes in this slab
  size_t used;            ///< bytes consumed so far
  // Data follows immediately after this header in memory.
} ArenaSlab;

struct ArenaSlabArena {
  ArenaSlab *head;      ///< current (most-recently allocated) slab
  size_t default_slab;  ///< size used when a new slab is needed
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Round `v` up to the next multiple of `align` (must be power-of-two).
static inline size_t align_up(size_t v, size_t align) {
  assert((align & (align - 1u)) == 0u && "align must be power-of-two");
  return (v + align - 1u) & ~(align - 1u);
}

static ArenaSlab *slab_new(size_t capacity) {
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
  a->head = slab_new(slab_size);
  if (!a->head) {
    free(a);
    return nullptr;
  }
  return a;
}

void *arena_alloc_aligned(Arena *a, size_t size, size_t align) {
  assert(a && "null arena");
  if (size == 0)
    size = 1; // guarantee non-null on success

  ArenaSlab *s = a->head;
  size_t offset = align_up(s->used, align);

  if (offset + size > s->capacity) {
    // Current slab is exhausted — allocate a new one.
    size_t new_cap = a->default_slab;
    if (size > new_cap)
      new_cap = align_up(size, 4096u); // oversized single allocation
    ArenaSlab *ns = slab_new(new_cap);
    if (!ns)
      return nullptr;
    ns->next = s;
    a->head = ns;
    s = ns;
    offset = 0;
  }

  void *ptr = (char *)(s + 1) + offset;
  memset(ptr, 0, size);
  s->used = offset + size;
  return ptr;
}

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
