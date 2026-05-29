#include "tlsf/intern.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// FNV-1a hash
// ---------------------------------------------------------------------------

static uint64_t fnv1a(const char *s, size_t len) {
  uint64_t h = 14695981039346656037ULL;
  for (size_t i = 0; i < len; i++) {
    h ^= (uint8_t)s[i];
    h *= 1099511628211ULL;
  }
  return h;
}

// ---------------------------------------------------------------------------
// Open-addressing hash table
// ---------------------------------------------------------------------------

#define INTERN_INITIAL_CAP 256u // must be power-of-two
#define INTERN_LOAD_NUM 3u      // resize when load > 3/4
#define INTERN_LOAD_DEN 4u

typedef struct {
  const char *key; ///< nullptr = empty slot; points into arena
} InternSlot;

struct InternTable {
  Arena *arena;
  InternSlot *slots;
  size_t cap;  ///< number of slots (power-of-two)
  size_t used; ///< occupied slots
};

static bool intern_insert(InternSlot *slots, size_t cap, const char *key) {
  uint64_t h = fnv1a(key, strlen(key));
  size_t idx = (size_t)(h & (cap - 1u));
  for (size_t i = 0; i < cap; i++) {
    size_t probe = (idx + i) & (cap - 1u);
    if (!slots[probe].key) {
      slots[probe].key = key;
      return true;
    }
    // Duplicate detection: callers only insert known-unique strings.
  }
  return false; // table full (shouldn't happen with load-factor guard)
}

static int intern_grow(InternTable *t) {
  size_t new_cap = t->cap * 2u;
  InternSlot *new_slots = calloc(new_cap, sizeof(InternSlot));
  if (!new_slots)
    return -1;
  for (size_t i = 0; i < t->cap; i++) {
    if (t->slots[i].key)
      intern_insert(new_slots, new_cap, t->slots[i].key);
  }
  free(t->slots);
  t->slots = new_slots;
  t->cap = new_cap;
  return 0;
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

InternTable *intern_table_new(Arena *arena) {
  InternTable *t = malloc(sizeof(InternTable));
  if (!t)
    return nullptr;
  t->arena = arena;
  t->cap = INTERN_INITIAL_CAP;
  t->used = 0;
  t->slots = calloc(t->cap, sizeof(InternSlot));
  if (!t->slots) {
    free(t);
    return nullptr;
  }
  return t;
}

void intern_table_free(InternTable *t) {
  if (!t)
    return;
  free(t->slots);
  free(t);
}

const char *intern_n(InternTable *t, const char *s, size_t len) {
  assert(t && s);

  // Probe for existing entry.
  uint64_t h = fnv1a(s, len);
  size_t idx = (size_t)(h & (t->cap - 1u));
  for (size_t i = 0; i < t->cap; i++) {
    size_t probe = (idx + i) & (t->cap - 1u);
    const char *k = t->slots[probe].key;
    if (!k)
      break; // empty slot → not present
    if (strncmp(k, s, len) == 0 && k[len] == '\0')
      return k; // found
  }

  // Not found — copy into arena then insert.
  if (t->used * INTERN_LOAD_DEN >= t->cap * INTERN_LOAD_NUM) {
    if (intern_grow(t) != 0)
      return nullptr;
  }

  char *copy = arena_alloc_aligned(t->arena, len + 1u, _Alignof(char));
  if (!copy)
    return nullptr;
  memcpy(copy, s, len);
  copy[len] = '\0';

  intern_insert(t->slots, t->cap, copy);
  t->used++;
  return copy;
}

const char *intern(InternTable *t, const char *s) {
  assert(s);
  return intern_n(t, s, strlen(s));
}
