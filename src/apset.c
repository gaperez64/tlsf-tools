#include "tlsf/apset.h"

#include "tlsf/simd.h"

// ---------------------------------------------------------------------------
// AP index table (pointer-keyed; names are interned so they compare by pointer)
// ---------------------------------------------------------------------------

void ap_table_init(ApTable *t, Arena *a) {
  t->arena = a;
  t->names = nullptr;
  t->flags = nullptr;
  t->count = 0;
  t->cap = 0;
  t->hash = nullptr;
  t->hcap = 0;
}

static uint32_t ptr_hash(const char *p) {
  // Mix the pointer bits (Fibonacci hashing).
  uint64_t x = (uint64_t)(uintptr_t)p;
  x *= 0x9E3779B97F4A7C15ull;
  return (uint32_t)(x >> 32);
}

static void rehash(ApTable *t, uint32_t new_hcap) {
  uint32_t *h = ARENA_ALLOC_N(t->arena, uint32_t, new_hcap);
  for (uint32_t i = 0; i < new_hcap; i++)
    h[i] = 0;
  for (uint32_t i = 0; i < t->count; i++) {
    uint32_t mask = new_hcap - 1;
    uint32_t j = ptr_hash(t->names[i]) & mask;
    while (h[j])
      j = (j + 1) & mask;
    h[j] = i + 1;
  }
  t->hash = h;
  t->hcap = new_hcap;
}

int32_t ap_table_find(const ApTable *t, const char *name) {
  if (t->hcap == 0)
    return -1;
  uint32_t mask = t->hcap - 1;
  uint32_t j = ptr_hash(name) & mask;
  while (t->hash[j]) {
    uint32_t idx = t->hash[j] - 1;
    if (t->names[idx] == name)
      return (int32_t)idx;
    j = (j + 1) & mask;
  }
  return -1;
}

uint32_t ap_table_intern(ApTable *t, const char *name, uint8_t flags) {
  int32_t found = ap_table_find(t, name);
  if (found >= 0) {
    t->flags[found] |= flags;
    return (uint32_t)found;
  }

  // Grow the dense arrays (copy-on-grow, arena-backed).
  if (t->count == t->cap) {
    uint32_t new_cap = t->cap ? t->cap * 2u : 16u;
    const char **nn = ARENA_ALLOC_N(t->arena, const char *, new_cap);
    uint8_t *nf = ARENA_ALLOC_N(t->arena, uint8_t, new_cap);
    for (uint32_t i = 0; i < t->count; i++) {
      nn[i] = t->names[i];
      nf[i] = t->flags[i];
    }
    t->names = nn;
    t->flags = nf;
    t->cap = new_cap;
  }
  uint32_t idx = t->count++;
  t->names[idx] = name;
  t->flags[idx] = flags;

  // Keep the hash table at <= 50% load.
  if (t->count * 2u > t->hcap)
    rehash(t, t->hcap ? t->hcap * 2u : 32u);
  else {
    uint32_t mask = t->hcap - 1;
    uint32_t j = ptr_hash(name) & mask;
    while (t->hash[j])
      j = (j + 1) & mask;
    t->hash[j] = idx + 1;
  }
  return idx;
}

// ---------------------------------------------------------------------------
// Bitset
// ---------------------------------------------------------------------------

void apset_init(ApSet *s, Arena *a, uint32_t nbits) {
  uint32_t nwords = (nbits + 63) / 64;
  if (nwords == 0)
    nwords = 1;
  s->words = ARENA_ALLOC_N(a, uint64_t, nwords);
  for (uint32_t i = 0; i < nwords; i++)
    s->words[i] = 0;
  s->nbits = nbits;
}

void apset_union(ApSet *dst, const ApSet *src) {
  uint32_t nwords = (dst->nbits + 63) / 64;
  tlsf_words_or(dst->words, src->words, nwords);
}

uint32_t apset_count(const ApSet *s) {
  uint32_t nwords = (s->nbits + 63) / 64;
  return tlsf_words_popcount(s->words, nwords);
}
