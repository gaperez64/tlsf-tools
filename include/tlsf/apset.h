#ifndef TLSF_APSET_H
#define TLSF_APSET_H

/// apset.h — atomic-proposition index table and bitsets over it.
///
/// `ApTable` assigns a dense index to each (interned) atomic-proposition name;
/// signals are interned first so input/output flags are known.  `ApSet` is a
/// fixed-width bitset over those indices, used for a constraint's input/output
/// support, occurrence polarity, and current/next timing.
///
/// All storage is arena-allocated (one arena_free tears everything down).

#include "tlsf/arena.h"
#include <stdbool.h>
#include <stdint.h>

enum { AP_FLAG_INPUT = 1u << 0, AP_FLAG_OUTPUT = 1u << 1 };

typedef struct {
  Arena *arena;
  const char **names; ///< index -> interned name (insertion order)
  uint8_t *flags;     ///< per-index AP_FLAG_* bits
  uint32_t count;
  uint32_t cap;
  uint32_t *hash; ///< open-addressing: idx+1 (0 = empty), size hcap (pow2)
  uint32_t hcap;
} ApTable;

void ap_table_init(ApTable *t, Arena *a);

/// Intern `name` (interned pointer), returning its dense index; `flags` is
/// OR-ed into the entry's flags (pass 0 for a plain occurrence).
uint32_t ap_table_intern(ApTable *t, const char *name, uint8_t flags);

/// Index of `name`, or -1 if absent.
int32_t ap_table_find(const ApTable *t, const char *name);

static inline const char *ap_table_name(const ApTable *t, uint32_t idx) {
  return t->names[idx];
}
static inline uint8_t ap_table_flags(const ApTable *t, uint32_t idx) {
  return t->flags[idx];
}

typedef struct {
  uint64_t *words;
  uint32_t nbits;
} ApSet;

void apset_init(ApSet *s, Arena *a, uint32_t nbits);
static inline void apset_set(ApSet *s, uint32_t i) {
  s->words[i >> 6] |= (uint64_t)1 << (i & 63);
}
static inline bool apset_test(const ApSet *s, uint32_t i) {
  return (s->words[i >> 6] >> (i & 63)) & 1u;
}
void apset_union(ApSet *dst, const ApSet *src);
uint32_t apset_count(const ApSet *s);

#endif // TLSF_APSET_H
