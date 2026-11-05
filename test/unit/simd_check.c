#include "simd.h"

#include <stdint.h>
#include <stdio.h>

#define MAX_WORDS 1000

static uint64_t next_word(uint64_t *state) {
  *state =
      *state * UINT64_C(6364136223846793005) + UINT64_C(1442695040888963407);
  return *state ^ (*state >> 29);
}

// An independent bit-by-bit reference, rather than the kernel's builtin.
static uint32_t scalar_popcount(uint64_t word) {
  uint32_t acc = 0;
  for (unsigned i = 0; i < 64; ++i)
    acc += (uint32_t)((word >> i) & 1u);
  return acc;
}

int main(void) {
  uint64_t a[MAX_WORDS + 9], b[MAX_WORDS + 9];
  uint64_t dst[MAX_WORDS + 9], expect[MAX_WORDS + 9];
  uint32_t counts[MAX_WORDS + 1];
  tlsf_words_or(NULL, NULL, 0);
  if (tlsf_words_popcount(NULL, 0) != 0)
    return 1;
  // Every length and every word alignment modulo 64 bytes: covers all tails
  // for 128/256/512-bit vectors, without assuming one of those widths.
  for (unsigned pattern = 0; pattern < 4; ++pattern) {
    for (uint32_t offset = 0; offset < 8; ++offset) {
      uint64_t state = UINT64_C(0x9e3779b97f4a7c15) ^ offset;
      for (uint32_t i = 0; i < MAX_WORDS + 9; ++i) {
        a[i] = pattern == 0   ? 0
               : pattern == 1 ? UINT64_MAX
               : pattern == 2 ? UINT64_C(0x5555555555555555)
                              : next_word(&state);
        b[i] = next_word(&state);
      }
      counts[0] = 0;
      for (uint32_t i = 0; i < MAX_WORDS; ++i)
        counts[i + 1] = counts[i] + scalar_popcount(a[offset + i]);
      for (uint32_t n = 0; n <= MAX_WORDS; ++n) {
        for (uint32_t i = 0; i < MAX_WORDS + 9; ++i) {
          dst[i] = a[i];
          expect[i] = i >= offset && i < offset + n ? a[i] | b[i] : a[i];
        }
        tlsf_words_or(dst + offset, b + offset, n);
        for (uint32_t i = 0; i < MAX_WORDS + 9; ++i)
          if (dst[i] != expect[i]) {
            fprintf(stderr, "tlsf_words_or mismatch n=%u offset=%u i=%u\n", n,
                    offset, i);
            return 1;
          }
        uint32_t got = tlsf_words_popcount(a + offset, n);
        if (got != counts[n]) {
          fprintf(stderr, "tlsf_words_popcount mismatch n=%u offset=%u\n", n,
                  offset);
          return 1;
        }
      }
    }
  }

  printf("simd=%s ok\n", TLSF_SIMD_TIER);
  return 0;
}
