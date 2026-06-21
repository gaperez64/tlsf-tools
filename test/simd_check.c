#include "tlsf/simd.h"

#include <stdint.h>
#include <stdio.h>

#define MAX_WORDS 1000

static uint64_t next_word(uint64_t *state) {
  *state =
      *state * UINT64_C(6364136223846793005) + UINT64_C(1442695040888963407);
  return *state ^ (*state >> 29);
}

static uint32_t scalar_popcount(const uint64_t *words, uint32_t n) {
  uint32_t acc = 0;
  for (uint32_t i = 0; i < n; i++)
    acc += (uint32_t)__builtin_popcountll(words[i]);
  return acc;
}

static uint32_t scalar_and_popcount(const uint64_t *a, const uint64_t *b,
                                    uint32_t n) {
  uint32_t acc = 0;
  for (uint32_t i = 0; i < n; i++)
    acc += (uint32_t)__builtin_popcountll(a[i] & b[i]);
  return acc;
}

int main(void) {
  static const uint32_t sizes[] = {0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 1000};
  uint64_t a[MAX_WORDS];
  uint64_t b[MAX_WORDS];
  uint64_t dst[MAX_WORDS];
  uint64_t expect[MAX_WORDS];

  for (uint32_t si = 0; si < sizeof(sizes) / sizeof(sizes[0]); si++) {
    uint32_t n = sizes[si];
    uint64_t state = UINT64_C(0x9e3779b97f4a7c15) ^ n;
    for (uint32_t i = 0; i < n; i++) {
      a[i] = next_word(&state);
      b[i] = next_word(&state);
      dst[i] = next_word(&state);
      expect[i] = dst[i] | b[i];
    }

    tlsf_words_or(dst, b, n);
    for (uint32_t i = 0; i < n; i++) {
      if (dst[i] != expect[i]) {
        fprintf(stderr, "tlsf_words_or mismatch n=%u i=%u\n", n, i);
        return 1;
      }
    }

    uint32_t got_pop = tlsf_words_popcount(a, n);
    uint32_t expect_pop = scalar_popcount(a, n);
    if (got_pop != expect_pop) {
      fprintf(stderr, "tlsf_words_popcount mismatch n=%u got=%u expect=%u\n", n,
              got_pop, expect_pop);
      return 1;
    }

    uint32_t got_and = tlsf_words_and_popcount(a, b, n);
    uint32_t expect_and = scalar_and_popcount(a, b, n);
    if (got_and != expect_and) {
      fprintf(stderr,
              "tlsf_words_and_popcount mismatch n=%u got=%u expect=%u\n", n,
              got_and, expect_and);
      return 1;
    }
  }

  printf("simd=%s ok\n", TLSF_SIMD_TIER);
  return 0;
}
