#ifndef TLSF_SIMD_H
#define TLSF_SIMD_H

// Word-array kernels use portable loops; the compiler chooses vector width
// from the -Dcpu target. No alignment beyond uint64_t is required. The tier
// reports the compiler target, not a fixed kernel width or runtime dispatch.
// "scalar" is the historical baseline label (the ABI may still allow SIMD).
#include <stdint.h>

#if defined(__AVX512F__)
#define TLSF_SIMD_TIER "avx512"
#elif defined(__AVX2__)
#define TLSF_SIMD_TIER "avx2"
#elif defined(__SSE2__) && defined(__POPCNT__) && defined(__SSE4_2__)
#define TLSF_SIMD_TIER "x86-64-v2"
#elif defined(__ARM_NEON) || defined(__aarch64__)
#define TLSF_SIMD_TIER "neon"
#else
#define TLSF_SIMD_TIER "scalar"
#endif

/// Compiler-selected width; no alignment or register-width assumptions.
static inline void tlsf_words_or(uint64_t *restrict dst,
                                 const uint64_t *restrict src, uint32_t n) {
  // A common AP set fits in one word. Keep that case cheap at every target.
  if (n == 1) {
    dst[0] |= src[0];
    return;
  }
  for (uint32_t i = 0; i < n; ++i)
    dst[i] |= src[i];
}

static inline uint32_t tlsf_words_popcount(const uint64_t *words, uint32_t n) {
  uint64_t acc = 0;
  for (uint32_t i = 0; i < n; ++i)
    acc += (uint64_t)__builtin_popcountll(words[i]);
  return (uint32_t)acc;
}
#endif
