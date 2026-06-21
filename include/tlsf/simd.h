#ifndef TLSF_SIMD_H
#define TLSF_SIMD_H

/// simd.h — compile-time CPU-ISA selection for the small word-array kernels.
///
/// The build picks one ISA tier via -Dcpu=... (see meson.build): the matching
/// `-m` flag makes the compiler predefine __AVX512F__ / __AVX2__ /
/// __POPCNT__+__SSE4_2__ / __ARM_NEON, which selects the corresponding branch
/// below.  Every kernel has a portable scalar fallback, so omitting -Dcpu
/// (baseline) is always correct.
///
/// These are deliberately tiny, branch-free reductions over uint64 word arrays
/// (bitset union / popcount / popcount-of-AND).  The vector paths process
/// several words per step; a scalar tail handles the remainder.  The dominant
/// preprocessor cost is elsewhere (the OxiDD BDD engine, AST expansion), so the
/// real win from -Dcpu is whole-tree auto-vectorization + cross-TU inlining;
/// these intrinsics make the bitset reductions explicit and ISA-portable.

#include <stdint.h>

#if defined(__AVX512F__)
#include <immintrin.h>
#define TLSF_SIMD_TIER "avx512"
#elif defined(__AVX2__)
#include <immintrin.h>
#define TLSF_SIMD_TIER "avx2"
#elif defined(__SSE2__) && defined(__POPCNT__) && defined(__SSE4_2__)
#include <emmintrin.h>
#define TLSF_SIMD_TIER "x86-64-v2"
#define TLSF_SIMD_SSE2 1
#elif defined(__ARM_NEON) || defined(__aarch64__)
#include <arm_neon.h>
#define TLSF_SIMD_TIER "neon"
#else
#define TLSF_SIMD_TIER "scalar"
#endif

/// dst[i] |= src[i] for i in [0, n).
static inline void tlsf_words_or(uint64_t *restrict dst,
                                 const uint64_t *restrict src, uint32_t n) {
  uint32_t i = 0;
#if defined(__AVX512F__)
  for (; i + 8 <= n; i += 8) {
    __m512i d = _mm512_loadu_si512((const void *)(dst + i));
    __m512i s = _mm512_loadu_si512((const void *)(src + i));
    _mm512_storeu_si512((void *)(dst + i), _mm512_or_si512(d, s));
  }
#elif defined(__AVX2__)
  for (; i + 4 <= n; i += 4) {
    __m256i d = _mm256_loadu_si256((const __m256i *)(dst + i));
    __m256i s = _mm256_loadu_si256((const __m256i *)(src + i));
    _mm256_storeu_si256((__m256i *)(dst + i), _mm256_or_si256(d, s));
  }
#elif defined(TLSF_SIMD_SSE2)
  for (; i + 2 <= n; i += 2) {
    __m128i d = _mm_loadu_si128((const __m128i *)(dst + i));
    __m128i s = _mm_loadu_si128((const __m128i *)(src + i));
    _mm_storeu_si128((__m128i *)(dst + i), _mm_or_si128(d, s));
  }
#elif defined(__ARM_NEON) || defined(__aarch64__)
  for (; i + 2 <= n; i += 2)
    vst1q_u64(dst + i, vorrq_u64(vld1q_u64(dst + i), vld1q_u64(src + i)));
#endif
  for (; i < n; i++)
    dst[i] |= src[i];
}

/// Population count of words[0..n).
static inline uint32_t tlsf_words_popcount(const uint64_t *words, uint32_t n) {
  uint64_t acc = 0;
  uint32_t i = 0;
#if defined(__AVX512F__) && defined(__AVX512VPOPCNTDQ__)
  __m512i v = _mm512_setzero_si512();
  for (; i + 8 <= n; i += 8)
    v = _mm512_add_epi64(
        v, _mm512_popcnt_epi64(_mm512_loadu_si512((const void *)(words + i))));
  uint64_t tmp[8];
  _mm512_storeu_si512((void *)tmp, v);
  for (int k = 0; k < 8; k++)
    acc += tmp[k];
#elif defined(__ARM_NEON) || defined(__aarch64__)
  for (; i + 2 <= n; i += 2) {
    uint8x16_t c = vcntq_u8(vreinterpretq_u8_u64(vld1q_u64(words + i)));
    acc += vaddlvq_u8(c);
  }
#endif
  for (; i < n; i++)
    acc += (uint64_t)__builtin_popcountll(words[i]);
  return (uint32_t)acc;
}

/// Population count of (a[i] & b[i]) for i in [0, n) — |a ∩ b|.
static inline uint32_t tlsf_words_and_popcount(const uint64_t *a,
                                               const uint64_t *b, uint32_t n) {
  uint64_t acc = 0;
  uint32_t i = 0;
#if defined(__AVX512F__) && defined(__AVX512VPOPCNTDQ__)
  __m512i v = _mm512_setzero_si512();
  for (; i + 8 <= n; i += 8) {
    __m512i x = _mm512_and_si512(_mm512_loadu_si512((const void *)(a + i)),
                                 _mm512_loadu_si512((const void *)(b + i)));
    v = _mm512_add_epi64(v, _mm512_popcnt_epi64(x));
  }
  uint64_t tmp[8];
  _mm512_storeu_si512((void *)tmp, v);
  for (int k = 0; k < 8; k++)
    acc += tmp[k];
#elif defined(__ARM_NEON) || defined(__aarch64__)
  for (; i + 2 <= n; i += 2) {
    uint64x2_t x = vandq_u64(vld1q_u64(a + i), vld1q_u64(b + i));
    acc += vaddlvq_u8(vcntq_u8(vreinterpretq_u8_u64(x)));
  }
#endif
  for (; i < n; i++)
    acc += (uint64_t)__builtin_popcountll(a[i] & b[i]);
  return (uint32_t)acc;
}

#endif // TLSF_SIMD_H
