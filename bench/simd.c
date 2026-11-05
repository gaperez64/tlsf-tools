// Compile with -O3 and the same CPU flags as the release build. Override the
// include path to compare headers; use several fresh runs and report medians.
#define _POSIX_C_SOURCE 200809L
#include "simd.h"
#include <stdio.h>
#include <time.h>

static volatile uint32_t checksum;

__attribute__((noinline)) static void
word_or(uint64_t *restrict a, const uint64_t *restrict b, uint32_t n) {
  tlsf_words_or(a, b, n);
}

__attribute__((noinline)) static uint32_t word_count(const uint64_t *a,
                                                     uint32_t n) {
  return tlsf_words_popcount(a, n);
}

static double seconds(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

int main(void) {
  static const uint32_t sizes[] = {1, 3, 8, 17, 64, 1000, 4096};
  uint64_t a[4096], b[4096];
  for (uint32_t i = 0; i < 4096; ++i) {
    a[i] = UINT64_C(0x123456789abcdef) * (i + 1);
    b[i] = ~a[i];
  }
  for (unsigned s = 0; s < sizeof sizes / sizeof *sizes; ++s) {
    uint32_t n = sizes[s], iterations = 20000000 / n;
    double start = seconds();
    for (uint32_t j = 0; j < iterations; ++j)
      word_or(a, b, n);
    double or_ns = (seconds() - start) * 1e9 / iterations;
    start = seconds();
    uint32_t sum = 0;
    for (uint32_t j = 0; j < iterations; ++j) {
      // Prevent loop-invariant hoisting without timing volatile array loads.
      __asm__ volatile("" : : "r"(a) : "memory");
      sum += word_count(a, n);
    }
    checksum = sum;
    double count_ns = (seconds() - start) * 1e9 / iterations;
    printf("%u %.3f %.3f\n", n, or_ns, count_ns);
  }
  return checksum == 0;
}
