#ifndef TLSF_FUZZ_CHECK_H
#define TLSF_FUZZ_CHECK_H
#include <stdlib.h>

#ifdef FUZZ_REPLAY
#include <stdio.h>

// One inventory: adding a CHECK requires an ID here; replay checks all IDs.
// clang-format off
#define FUZZ_CHECKS(X) \
  X(R1) X(R2) X(R3) \
  X(A1) X(A2) X(A3) X(A4) X(A5) X(A6) X(A7) X(A8) \
  X(D1) X(D2) X(D3) X(D4) X(D6) X(D7) X(D8) X(D9) X(D10) X(D11) X(D12) \
  X(C1) X(C2) X(C3) X(C4) X(C5) X(C6) X(C7) X(C8)
// clang-format on
#define FUZZ_ENUM(id) id,
typedef enum { FUZZ_CHECKS(FUZZ_ENUM) FUZZ_CHECK_COUNT } FuzzCheck;
#undef FUZZ_ENUM

// Only replay builds record hits and print check IDs.
void fuzz_check_hit(FuzzCheck id);
#define CHECK(id, cond)                                                        \
  do {                                                                         \
    fuzz_check_hit(id);                                                        \
    if (!(cond)) {                                                             \
      fprintf(stderr, "CHECK %s failed\n", #id);                               \
      abort();                                                                 \
    }                                                                          \
  } while (0)
#else
#define CHECK(id, cond)                                                        \
  do {                                                                         \
    if (!(cond))                                                               \
      abort();                                                                 \
  } while (0)
#endif
#endif
