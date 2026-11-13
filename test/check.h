#ifndef TLSF_TEST_CHECK_H
#define TLSF_TEST_CHECK_H

#include <stdio.h>
#include <stdlib.h>

// Keep predicates and their side effects in every build. Never change NDEBUG:
// production headers must see the same configuration as the linked library.
#define CHECK(expr)                                                            \
  do {                                                                         \
    if (!(expr)) {                                                             \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #expr); \
      exit(EXIT_FAILURE);                                                      \
    }                                                                          \
  } while (0)

#endif
