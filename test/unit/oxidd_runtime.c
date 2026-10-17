#define _POSIX_C_SOURCE 200809L
#include "tlsf/process.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>

int main(int argc, char **argv) {
  assert(argc == 2);
  unsigned long mib = strtoul(argv[1], nullptr, 10);
  rlim_t bound = mib ? (rlim_t)mib * 1024 * 1024 : RLIM_INFINITY;
  struct rlimit limit = {bound, bound};
  assert(setrlimit(RLIMIT_AS, &limit) == 0);
  assert(unsetenv("OXIDD_STACK_SIZE") == 0);
  assert(tlsf_oxidd_configure_process_stack() == 0);
  if (mib) {
    unsigned long expected = mib * 1024 * 1024 / 16;
    if (expected < 8 * 1024 * 1024)
      expected = 8 * 1024 * 1024;
    if (expected > 1024 * 1024 * 1024)
      expected = 1024 * 1024 * 1024;
    char value[32];
    snprintf(value, sizeof value, "%lu", expected);
    assert(strcmp(getenv("OXIDD_STACK_SIZE"), value) == 0);
  } else {
    assert(getenv("OXIDD_STACK_SIZE") == nullptr);
  }
  // Run only before threads exist; leave every explicit value to OxiDD.
  const char *values[] = {"+8388608", "1099511627776", "invalid", ""};
  for (size_t i = 0; i < sizeof values / sizeof *values; ++i) {
    assert(setenv("OXIDD_STACK_SIZE", values[i], 1) == 0);
    assert(tlsf_oxidd_configure_process_stack() == 0);
    assert(strcmp(getenv("OXIDD_STACK_SIZE"), values[i]) == 0);
  }
  return 0;
}
