#define _POSIX_C_SOURCE 200809L
#include "tlsf/process.h"

#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>

int tlsf_oxidd_configure_process_stack(void) {
#ifdef RLIMIT_AS
  if (getenv("OXIDD_STACK_SIZE"))
    return 0;
  struct rlimit limit;
  if (getrlimit(RLIMIT_AS, &limit))
    return -1;
  if (limit.rlim_cur != RLIM_INFINITY) {
    rlim_t stack = limit.rlim_cur / 16;
    if (stack < 8 * 1024 * 1024)
      stack = 8 * 1024 * 1024;
    if (stack > 1024 * 1024 * 1024)
      stack = 1024 * 1024 * 1024;
    char value[32];
    snprintf(value, sizeof value, "%llu", (unsigned long long)stack);
    return setenv("OXIDD_STACK_SIZE", value, 0);
  }
#endif
  return 0;
}
