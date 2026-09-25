// Keep the project-owned host-allocation boundary in its own translation unit
// so failure-injection link wrappers also intercept allocations made by
// oxidd_common.c itself.

#include "oxidd_common.h"

#include <stdlib.h>

void *oxidd_host_realloc(void *ptr, size_t size) { return realloc(ptr, size); }
void *oxidd_host_calloc(size_t count, size_t size) {
  return calloc(count, size);
}
