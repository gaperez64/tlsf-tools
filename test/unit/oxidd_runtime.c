#define _POSIX_C_SOURCE 200809L
#include "oxidd_runtime.h"

#include <assert.h>
#include <stdlib.h>
#include <sys/resource.h>

// Under a finite RLIMIT_AS OxiDD sizes its worker stacks to fit; an explicit
// stack it cannot map yields an invalid manager instead of an abort.
int main(int argc, char **argv) {
  assert(argc == 2);
  unsigned long mib = strtoul(argv[1], nullptr, 10);
  rlim_t bound = mib ? (rlim_t)mib * 1024 * 1024 : RLIM_INFINITY;
  struct rlimit limit = {bound, bound};
  assert(setrlimit(RLIMIT_AS, &limit) == 0);
  assert(unsetenv("OXIDD_STACK_SIZE") == 0);
  oxidd_bdd_manager_t m = tlsf_oxidd_manager_new(1u << 10, 1u << 10);
  assert(m._p);
  oxidd_bdd_manager_unref(m);
  if (mib) {
    assert(setenv("OXIDD_STACK_SIZE", "1099511627776", 1) == 0);
    m = tlsf_oxidd_manager_new(1u << 10, 1u << 10);
    assert(!m._p);
  }
  return 0;
}
