#include "oxidd_runtime.h"

oxidd_bdd_manager_t tlsf_oxidd_manager_new(size_t nodes, size_t cache) {
  return oxidd_bdd_manager_new(nodes, cache, 1);
}
