#ifndef TLSF_OXIDD_RUNTIME_H
#define TLSF_OXIDD_RUNTIME_H

#include <oxidd/capi.h>
#include <stddef.h>

#ifdef __cplusplus
using oxidd::capi::oxidd_bdd_manager_t;
extern "C" {
#endif

/// Shared single-worker constructor; OxiDD owns allocation and thread creation.
oxidd_bdd_manager_t tlsf_oxidd_manager_new(size_t nodes, size_t cache);

#ifdef __cplusplus
}
#endif
#endif
