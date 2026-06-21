#ifndef TLSF_BUILD_INFO_H
#define TLSF_BUILD_INFO_H

#include "build_config.h"
#include "tlsf/simd.h"

static inline const char *tlsf_build_oxidd(void) {
#if TLSF_BUILD_OXIDD
  return "yes";
#else
  return "no";
#endif
}

static inline const char *tlsf_build_research(void) {
#if TLSF_BUILD_RESEARCH
  return "yes";
#else
  return "no";
#endif
}

static inline const char *tlsf_build_simd(void) { return TLSF_SIMD_TIER; }

#endif // TLSF_BUILD_INFO_H
