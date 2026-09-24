#ifndef TLSF_NATIVE_H
#define TLSF_NATIVE_H

/* ABI umbrella for the existing TLSF pipeline and GR(1) solver, plus the
 * independent checker. No second parse or solve object model is defined. */
#define TLSF_NATIVE_ABI_VERSION 1
#include "tlsf/pipeline.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/gr1_check.h"

#endif
