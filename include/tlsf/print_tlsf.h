#ifndef TLSF_PRINT_TLSF_H
#define TLSF_PRINT_TLSF_H

/// print_tlsf.h — emit a TlsfSpec as basic TLSF.
///
/// Basic TLSF = INFO block + MAIN block with INPUTS, OUTPUTS, and the six
/// formula subsections.  No GLOBAL section (all parameters and definitions
/// have been expanded away by expand()).
///
/// The output is valid TLSF that can be re-parsed by this tool or by syfco.

#include "tlsf/spec.h"
#include <stdio.h>

void print_tlsf(FILE *out, const TlsfSpec *spec);

#endif // TLSF_PRINT_TLSF_H
