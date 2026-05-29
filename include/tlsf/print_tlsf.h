#ifndef TLSF_PRINT_TLSF_H
#define TLSF_PRINT_TLSF_H

/// print_tlsf.h — emit a TlsfSpec as TLSF.
///
/// With include_global=false the output is *basic* TLSF: INFO block + MAIN
/// block with INPUTS, OUTPUTS, and the six formula subsections, with all
/// parameters and definitions expanded away (use after expand()).
///
/// With include_global=true the GLOBAL section (PARAMETERS + DEFINITIONS) is
/// preserved, so a parsed-but-unexpanded spec can be re-emitted faithfully —
/// e.g. to substitute parameter values without expanding the rest.
///
/// The output is valid TLSF that can be re-parsed by this tool or by syfco.

#include "tlsf/spec.h"
#include <stdbool.h>
#include <stdio.h>

void print_tlsf(FILE *out, const TlsfSpec *spec, bool include_global);

#endif // TLSF_PRINT_TLSF_H
