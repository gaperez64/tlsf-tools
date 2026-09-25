#ifndef TLSF_PROVENANCE_H
#define TLSF_PROVENANCE_H

#include "tlsf/spec.h"
#include <stdio.h>

// Write the expanded, source-anchored instance. The SHA is over input bytes.
int provenance_write(FILE *out, const TlsfSpec *spec, const ParamDecl *params,
                     uint16_t param_count, const char source_sha256[65]);

#endif
