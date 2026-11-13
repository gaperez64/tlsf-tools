#ifndef TLSF_NORMALIZE_INTERNAL_H
#define TLSF_NORMALIZE_INTERNAL_H

#include "tlsf/normalize.h"

// List-level split with the same per-invocation telemetry as formula passes.
uint32_t tlsf_normalize_split(Arena *a, Node *root, Node ***out, bool pre,
                              TlsfNormStats *stats);

#endif
