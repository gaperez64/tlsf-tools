#ifndef TLSF_PROVENANCE_H
#define TLSF_PROVENANCE_H

#include "tlsf/convert.h"
#include "tlsf/spec.h"
#include <stdio.h>

typedef struct ValueOriginCapture {
  Arena *arena;
  TlsfValueOrigins *record;
  size_t remaining;
  uint64_t *bit_operand_bound;
  uint32_t formula_id;
  TlsfValueSection section;
} ValueOriginCapture;

void value_origin_capture_init(ValueOriginCapture *capture);
void value_origin_buses(const TlsfSpec *spec);
bool value_origin_dependencies(
    const TlsfSpec *spec, const Node *const *nodes, size_t count,
    bool (*bound)(Arena *, const void *, const char *), const void *scope,
    const uint16_t **ids, uint16_t *id_count);

// Write the expanded, source-anchored instance. The SHA is over input bytes.
int provenance_write(FILE *out, const TlsfSpec *spec, const ParamDecl *params,
                     uint16_t param_count, const DefDecl *defs,
                     uint16_t def_count, const char source_sha256[65]);

#endif
