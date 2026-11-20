#ifndef TLSF_PIPELINE_SOURCE_INTERNAL_H
#define TLSF_PIPELINE_SOURCE_INTERNAL_H

#include <stddef.h>
#include <stdint.h>
#include "tlsf/pipeline.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Count declarations in the parsed, unexpanded source. -1 means parse failure.
 */
int tlsf_source_parameter_count(const uint8_t *source, size_t size);

/* Reduction consumes the expanded spec and provenance, not cover/templates. */
TlsfPipeline *tlsf_pipeline_load_frontend(FILE *in,
                                          const TlsfPipelineOptions *options);
TlsfPipeline *
tlsf_pipeline_load_frontend_bytes(const uint8_t *source, size_t size,
                                  const TlsfPipelineOptions *options);

#ifdef __cplusplus
}
#endif
#endif
