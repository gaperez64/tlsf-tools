#ifndef TLSF_PIPELINE_SOURCE_INTERNAL_H
#define TLSF_PIPELINE_SOURCE_INTERNAL_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Count declarations in the parsed, unexpanded source. -1 means parse failure. */
int tlsf_source_parameter_count(const uint8_t *source, size_t size);

#ifdef __cplusplus
}
#endif
#endif
