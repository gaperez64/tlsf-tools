#ifndef TLSF_PIPELINE_H
#define TLSF_PIPELINE_H

#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/templates.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
  TLSF_PIPELINE_OK,
  TLSF_PIPELINE_INVALID,
  TLSF_PIPELINE_DECLINED,
  TLSF_PIPELINE_LIMIT,
} TlsfPipelineStatus;

typedef struct {
  TlsfPipelineStatus status;
  char stage[48], message[256];
} TlsfPipelineError;

typedef struct {
  bool split;
  bool certify;
  unsigned template_mask;
  const char *overwrite_semantics;
  const char *overwrite_target;
  ParamOverride *overrides;
  size_t n_overrides;
  const char *tool_name;
} TlsfPipelineOptions;

#define TLSF_PIPELINE_OPTIONS_ABI_VERSION 2
typedef struct {
  bool split;
  bool certify;
  unsigned template_mask;
  const char *overwrite_semantics;
  const char *overwrite_target;
  ParamOverride *overrides;
  size_t n_overrides;
  const char *tool_name;
  uint32_t abi_version;
  size_t struct_size;
  FILE *provenance_out;
  const char *source_sha256;
  bool require_unambiguous_origin;
  TlsfPipelineError *error;
} TlsfPipelineOptionsV2;

typedef struct {
  TlsfSpec *spec;
  ConstraintCover *cover;
  Csnf *csnf;
  CsnfComposition *composition;
  /* Owned, immutable source snapshot when loaded with load_bytes. */
  const uint8_t *source_bytes;
  size_t source_size;
  char source_sha256[65];
} TlsfPipeline;

[[nodiscard]] TlsfPipeline *tlsf_pipeline_load(FILE *fp,
                                               const TlsfPipelineOptions *opts);
[[nodiscard]] TlsfPipeline *
tlsf_pipeline_load_v2(FILE *fp, const TlsfPipelineOptionsV2 *opts);
[[nodiscard]] TlsfPipeline *
tlsf_pipeline_load_bytes_v2(const uint8_t *source, size_t size,
                            const TlsfPipelineOptionsV2 *opts);
/* Hash an immutable source snapshot. Embedded NUL is rejected. */
bool tlsf_pipeline_source_sha256(const void *source, size_t size,
                                 char output[65]);
/* Expand an already parsed spec and optionally emit frontend provenance v1. */
int tlsf_pipeline_expand_spec(TlsfSpec *spec, const ParamOverride *overrides,
                              size_t count, FILE *provenance_out,
                              const char source_sha256[65],
                              bool require_unambiguous_origin,
                              TlsfPipelineError *error);
void tlsf_pipeline_free(TlsfPipeline *p);

#ifdef __cplusplus
}
#endif

#endif // TLSF_PIPELINE_H
