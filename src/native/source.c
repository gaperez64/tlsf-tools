#define _GNU_SOURCE
#include "tlsf/pipeline.h"
#include "source_internal.h"

#include "provenance.h"
#include "sha256.h"
#include "diagnostic.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Internal pre-expansion inspection for native lifting. The parser owns the
 * source declaration table; expansion later clears it. */
int tlsf_source_parameter_count(const uint8_t *source, size_t size) {
  if (!source || !size || memchr(source, '\0', size))
    return -1;
  FILE *in = fmemopen((void *)source, size, "r");
  if (!in)
    return -1;
  char *diagnostic = NULL;
  size_t diagnostic_size = 0;
  FILE *capture = open_memstream(&diagnostic, &diagnostic_size);
  if (!capture) {
    fclose(in);
    return -1;
  }
  FILE *previous = tlsf_diagnostic_swap(capture);
  TlsfSpec *spec = cli_parse(in, "tlsf-lift");
  tlsf_diagnostic_swap(previous);
  fclose(capture);
  fclose(in);
  free(diagnostic);
  if (!spec)
    return -1;
  int count = spec->param_count;
  spec_free(spec);
  return count;
}

static int pipeline_error(TlsfPipelineError *error, int result,
                          TlsfPipelineStatus status, const char *stage,
                          const char *message) {
  if (error) {
    *error = (TlsfPipelineError){.status = status};
    snprintf(error->stage, sizeof error->stage, "%s", stage);
    snprintf(error->message, sizeof error->message, "%s", message);
  }
  return result;
}

bool tlsf_pipeline_source_sha256(const void *source, size_t size,
                                 char output[65]) {
  if (!source || !size || !output || memchr(source, '\0', size))
    return false;
  sha256_hex(source, size, output);
  return true;
}

static int expand_spec_impl(TlsfSpec *spec, const ParamOverride *overrides,
                            size_t count, FILE *provenance_out,
                            const char source_sha256[65],
                            bool require_unambiguous_origin,
                            TlsfPipelineError *error) {
  if (!spec || (count && !overrides) ||
      (provenance_out && (!source_sha256 || strlen(source_sha256) != 64)))
    return pipeline_error(error, -1, TLSF_PIPELINE_INVALID, "expand",
                          "invalid argument");
  for (size_t i = 0; i < count; i++) {
    if (!overrides[i].name || !*overrides[i].name)
      return pipeline_error(error, -1, TLSF_PIPELINE_INVALID, "override",
                            "empty parameter name");
    for (size_t j = 0; j < i; j++)
      if (!strcmp(overrides[i].name, overrides[j].name))
        return pipeline_error(error, -1, TLSF_PIPELINE_INVALID, "override",
                              "duplicate parameter override");
    bool found = false;
    for (uint16_t j = 0; j < spec->param_count; j++)
      found |= !strcmp(overrides[i].name, spec->params[j].name);
    if (!found)
      return pipeline_error(error, -1, TLSF_PIPELINE_INVALID, "override",
                            "unknown parameter");
  }
  const ParamDecl *source_params = spec->params;
  uint16_t source_param_count = spec->param_count;
  spec->capture_provenance = provenance_out || require_unambiguous_origin;
  if (expand(spec, overrides, count) != 0)
    return pipeline_error(error, -1, TLSF_PIPELINE_DECLINED, "expand",
                          "TLSF expansion failed");
  if (require_unambiguous_origin && spec->provenance_ambiguous)
    return pipeline_error(error, -2, TLSF_PIPELINE_DECLINED, "provenance",
                          "ambiguous source origin");
  if (provenance_out &&
      provenance_write(provenance_out, spec, source_params, source_param_count,
                       source_sha256) != 0)
    return pipeline_error(error, -3, TLSF_PIPELINE_LIMIT, "provenance",
                          "provenance output failed");
  return pipeline_error(error, 0, TLSF_PIPELINE_OK, "expand", "");
}

int tlsf_pipeline_expand_spec(TlsfSpec *spec, const ParamOverride *overrides,
                              size_t count, FILE *provenance_out,
                              const char source_sha256[65],
                              bool require_unambiguous_origin,
                              TlsfPipelineError *error) {
  char *diagnostic = nullptr;
  size_t size = 0;
  FILE *capture = open_memstream(&diagnostic, &size);
  if (!capture)
    return pipeline_error(error, -1, TLSF_PIPELINE_LIMIT, "expand",
                          "out of memory");
  FILE *previous = tlsf_diagnostic_swap(capture);
  int result =
      expand_spec_impl(spec, overrides, count, provenance_out, source_sha256,
                       require_unambiguous_origin, error);
  tlsf_diagnostic_swap(previous);
  fclose(capture);
  if (result && error && diagnostic && size) {
    while (size && diagnostic[size - 1] == '\n')
      diagnostic[--size] = '\0';
    snprintf(error->message, sizeof error->message, "%s", diagnostic);
  }
  free(diagnostic);
  return result;
}

TlsfPipeline *
tlsf_pipeline_load_bytes_v2(const uint8_t *source, size_t size,
                            const TlsfPipelineOptionsV2 *options) {
  if (options && (options->abi_version != TLSF_PIPELINE_OPTIONS_ABI_VERSION ||
                  options->struct_size != sizeof *options))
    return nullptr;
  char hash[65];
  if (!tlsf_pipeline_source_sha256(source, size, hash)) {
    pipeline_error(options ? options->error : nullptr, -1,
                   TLSF_PIPELINE_INVALID, "source",
                   "invalid source bytes or embedded NUL");
    return nullptr;
  }
  uint8_t *snapshot = malloc(size);
  if (!snapshot) {
    pipeline_error(options ? options->error : nullptr, -1, TLSF_PIPELINE_LIMIT,
                   "source", "out of memory");
    return nullptr;
  }
  memcpy(snapshot, source, size);
  FILE *in = fmemopen(snapshot, size, "r");
  if (!in) {
    free(snapshot);
    pipeline_error(options ? options->error : nullptr, -1, TLSF_PIPELINE_LIMIT,
                   "source", "cannot open source stream");
    return nullptr;
  }
  TlsfPipelineOptionsV2 resolved =
      options ? *options : (TlsfPipelineOptionsV2){0};
  if (!options) {
    resolved.certify = true;
    resolved.template_mask = TPL_ALL;
  }
  resolved.abi_version = TLSF_PIPELINE_OPTIONS_ABI_VERSION;
  resolved.struct_size = sizeof resolved;
  resolved.source_sha256 = hash;
  TlsfPipeline *pipeline = tlsf_pipeline_load_v2(in, &resolved);
  fclose(in);
  if (pipeline) {
    pipeline->source_bytes = snapshot;
    pipeline->source_size = size;
    memcpy(pipeline->source_sha256, hash, sizeof hash);
  } else {
    free(snapshot);
  }
  return pipeline;
}
