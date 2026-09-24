#define _GNU_SOURCE
#include "tlsf/pipeline.h"
#include "diagnostic.h"

#include "tlsf/expand.h"
#include "tlsf/recognize.h"
#include "tlsf/spec.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *pipeline_tool_name(const TlsfPipelineOptionsV2 *opts) {
  return opts && opts->tool_name ? opts->tool_name : "tlsf";
}

static void pipeline_status(const TlsfPipelineOptionsV2 *opts,
                            TlsfPipelineStatus status, const char *stage,
                            const char *message) {
  if (opts && opts->error) {
    *opts->error = (TlsfPipelineError){.status = status};
    snprintf(opts->error->stage, sizeof opts->error->stage, "%s", stage);
    snprintf(opts->error->message, sizeof opts->error->message, "%s", message);
  }
}

static TlsfPipeline *pipeline_load_impl(FILE *fp,
                                        const TlsfPipelineOptionsV2 *opts) {
  if (opts && (opts->abi_version != TLSF_PIPELINE_OPTIONS_ABI_VERSION ||
               opts->struct_size != sizeof *opts))
    return nullptr;
  const char *tool = pipeline_tool_name(opts);
  TlsfPipeline *p = calloc(1, sizeof(*p));
  if (!p) {
    pipeline_status(opts, TLSF_PIPELINE_LIMIT, "pipeline", "out of memory");
    fprintf(tlsf_diagnostic_stream(), "%s: out of memory\n", tool);
    return nullptr;
  }

  p->spec = cli_parse(fp, tool);
  if (!p->spec) {
    pipeline_status(opts, TLSF_PIPELINE_INVALID, "parse", "TLSF parse failed");
    goto fail;
  }

  if (opts && opts->overwrite_semantics &&
      !parse_semantics(opts->overwrite_semantics, &p->spec->info.semantics)) {
    fprintf(tlsf_diagnostic_stream(), "%s: invalid semantics '%s'\n", tool,
            opts->overwrite_semantics);
    pipeline_status(opts, TLSF_PIPELINE_INVALID, "semantics",
                    "invalid semantics override");
    goto fail;
  }
  if (opts && opts->overwrite_target &&
      !parse_target(opts->overwrite_target, &p->spec->info.target)) {
    fprintf(tlsf_diagnostic_stream(), "%s: invalid target '%s'\n", tool,
            opts->overwrite_target);
    pipeline_status(opts, TLSF_PIPELINE_INVALID, "target",
                    "invalid target override");
    goto fail;
  }
  if (!spec_validate_semantics(p->spec, tool)) {
    pipeline_status(opts, TLSF_PIPELINE_DECLINED, "semantics",
                    "unsupported semantics");
    goto fail;
  }

  if (tlsf_pipeline_expand_spec(p->spec, opts ? opts->overrides : nullptr,
                                opts ? opts->n_overrides : 0,
                                opts ? opts->provenance_out : nullptr,
                                opts ? opts->source_sha256 : nullptr,
                                opts && opts->require_unambiguous_origin,
                                opts ? opts->error : nullptr) != 0)
    goto fail;
  if (!spec_adapt_target(p->spec)) {
    pipeline_status(opts, TLSF_PIPELINE_LIMIT, "adapt", "adaptation failed");
    fprintf(tlsf_diagnostic_stream(),
            "%s: semantics/target adaptation failed (OOM)\n", tool);
    goto fail;
  }

  p->cover = cover_build(p->spec, opts && opts->split);
  if (!p->cover) {
    pipeline_status(opts, TLSF_PIPELINE_LIMIT, "cover", "out of memory");
    fprintf(tlsf_diagnostic_stream(), "%s: out of memory\n", tool);
    goto fail;
  }
  recognize_all(p->cover);

  p->csnf = templates_certify(p->cover, opts ? opts->template_mask : TPL_ALL,
                              opts ? opts->certify : true);
  p->composition = p->csnf ? csnf_compose(p->csnf) : nullptr;
  if (!p->csnf || !p->composition) {
    pipeline_status(opts, TLSF_PIPELINE_LIMIT, "compose", "out of memory");
    fprintf(tlsf_diagnostic_stream(), "%s: out of memory\n", tool);
    goto fail;
  }

  pipeline_status(opts, TLSF_PIPELINE_OK, "pipeline", "");
  return p;

fail:
  tlsf_pipeline_free(p);
  return nullptr;
}

TlsfPipeline *tlsf_pipeline_load_v2(FILE *fp,
                                    const TlsfPipelineOptionsV2 *opts) {
  char *diagnostic = nullptr;
  size_t size = 0;
  FILE *capture = open_memstream(&diagnostic, &size);
  if (!capture) {
    pipeline_status(opts, TLSF_PIPELINE_LIMIT, "diagnostic", "out of memory");
    return nullptr;
  }
  FILE *previous = tlsf_diagnostic_swap(capture);
  TlsfPipeline *result = pipeline_load_impl(fp, opts);
  tlsf_diagnostic_swap(previous);
  fclose(capture);
  if (!result && opts && opts->error && diagnostic && size) {
    while (size && diagnostic[size - 1] == '\n')
      diagnostic[--size] = '\0';
    snprintf(opts->error->message, sizeof opts->error->message, "%s",
             diagnostic);
  }
  free(diagnostic);
  return result;
}

void tlsf_pipeline_free(TlsfPipeline *p) {
  if (!p)
    return;
  csnf_composition_free(p->composition);
  csnf_free(p->csnf);
  spec_free(p->spec);
  free((void *)p->source_bytes);
  free(p);
}

TlsfPipeline *tlsf_pipeline_load(FILE *fp, const TlsfPipelineOptions *options) {
  TlsfPipelineOptionsV2 converted = {0};
  if (options)
    memcpy(&converted, options, sizeof *options);
  converted.abi_version = TLSF_PIPELINE_OPTIONS_ABI_VERSION;
  converted.struct_size = sizeof converted;
  return tlsf_pipeline_load_v2(fp, options ? &converted : nullptr);
}
