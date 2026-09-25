#define _GNU_SOURCE
#include "tlsf/pipeline.h"
#include "diagnostic.h"

#include "tlsf/expand.h"
#include "tlsf/recognize.h"
#include "tlsf/spec.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *pipeline_tool_name(const TlsfPipelineOptions *opts) {
  return opts && opts->tool_name ? opts->tool_name : "tlsf";
}

static void pipeline_status(const TlsfPipelineOptions *opts,
                            TlsfPipelineStatus status, const char *stage,
                            const char *message) {
  if (opts && opts->error) {
    *opts->error = (TlsfPipelineError){.status = status};
    snprintf(opts->error->stage, sizeof opts->error->stage, "%s", stage);
    snprintf(opts->error->message, sizeof opts->error->message, "%s", message);
  }
}

static TlsfPipeline *pipeline_load_impl(FILE *fp,
                                        const TlsfPipelineOptions *opts) {
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

  char *provenance_buffer = nullptr;
  size_t provenance_size = 0;
  FILE *provenance_stream =
      opts && opts->source_sha256
          ? open_memstream(&provenance_buffer, &provenance_size)
          : nullptr;
  if (opts && opts->source_sha256 && !provenance_stream) {
    pipeline_status(opts, TLSF_PIPELINE_LIMIT, "provenance", "out of memory");
    goto fail;
  }
  if (tlsf_pipeline_expand_spec(p->spec, opts ? opts->overrides : nullptr,
                                opts ? opts->n_overrides : 0,
                                provenance_stream ? provenance_stream
                                : opts            ? opts->provenance_out
                                                  : nullptr,
                                opts ? opts->source_sha256 : nullptr,
                                opts && opts->require_unambiguous_origin,
                                opts ? opts->error : nullptr) != 0) {
    if (provenance_stream)
      fclose(provenance_stream);
    free(provenance_buffer);
    goto fail;
  }
  if (provenance_stream) {
    if (fclose(provenance_stream) != 0) {
      free(provenance_buffer);
      pipeline_status(opts, TLSF_PIPELINE_LIMIT, "provenance", "output failed");
      goto fail;
    }
    p->frontend_provenance_json = provenance_buffer;
    p->frontend_provenance_size = provenance_size;
    if (opts->provenance_out &&
        fwrite(provenance_buffer, 1, provenance_size, opts->provenance_out) !=
            provenance_size) {
      pipeline_status(opts, TLSF_PIPELINE_LIMIT, "provenance", "output failed");
      goto fail;
    }
  }
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

TlsfPipeline *tlsf_pipeline_load(FILE *fp, const TlsfPipelineOptions *opts) {
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
  free(p->frontend_provenance_json);
  free(p);
}
