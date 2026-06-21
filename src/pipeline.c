#include "tlsf/pipeline.h"

#include "tlsf/expand.h"
#include "tlsf/recognize.h"
#include "tlsf/spec.h"

#include <stdio.h>
#include <stdlib.h>

static const char *pipeline_tool_name(const TlsfPipelineOptions *opts) {
  return opts && opts->tool_name ? opts->tool_name : "tlsf";
}

TlsfPipeline *tlsf_pipeline_load(FILE *fp, const TlsfPipelineOptions *opts) {
  const char *tool = pipeline_tool_name(opts);
  TlsfPipeline *p = calloc(1, sizeof(*p));
  if (!p) {
    fprintf(stderr, "%s: out of memory\n", tool);
    return nullptr;
  }

  p->spec = cli_parse(fp, tool);
  if (!p->spec)
    goto fail;

  if (opts && opts->overwrite_semantics &&
      !parse_semantics(opts->overwrite_semantics, &p->spec->info.semantics)) {
    fprintf(stderr, "%s: invalid semantics '%s'\n", tool,
            opts->overwrite_semantics);
    goto fail;
  }
  if (opts && opts->overwrite_target &&
      !parse_target(opts->overwrite_target, &p->spec->info.target)) {
    fprintf(stderr, "%s: invalid target '%s'\n", tool, opts->overwrite_target);
    goto fail;
  }
  if (!spec_validate_semantics(p->spec, tool))
    goto fail;

  if (expand(p->spec, opts ? opts->overrides : nullptr,
             opts ? opts->n_overrides : 0) != 0)
    goto fail;

  p->cover = cover_build(p->spec, opts && opts->split);
  if (!p->cover) {
    fprintf(stderr, "%s: out of memory\n", tool);
    goto fail;
  }
  recognize_all(p->cover);

  p->csnf = templates_certify(p->cover,
                              opts ? opts->template_mask : TPL_ALL,
                              opts ? opts->certify : true);
  p->composition = p->csnf ? csnf_compose(p->csnf) : nullptr;
  if (!p->csnf || !p->composition) {
    fprintf(stderr, "%s: out of memory\n", tool);
    goto fail;
  }

  return p;

fail:
  tlsf_pipeline_free(p);
  return nullptr;
}

void tlsf_pipeline_free(TlsfPipeline *p) {
  if (!p)
    return;
  csnf_composition_free(p->composition);
  csnf_free(p->csnf);
  spec_free(p->spec);
  free(p);
}
