#ifndef TLSF_PIPELINE_H
#define TLSF_PIPELINE_H

#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/templates.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>

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

typedef struct {
  TlsfSpec *spec;
  ConstraintCover *cover;
  Csnf *csnf;
  CsnfComposition *composition;
} TlsfPipeline;

[[nodiscard]] TlsfPipeline *tlsf_pipeline_load(FILE *fp,
                                               const TlsfPipelineOptions *opts);
void tlsf_pipeline_free(TlsfPipeline *p);

#endif // TLSF_PIPELINE_H
