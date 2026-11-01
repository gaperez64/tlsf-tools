#include "tlsf/gr1_reduction.h"
#include "tlsf/pipeline.h"
#include <stdio.h>
#include <string.h>

static int check(const char *name, const char *source,
                 TlsfGr1ReductionStatus expected) {
  TlsfPipelineError load_error = {0};
  TlsfPipelineOptions load = {
      .certify = true, .template_mask = TPL_ALL, .error = &load_error};
  TlsfPipeline *pipeline =
      tlsf_pipeline_load_bytes((const uint8_t *)source, strlen(source), &load);
  if (!pipeline) {
    fprintf(stderr, "%s: pipeline failed\n", name);
    return 1;
  }
  TlsfGr1ReductionOptions options = {.semantics = TLSF_GR1_EXACT,
                                     .max_artifact_bytes = 16u << 20,
                                     .max_monitor_states = 10000};
  TlsfGr1Reduction result = {0};
  TlsfGr1ReductionError error = {0};
  TlsfGr1ReductionStatus status =
      tlsf_gr1_reduce(pipeline, &options, &result, &error);
  int failed =
      status != expected || (status == TLSF_GR1_REDUCE_OK &&
                             (!result.aag_size || !result.provenance_size));
  if (failed)
    fprintf(stderr, "%s: status %d, expected %d\n", name, (int)status,
            (int)expected);
  tlsf_gr1_reduction_clear(&result);
  tlsf_pipeline_free(pipeline);
  return failed;
}

int main(void) {
  int failures = 0;
  failures +=
      check("general Pi2",
            "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { go; } "
            "OUTPUTS { p; q; } GUARANTEES { G(go -> (p U q)); } }",
            TLSF_GR1_REDUCE_OK);
  failures +=
      check("default-only frozen absorption",
            "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { OUTPUTS { a; b; } "
            "GUARANTEES { G(F a || (F a && F(G b))); } }",
            TLSF_GR1_REDUCE_OK);
  failures +=
      check("non-Buchi formula",
            "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { OUTPUTS { a; } "
            "GUARANTEES { F G a; } }",
            TLSF_GR1_REDUCE_UNSUPPORTED);
  printf("3 GR1 admission checks, %d failures\n", failures);
  return failures ? 1 : 0;
}
