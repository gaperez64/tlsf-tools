#include "tlsf/pipeline.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/gr1_check.h"
#include "tlsf/gr1_reduction.h"
#include "tlsf/gr1_lift.h"

#include <assert.h>
#include <string.h>

static int cancelled(void *ctx) {
  (void)ctx;
  return 1;
}

static int cancel_at_boundary(void *ctx) {
  unsigned *calls = ctx;
  return ++*calls == 3;
}

int main(void) {
  static const char source[] =
      "INFO { TITLE: \"C ABI\" DESCRIPTION: \"reduction\" "
      "SEMANTICS: Mealy TARGET: Mealy }\n"
      "MAIN { INPUTS { i; } OUTPUTS { o; } "
      "GUARANTEE { G (i -> o); G F o; } }\n";
  TlsfPipelineError load_error = {0};
  TlsfPipelineOptions load_options = {
      .certify = true,
      .template_mask = TPL_ALL,

      .error = &load_error,
  };
  TlsfPipeline *pipeline = tlsf_pipeline_load_bytes(
      (const uint8_t *)source, strlen(source), &load_options);
  assert(pipeline);
  TlsfGr1ReductionOptions options = {

      .semantics = TLSF_GR1_EXACT,
      .max_artifact_bytes = 1024 * 1024,
      .max_monitor_states = 100,
  };
  TlsfGr1Reduction result = {0};
  TlsfGr1ReductionError error = {0};
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_OK);
  assert(result.game && result.aag && result.provenance_json);
  assert(aig_num_inputs(result.game) == 2);
  assert(aig_num_justice(result.game) == 2);
  assert(strstr(result.provenance_json, "\"available\":true"));
  Aig *owned_game = result.game;
  char *owned_aag = result.aag;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_INVALID);
  assert(result.game == owned_game && result.aag == owned_aag);
  assert(strstr(error.message, "result must be empty"));
  tlsf_gr1_reduction_clear(&result);
  tlsf_gr1_reduction_clear(&result);
  options.cancelled = cancelled;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_CANCELLED);
  assert(!result.game && !result.aag);
  unsigned boundary_calls = 0;
  options.cancelled = cancel_at_boundary;
  options.cancel_ctx = &boundary_calls;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_CANCELLED);
  assert(boundary_calls == 3);
  assert(strcmp(error.stage, "parse-formula") == 0);
  assert(!result.game && !result.aag);
  options.cancel_ctx = NULL;
  options.max_artifact_bytes = 0;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_INVALID);
  assert(!result.game && !result.aag);
  options.max_artifact_bytes = 1024 * 1024;
  options.cancelled = NULL;
  options.max_monitor_states = 1;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_LIMIT);
  assert(!result.game && !result.aag);
  options.max_monitor_states = 100;
  options.deadline_mono_ns = 1;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_DEADLINE);
  assert(!result.game && !result.aag);
  options.deadline_mono_ns = 0;
  options.max_artifact_bytes = 1;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_LIMIT);
  assert(!result.game && !result.aag);
  options.max_artifact_bytes = 1024 * 1024;
  uint8_t *snapshot = (uint8_t *)pipeline->source_bytes;
  uint8_t original = snapshot[0];
  snapshot[0] ^= 1;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_INVALID);
  assert(!result.game && !result.aag);
  snapshot[0] = original;
  tlsf_pipeline_free(pipeline);
  static const char fallback_source[] =
      "INFO { TITLE: \"aborter\" DESCRIPTION: \"fallback\" "
      "SEMANTICS: Mealy TARGET: Mealy }\n"
      "MAIN { INPUTS { i; } OUTPUTS { o; } "
      "GUARANTEES { G (F o || ((!i || X i) && (i || X !i))); } }\n";
  pipeline = tlsf_pipeline_load_bytes((const uint8_t *)fallback_source,
                                      strlen(fallback_source), &load_options);
  assert(pipeline);
  options.max_monitor_states = 3;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_LIMIT);
  assert(strcmp(error.stage, "determinize") == 0);
  assert(!result.game && !result.aag);
  options.max_monitor_states = 4;
  assert(tlsf_gr1_reduce(pipeline, &options, &result, &error) ==
         TLSF_GR1_REDUCE_OK);
  assert(strstr(result.metadata_json, "\"fallback_monitor_count\":1"));
  tlsf_gr1_reduction_clear(&result);
  tlsf_pipeline_free(pipeline);
  return 0;
}
