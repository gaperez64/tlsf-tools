/* Positive controls: the same guard placement through the new opt-in APIs. */
#include "../../include/tlsf/gr1_check.h"
#include "../../include/tlsf/gr1_reduction.h"
#include "../../include/tlsf/gr1_lift.h"
#include "../../include/tlsf/gr1_oxidd.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define CHECK(test)                                                            \
  do {                                                                         \
    if (!(test)) {                                                             \
      fprintf(stderr, "new ABI check failed at %d: %s\n", __LINE__, #test);    \
      abort();                                                                 \
    }                                                                          \
  } while (0)
static void *guarded_copy(const void *bytes, size_t size, void **mapping) {
  size_t page = (size_t)sysconf(_SC_PAGESIZE);
  CHECK(page > size);
  *mapping = mmap(NULL, page * 2, PROT_READ | PROT_WRITE,
                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  CHECK(*mapping != MAP_FAILED);
  CHECK(mprotect((char *)*mapping + page, page, PROT_NONE) == 0);
  void *layout = (char *)*mapping + page - size;
  memcpy(layout, bytes, size);
  return layout;
}
static void unguard(void *mapping) {
  CHECK(munmap(mapping, (size_t)sysconf(_SC_PAGESIZE) * 2) == 0);
}
void run_new_controls(const char *source, size_t size, const char *param_source,
                      size_t param_size);
void run_new_controls(const char *source, size_t size, const char *param_source,
                      size_t param_size) {
  void *mapping = NULL;
  TlsfGr1LiftOptions lift_options = {0};
  const TlsfGr1LiftOptions *lift =
      guarded_copy(&lift_options, sizeof lift_options, &mapping);
  TlsfGr1LiftResult lift_result = {0};
  TlsfGr1LiftError lift_error = {0};
  TlsfGr1LiftStats lift_stats = {0};
  CHECK(tlsf_gr1_lift_with_stats((const uint8_t *)source, size, NULL, 0, lift,
                                 &lift_result, &lift_error, &lift_stats, NULL,
                                 NULL) == TLSF_GR1_LIFT_DECLINED);
  CHECK(strcmp(lift_error.stage, "parameters") == 0);
  TlsfGr1LiftStatus lift_status = tlsf_gr1_lift_with_stats(
      (const uint8_t *)param_source, param_size, NULL, 0, lift, &lift_result,
      &lift_error, &lift_stats, NULL, NULL);
  if (lift_status != TLSF_GR1_LIFT_OK)
    fprintf(stderr, "new lift status=%d stage=%s message=%s\n", lift_status,
            lift_error.stage, lift_error.message);
  CHECK(lift_status == TLSF_GR1_LIFT_OK);
  CHECK(lift_result.verdict == TLSF_GR1_CHECK_VERIFIED &&
        lift_stats.seed_solves);
  tlsf_gr1_lift_result_clear(&lift_result);
  unguard(mapping);

  TlsfPipelineOptions load_options = {0};
  load_options.certify = true;
  load_options.template_mask = TPL_ALL;
  TlsfPipeline *pipeline =
      tlsf_pipeline_load_bytes((const uint8_t *)source, size, &load_options);
  CHECK(pipeline != NULL);
  TlsfGr1ReductionOptions reduction_options = {0};
  reduction_options.semantics = TLSF_GR1_EXACT;
  reduction_options.max_artifact_bytes = 1u << 20;
  reduction_options.max_monitor_states = 100;
  const TlsfGr1ReductionOptions *reduce =
      guarded_copy(&reduction_options, sizeof reduction_options, &mapping);
  TlsfGr1Reduction result = {0};
  TlsfGr1ReductionError error = {0};
  TlsfGr1ReductionStats reduction_stats = {0};
  CHECK(tlsf_gr1_reduce_with_stats(pipeline, reduce, &result, &error,
                                   &reduction_stats, NULL,
                                   NULL) == TLSF_GR1_REDUCE_OK);
  CHECK(result.game != NULL &&
        reduction_stats.stages[TLSF_GR1_REDUCE_STATS_SOURCE].wall_ns);
  unguard(mapping);

  Gr1CertificateOptions certificate = {0};
  certificate.semantics = GR1_CERTIFICATE_SEMANTICS_EXACT;
  Gr1CertificateOptions *export =
      guarded_copy(&certificate, sizeof certificate, &mapping);
  Gr1CertificateStats stats = {0};
  OxiddSolveOptions solver = oxidd_solve_options_default();
  solver.node_cap = solver.cache_cap = 1u << 16;
  int unreal = 0;
  Aig *game = result.game;
  result.game = NULL;
  Aig *strategy = solve_gr1_oxidd_ex_with_certificate_and_stats(
      game, &unreal, &solver, export, &stats);
  CHECK(strategy != NULL && !unreal && !export->failed);
  CHECK(stats.solve_wall_ns);
  aig_free(strategy);
  unguard(mapping);
  tlsf_gr1_reduction_clear(&result);
  tlsf_pipeline_free(pipeline);
}
