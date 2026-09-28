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
static void lower_rss_after_reduction(void *context,
                                      TlsfGr1LiftStatsStage stage,
                                      const TlsfGr1LiftStageStats *event) {
  (void)event;
  if (stage == TLSF_GR1_LIFT_STATS_SEED_WINDOW)
    ((TlsfGr1ConstructionBudget *)context)->max_rss_bytes = 1;
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
  TlsfGr1ConstructionBudget budget = {0};
  budget.size = sizeof budget;
  budget.max_formula_nodes = 1;
  TlsfGr1ConstructionWork work = {0};
  CHECK(tlsf_gr1_lift_with_budget((const uint8_t *)param_source, param_size,
                                  NULL, 0, lift, &lift_result, &lift_error,
                                  &lift_stats, NULL, NULL, &budget,
                                  &work) == TLSF_GR1_LIFT_LIMIT);
  CHECK(strcmp(lift_error.stage, "budget-structure") == 0);
  CHECK(work.formula_nodes > budget.max_formula_nodes);
  budget.max_formula_nodes = 0;
  work = (TlsfGr1ConstructionWork){0};
  CHECK(tlsf_gr1_lift_with_budget(
            (const uint8_t *)param_source, param_size, NULL, 0, lift,
            &lift_result, &lift_error, &lift_stats, lower_rss_after_reduction,
            &budget, &budget, &work) == TLSF_GR1_LIFT_LIMIT);
  CHECK(strcmp(lift_error.stage, "budget-memory") == 0);
  CHECK(strstr(lift_error.message, "seed") != NULL);
  CHECK(work.peak_rss_bytes > budget.max_rss_bytes);
  CHECK(lift_result.game_aag == NULL && lift_result.certificate_aag == NULL);
  budget.max_rss_bytes = 0;
  budget.max_formula_nodes = 1;
  TlsfGr1LiftPhaseBudgetV2 phase_budget = {0};
  phase_budget.size = sizeof phase_budget;
  phase_budget.max_discovery_bdd_ops = 1;
  void *phase_mapping = NULL;
  const TlsfGr1LiftPhaseBudgetV2 *guarded_phase =
      guarded_copy(&phase_budget, sizeof phase_budget, &phase_mapping);
  CHECK(guarded_phase->size == sizeof phase_budget);
  CHECK(tlsf_gr1_lift_with_phase_budget_v2(
            (const uint8_t *)param_source, param_size, NULL, 0, lift,
            &lift_result, &lift_error, &lift_stats, NULL, NULL, NULL, NULL,
            guarded_phase) == TLSF_GR1_LIFT_LIMIT);
  CHECK(lift_result.game_aag == NULL && lift_result.certificate_aag == NULL);
  unguard(phase_mapping);
  phase_budget.size = sizeof phase_budget - 1;
  guarded_phase =
      guarded_copy(&phase_budget, sizeof phase_budget, &phase_mapping);
  CHECK(tlsf_gr1_lift_with_phase_budget_v2(
            (const uint8_t *)param_source, param_size, NULL, 0, lift,
            &lift_result, &lift_error, &lift_stats, NULL, NULL, NULL, NULL,
            guarded_phase) == TLSF_GR1_LIFT_INVALID);
  CHECK(strcmp(lift_error.stage, "arguments") == 0);
  unguard(phase_mapping);
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
  reduce = guarded_copy(&reduction_options, sizeof reduction_options, &mapping);
  work = (TlsfGr1ConstructionWork){0};
  CHECK(tlsf_gr1_reduce_with_budget(pipeline, reduce, &result, &error,
                                    &reduction_stats, NULL, NULL, &budget,
                                    &work) == TLSF_GR1_REDUCE_LIMIT);
  CHECK(strcmp(error.stage, "budget-structure") == 0);
  CHECK(work.formula_nodes > budget.max_formula_nodes);
  unguard(mapping);
  tlsf_pipeline_free(pipeline);
}
