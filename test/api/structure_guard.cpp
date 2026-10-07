#include "tlsf/gr1_lift.h"
#include "tlsf/gr1_reduction.h"

#include <cassert>
#include <cmath>
#include <cstring>
#include <limits>
#include <string>

static int cancelled(void *) { return 1; }

int main() {
  const char source[] =
      "INFO { TITLE: \"generated guard boundary\" SEMANTICS: Mealy TARGET: "
      "Mealy }\n"
      "MAIN { INPUTS { request; } OUTPUTS { response; } "
      "GUARANTEES { G (request -> response); G F response; } }\n";
  TlsfPipelineOptions load{};
  load.certify = true;
  load.template_mask = TPL_ALL;
  TlsfPipeline *pipeline = tlsf_pipeline_load_bytes(
      reinterpret_cast<const uint8_t *>(source), sizeof source - 1, &load);
  assert(pipeline);
  TlsfGr1ReductionStats stats{};
  TlsfGr1ReductionOptions options{};
  options.max_artifact_bytes = 1u << 20;
  options.max_monitor_states = 100;
  options.stats = &stats;
  TlsfGr1Reduction result{};
  TlsfGr1ReductionError error{};
  TlsfGr1ReductionStatus cause;
  assert(tlsf_gr1_reduce_v1(pipeline, &options, &result, &error, &cause) ==
         TLSF_GR1_REDUCE_OK);
  const TlsfGr1ConstructionWork work = stats.work;
  const std::string incumbent_aag(result.aag, result.aag_size);
  const std::string incumbent_metadata(result.metadata_json,
                                       result.metadata_size);
  tlsf_gr1_reduction_clear(&result);
  TlsfGr1StructureGuardOptionsV1 guard{1};
  // Byte-identical reductions through legacy, explicit 1, and NULL v2 options.
  for (const auto *setting :
       {&guard, static_cast<TlsfGr1StructureGuardOptionsV1 *>(nullptr)}) {
    assert(tlsf_gr1_reduce_v2(pipeline, &options, setting, &result, &error,
                              &cause) == TLSF_GR1_REDUCE_OK);
    assert(cause == TLSF_GR1_REDUCE_OK);
    assert(incumbent_aag == std::string(result.aag, result.aag_size));
    assert(incumbent_metadata ==
           std::string(result.metadata_json, result.metadata_size));
    assert(!memcmp(&work, &stats.work,
                   offsetof(TlsfGr1ConstructionWork, peak_rss_bytes)));
    tlsf_gr1_reduction_clear(&result);
  }
  // Each structural guard, in isolation: equality passes, one below stops,
  // and a global factor of 2 (or off) permits exactly the same reduction.
  for (unsigned field = 0; field < 6; ++field) {
    options.budget = {};
    uint64_t value = 0;
    const auto set_limit = [&](uint64_t limit) {
      switch (field) {
      case 0:
        options.budget.max_formula_nodes = limit;
        value = work.formula_nodes;
        break;
      case 1:
        options.budget.max_ap_count = limit;
        value = work.ap_count;
        break;
      case 2:
        options.budget.max_conjuncts = limit;
        value = work.conjuncts;
        break;
      case 3:
        options.budget.max_conjunct_nodes = limit;
        value = work.max_conjunct_nodes;
        break;
      case 4:
        options.budget.max_temporal_depth = limit;
        value = work.max_temporal_depth;
        break;
      case 5:
        options.budget.max_predicted_monitor_states = limit;
        value = work.predicted_monitor_states;
        break;
      }
    };
    set_limit(1);
    assert(value > 1);
    set_limit(value);
    guard.scale = 1;
    assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                              &cause) == TLSF_GR1_REDUCE_OK);
    tlsf_gr1_reduction_clear(&result);
    set_limit(value - 1);
    const auto budget = options.budget;
    assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                              &cause) == TLSF_GR1_REDUCE_LIMIT);
    assert(cause == TLSF_GR1_REDUCE_LIMIT &&
           !strcmp(error.stage, "budget-structure"));
    assert(stats.work.monitors_completed == 0);
    assert(tlsf_gr1_reduce_v1(pipeline, &options, &result, &error, &cause) ==
           TLSF_GR1_REDUCE_LIMIT);
    for (double scale : {2., 4., 0., std::numeric_limits<double>::max()}) {
      guard.scale = scale;
      assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                                &cause) == TLSF_GR1_REDUCE_OK);
      assert(incumbent_aag == std::string(result.aag, result.aag_size));
      assert(!memcmp(&budget, &options.budget, sizeof budget));
      tlsf_gr1_reduction_clear(&result);
    }
  }
  options.budget = {};
  guard.scale = 0;
  options.budget.max_total_states = 1;
  assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                            &cause) == TLSF_GR1_REDUCE_LIMIT);
  assert(!strcmp(error.stage, "budget-translate") ||
         strstr(error.stage, "budget-monitor"));
  options.budget = {};
  options.budget.max_total_edges = 1;
  assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                            &cause) == TLSF_GR1_REDUCE_LIMIT);
  assert(!strcmp(error.stage, "budget-translate") ||
         strstr(error.stage, "budget-monitor"));
  options.budget = {};
  options.budget.max_rss_bytes = 1;
  assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                            &cause) == TLSF_GR1_REDUCE_LIMIT);
  assert(!strcmp(error.stage, "budget-memory"));
  options.budget = {};
  options.deadline_mono_ns = 1;
  assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                            &cause) == TLSF_GR1_REDUCE_DEADLINE);
  options.deadline_mono_ns = 0;
  options.cancelled = cancelled;
  assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                            &cause) == TLSF_GR1_REDUCE_CANCELLED);
  options.cancelled = nullptr;
  options.max_artifact_bytes = 1;
  assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                            &cause) == TLSF_GR1_REDUCE_LIMIT);
  options.max_artifact_bytes = 1u << 20;
  options.budget.max_formula_nodes = 1;
  guard.scale = std::numeric_limits<double>::min();
  assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                            &cause) == TLSF_GR1_REDUCE_LIMIT);
  for (double scale : {-1., std::numeric_limits<double>::infinity(),
                       std::numeric_limits<double>::quiet_NaN()}) {
    guard.scale = scale;
    assert(tlsf_gr1_reduce_v2(pipeline, &options, &guard, &result, &error,
                              &cause) == TLSF_GR1_REDUCE_INVALID);
    assert(cause == TLSF_GR1_REDUCE_INVALID);
  }
  tlsf_pipeline_free(pipeline);

  // The lifting version carries the same setting to target preparation.
  TlsfGr1LiftOptions lift{};
  TlsfGr1LiftStats lift_stats{};
  lift.stats = &lift_stats;
  lift.budget.max_formula_nodes = work.formula_nodes - 1;
  lift.solver_nodes = lift.checker_nodes = 1u << 20;
  lift.solver_cache = lift.checker_cache = 1u << 16;
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError lift_error{};
  TlsfGr1LiftStatus lift_cause;
  guard.scale = 1;
  assert(tlsf_gr1_lift_target_prepare_exact_v2(
             reinterpret_cast<const uint8_t *>(source), sizeof source - 1,
             &lift, &guard, &target, &lift_error,
             &lift_cause) == TLSF_GR1_LIFT_LIMIT);
  assert(lift_cause == TLSF_GR1_LIFT_LIMIT && !target);
  guard.scale = 2;
  assert(tlsf_gr1_lift_target_prepare_exact_v2(
             reinterpret_cast<const uint8_t *>(source), sizeof source - 1,
             &lift, &guard, &target, &lift_error,
             &lift_cause) == TLSF_GR1_LIFT_OK);
  TlsfGr1BothResult both{};
  assert(tlsf_gr1_both_from_target_v2(target, &lift, &guard, nullptr, &both,
                                      &lift_error) == TLSF_GR1_LIFT_OK);
  assert(both.target_reductions == 1 && both.target_checks == 1);
  assert(tlsf_gr1_lift_target_matches(target, &both.proof));
  tlsf_gr1_both_result_clear(&both);
  tlsf_gr1_lift_target_free(target);
  // A target prepared with relaxed guards must carry that scale to seeds.
  const char parameterized[] =
      "INFO { TITLE: \"generated repeated recurrence\" SEMANTICS: Mealy "
      "TARGET: Mealy }\n"
      "GLOBAL { PARAMETERS { extent = 5; } }\n"
      "MAIN { INPUTS { demand[extent]; } OUTPUTS { response[extent]; } "
      "GUARANTEES { &&[0 <= i < extent] G F response[i]; } }\n";
  target = nullptr;
  lift.budget.max_formula_nodes = 1;
  lift.disable_env_lift = 1;
  lift.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
  guard.scale = 32;
  assert(tlsf_gr1_lift_target_prepare_exact_v2(
             reinterpret_cast<const uint8_t *>(parameterized),
             sizeof parameterized - 1, &lift, &guard, &target, &lift_error,
             &lift_cause) == TLSF_GR1_LIFT_OK);
  for (double scale : {1., 32.}) {
    guard.scale = scale;
    assert(tlsf_gr1_both_from_target_v2(target, &lift, &guard, nullptr, &both,
                                        &lift_error) == TLSF_GR1_LIFT_OK);
    if (scale == 1)
      assert(both.route == TLSF_GR1_BOTH_DIRECT);
    assert((both.seed_solves > 0) == (scale != 1));
    assert(both.target_checks == 1 &&
           tlsf_gr1_lift_target_matches(target, &both.proof));
    tlsf_gr1_both_result_clear(&both);
  }
  tlsf_gr1_lift_target_free(target);
  return 0;
}
