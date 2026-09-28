#ifndef TLSF_GR1_REDUCTION_H
#define TLSF_GR1_REDUCTION_H

#include "tlsf/aiger.h"
#include "tlsf/pipeline.h"

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
  TLSF_GR1_REDUCE_OK,
  TLSF_GR1_REDUCE_UNSUPPORTED,
  TLSF_GR1_REDUCE_DECLINED,
  TLSF_GR1_REDUCE_LIMIT,
  TLSF_GR1_REDUCE_DEADLINE,
  TLSF_GR1_REDUCE_CANCELLED,
  TLSF_GR1_REDUCE_INVALID,
  TLSF_GR1_REDUCE_ERROR,
} TlsfGr1ReductionStatus;

typedef enum { TLSF_GR1_EXACT, TLSF_GR1_STRICT } TlsfGr1ReductionSemantics;

typedef enum {
  TLSF_GR1_REDUCE_STATS_SOURCE,
  TLSF_GR1_REDUCE_STATS_MONITORS,
  TLSF_GR1_REDUCE_STATS_ENCODE,
  TLSF_GR1_REDUCE_STATS_PUBLISH,
  TLSF_GR1_REDUCE_STATS_COUNT
} TlsfGr1ReductionStatsStage;
typedef struct {
  uint64_t wall_ns, cpu_ns;
  int64_t rss_kb, peak_rss_kb;
  uint64_t arena, hblkhd, uordblks, fordblks;
} TlsfGr1ReductionStageStats;
typedef struct {
  TlsfGr1ReductionStageStats stages[TLSF_GR1_REDUCE_STATS_COUNT];
  uint64_t monitor_count, monitor_states, game_latches, game_ands;
} TlsfGr1ReductionStats;

typedef struct {
  TlsfGr1ReductionSemantics semantics;
  /* Absolute CLOCK_MONOTONIC nanoseconds; zero disables the deadline.
   * Deadline and cancellation are checked cooperatively between Spot calls.
   * Spot translation and language-equivalence calls cannot be interrupted
   * in-process. For hard time and memory bounds, run the reduction in a
   * killable process, as Acacia's forked arms do. */
  uint64_t deadline_mono_ns;
  int (*cancelled)(void *);
  void *cancel_ctx;
  /* Required positive caps. The artifact cap checks produced output sizes;
   * it does not cap intermediate Spot/BuDDy allocations. The state cap bounds
   * all one-hot monitor latches and is passed to Spot determinization. */
  size_t max_artifact_bytes;
  uint32_t max_monitor_states;
} TlsfGr1ReductionOptions;

typedef struct {
  TlsfGr1ReductionStatus status;
  char stage[48];
  char message[256];
} TlsfGr1ReductionError;

/* Opt-in construction limits. size must be sizeof this version. A zero limit
 * disables that particular check. Existing option and result layouts stay
 * unchanged. RSS is a soft process high-water check; the caller retains its
 * absolute deadline and cgroup memory boundary. */
typedef struct {
  size_t size;
  uint64_t max_formula_nodes, max_ap_count, max_conjuncts, max_conjunct_nodes;
  uint64_t max_predicted_monitor_states;
  uint32_t max_temporal_depth, max_total_states, max_total_edges;
  uint64_t max_rss_bytes;
} TlsfGr1ConstructionBudget;
typedef struct {
  uint64_t formula_nodes, ap_count, conjuncts, max_conjunct_nodes;
  uint64_t max_temporal_depth, predicted_monitor_states;
  /* On a Spot aborter decline, the crossed state or edge count is a lower
   * bound (limit + 1). Spot discards the partial graph, so its other count
   * is unavailable. monitors_completed counts only finished monitors. */
  uint64_t monitors_completed, states, edges, peak_rss_bytes;
} TlsfGr1ConstructionWork;

/* Initialize every field to zero before the first call. A non-empty result
 * must be cleared before reuse; reduction rejects it without changing it.
 * All fields are owned by the result and valid until clear. On other failures
 * the result is empty. Text fields are NUL terminated and have explicit
 * lengths. Exact preserves the lowered implication. Strict is REAL-sound only:
 * a strict losing game must never be used as an UNREAL proof. */
typedef struct {
  Aig *game;
  char *aag;
  size_t aag_size;
  char *metadata_json;
  size_t metadata_size;
  char *provenance_json;
  size_t provenance_size;
  char *symbol_map;
  size_t symbol_map_size;
} TlsfGr1Reduction;

/* pipeline must come from tlsf_pipeline_load_bytes so its retained source
 * and frontend provenance are bound to the same snapshot. */
TlsfGr1ReductionStatus tlsf_gr1_reduce(const TlsfPipeline *pipeline,
                                       const TlsfGr1ReductionOptions *options,
                                       TlsfGr1Reduction *result,
                                       TlsfGr1ReductionError *error);
TlsfGr1ReductionStatus tlsf_gr1_reduce_with_stats(
    const TlsfPipeline *pipeline, const TlsfGr1ReductionOptions *options,
    TlsfGr1Reduction *result, TlsfGr1ReductionError *error,
    TlsfGr1ReductionStats *stats,
    void (*stats_callback)(void *, TlsfGr1ReductionStatsStage,
                           const TlsfGr1ReductionStageStats *),
    void *stats_context);
TlsfGr1ReductionStatus tlsf_gr1_reduce_with_budget(
    const TlsfPipeline *pipeline, const TlsfGr1ReductionOptions *options,
    TlsfGr1Reduction *result, TlsfGr1ReductionError *error,
    TlsfGr1ReductionStats *stats,
    void (*stats_callback)(void *, TlsfGr1ReductionStatsStage,
                           const TlsfGr1ReductionStageStats *),
    void *stats_context, const TlsfGr1ConstructionBudget *budget,
    TlsfGr1ConstructionWork *work);
void tlsf_gr1_reduction_clear(TlsfGr1Reduction *result);

#ifdef __cplusplus
}
#endif

#endif
