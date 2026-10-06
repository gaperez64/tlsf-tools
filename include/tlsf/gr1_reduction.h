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

/* Construction limits. A zero limit disables that particular check, so a
 * zero-initialized budget imposes none. RSS is a soft process high-water
 * check; the caller retains its absolute deadline and cgroup memory boundary.
 * The library reads the budget in the caller's options at every check, so a
 * stats callback may tighten it while a call runs. */
typedef struct {
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
   * is unavailable. monitors_completed counts only finished monitors.
   * peak_rss_bytes is sampled only while max_rss_bytes is set. */
  uint64_t monitors_completed, states, edges, peak_rss_bytes;
} TlsfGr1ConstructionWork;

/* Optional profiling output. The call zeroes it first and keeps the partial
 * work of a failed call. Timings use process CPU and CLOCK_MONOTONIC time. */
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
  TlsfGr1ConstructionWork work;
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
  TlsfGr1ConstructionBudget budget;
  /* Optional; null skips profiling. The callback, if any, receives each
   * finished stage row and runs only when stats is set. */
  TlsfGr1ReductionStats *stats;
  void (*stats_callback)(void *, TlsfGr1ReductionStatsStage,
                         const TlsfGr1ReductionStageStats *);
  void *stats_context;
} TlsfGr1ReductionOptions;

typedef struct {
  TlsfGr1ReductionStatus status;
  char stage[48];
  char message[256];
} TlsfGr1ReductionError;

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
/* Optional diagnostic status, independent of the legacy return. Contract
 * failures retain UNSUPPORTED but report ERROR here. Initialized to OK on
 * success; no existing public structure changes. */
TlsfGr1ReductionStatus
tlsf_gr1_reduce_v1(const TlsfPipeline *pipeline,
                   const TlsfGr1ReductionOptions *options,
                   TlsfGr1Reduction *result, TlsfGr1ReductionError *error,
                   TlsfGr1ReductionStatus *failure_status);
void tlsf_gr1_reduction_clear(TlsfGr1Reduction *result);

#ifdef __cplusplus
}
#endif

#endif
