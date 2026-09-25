#ifndef TLSF_GR1_REDUCTION_H
#define TLSF_GR1_REDUCTION_H

#include "tlsf/aiger.h"
#include "tlsf/pipeline.h"

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define TLSF_GR1_REDUCTION_ABI_VERSION 1

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

typedef struct {
  uint32_t abi_version;
  size_t struct_size;
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

/* pipeline must come from tlsf_pipeline_load_bytes_v2 so its retained source
 * and frontend provenance are bound to the same snapshot. */
TlsfGr1ReductionStatus
tlsf_gr1_reduce_v1(const TlsfPipeline *pipeline,
                   const TlsfGr1ReductionOptions *options,
                   TlsfGr1Reduction *result, TlsfGr1ReductionError *error);
void tlsf_gr1_reduction_clear(TlsfGr1Reduction *result);

#ifdef __cplusplus
}
#endif

#endif
