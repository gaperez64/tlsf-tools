#ifndef TLSF_OXIDD_OPTIONS_H
#define TLSF_OXIDD_OPTIONS_H
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#ifdef __cplusplus
extern "C" {
#endif
#define TLSF_OXIDD_OPTIONS_ABI_VERSION 2
typedef enum {
  OXIDD_GC_AUTO = 0,
  OXIDD_GC_PRESSURE = 1,
} OxiddGcMode;

typedef enum {
  OXIDD_VAR_ORDER_INPUT_FIRST = 0,
  OXIDD_VAR_ORDER_STATE_FIRST,
  OXIDD_VAR_ORDER_FANIN_DFS,
} OxiddVarOrder;

typedef enum {
  OXIDD_BUILD_GATES = 0,
} OxiddBuildPlan;

typedef enum {
  OXIDD_SAFETY_OBJECTIVE_OUTPUT = 0,
  OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR = 1,
} OxiddSafetyObjective;

typedef enum {
  OXIDD_FAILURE_NONE,
  OXIDD_FAILURE_BDD,
  OXIDD_FAILURE_HOST,
  OXIDD_FAILURE_CONFIGURATION,
  OXIDD_FAILURE_CONVERSION,
  OXIDD_FAILURE_INVALID,
  OXIDD_FAILURE_DEADLINE,
  OXIDD_FAILURE_CANCELLED,
  OXIDD_FAILURE_ARTIFACT_LIMIT
} OxiddFailureKind;

typedef struct {
  OxiddFailureKind kind;
  const char *phase, *operation;
  size_t operation_id;
  uint32_t index;
} OxiddFailure;

typedef struct {
  size_t node_cap;  // 0 = legacy heuristic default
  size_t cache_cap; // 0 = legacy heuristic default
  OxiddGcMode gc_mode;
  unsigned gc_threshold_percent;
  unsigned verbosity;
  FILE *trace;
  OxiddSafetyObjective safety_objective;
  uint32_t safety_output_index;
  OxiddFailure *failure; // optional caller-owned output; never a losing verdict
  OxiddVarOrder var_order;
  OxiddBuildPlan build_plan;
  // Strict tlsfsolve-order-v1 local-variable permutation.
  const char *order_file;
  bool demand_transitions, realizability_only;
#ifndef NDEBUG
  bool trace_roots;
  uint32_t trace_gate;
  size_t trace_node_limit, trace_scratch_bytes;
#endif
} OxiddSolveOptions;

typedef struct {
  size_t node_cap;  // 0 = legacy heuristic default
  size_t cache_cap; // 0 = legacy heuristic default
  OxiddGcMode gc_mode;
  unsigned gc_threshold_percent;
  unsigned verbosity;
  FILE *trace;
  OxiddSafetyObjective safety_objective;
  uint32_t safety_output_index;
  OxiddFailure *failure; // optional caller-owned output; never a losing verdict
  OxiddVarOrder var_order;
  OxiddBuildPlan build_plan;
  // Strict tlsfsolve-order-v1 local-variable permutation.
  const char *order_file;
  bool demand_transitions, realizability_only;
#ifndef NDEBUG
  bool trace_roots;
  uint32_t trace_gate;
  size_t trace_node_limit, trace_scratch_bytes;
#endif
  uint32_t abi_version;
  size_t struct_size;
  uint64_t deadline_mono_ns;
  int (*cancelled)(void *);
  void *cancel_ctx;
  size_t max_artifact_bytes;
} OxiddSolveOptionsV2;

OxiddSolveOptions oxidd_solve_options_default(void);
OxiddSolveOptionsV2 oxidd_solve_options_default_v2(void);
#ifdef __cplusplus
}
#endif
#endif
