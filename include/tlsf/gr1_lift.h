#ifndef TLSF_GR1_LIFT_H
#define TLSF_GR1_LIFT_H

#include "tlsf/gr1_check.h"
#include "tlsf/gr1_reduction.h"
#include "tlsf/expand.h"
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Evidence v1.1 binds the policy AAG for certificate checks. Region checks
 * have no policy artifact and must omit policy_sha256. */
#define TLSF_GR1_LIFT_EVIDENCE_FORMAT "tlsf-gr1-lift-evidence-v1.1"

typedef enum {
  TLSF_GR1_LIFT_OK,
  TLSF_GR1_LIFT_UNSUPPORTED,
  TLSF_GR1_LIFT_DECLINED,
  TLSF_GR1_LIFT_LIMIT,
  TLSF_GR1_LIFT_DEADLINE,
  TLSF_GR1_LIFT_CANCELLED,
  TLSF_GR1_LIFT_INVALID,
  TLSF_GR1_LIFT_ERROR,
} TlsfGr1LiftStatus;

/* Zero-valued knobs use these global defaults. They match the applicable
 * settings.py Stage C values. The caller supplies one immutable TLSF snapshot;
 * every seed is expanded from these bytes by changing declared PARAMETERS.
 * Zero-valued caps select their defaults; effective caps are positive.
 * Spot calls cannot be interrupted in process, so a hard deadline also needs
 * a killable caller process. */
#define TLSF_GR1_LIFT_DEFAULT_MAX_SIZES_PER_AXIS 6u
#define TLSF_GR1_LIFT_DEFAULT_MAX_PREDICATE_ARITY 4u
#define TLSF_GR1_LIFT_DEFAULT_MAX_SUBSETS_PER_PREDICATE 2000u
/* Fixed per-run lifting work and proof budgets, independent of the caller's
 * caps; the absolute deadline remains a hard stop in every phase. */
#define TLSF_GR1_LIFT_DEFAULT_SEED_PROBES 24u
#define TLSF_GR1_LIFT_DEFAULT_DISCOVERY_BDD_OPS 2000000ull
#define TLSF_GR1_LIFT_DEFAULT_POLICY_BDD_OPS 2000000ull
#define TLSF_GR1_LIFT_DEFAULT_POLICY_PROOF_NS 12000000000ull
#define TLSF_GR1_LIFT_DEFAULT_SOLVER_NODES (1u << 25)
#define TLSF_GR1_LIFT_DEFAULT_SOLVER_CACHE (1u << 23)
#define TLSF_GR1_LIFT_DEFAULT_CHECKER_NODES (1u << 26)
#define TLSF_GR1_LIFT_DEFAULT_CHECKER_CACHE (1u << 23)
#define TLSF_GR1_LIFT_DEFAULT_SCHEMA_NODES 4000000u
#define TLSF_GR1_LIFT_DEFAULT_SCHEMA_CACHE 400000u
#define TLSF_GR1_LIFT_DEFAULT_MAX_ARTIFACT_BYTES (16u << 20)
#define TLSF_GR1_LIFT_DEFAULT_MAX_MONITOR_STATES 10000u
#define TLSF_GR1_ENV_DEFAULT_CANDIDATE_NS 180000000000ull

/* Optional profiling output. The call zeroes it first and keeps the partial
 * work of a failed call and its final decline stage. Timings use process CPU
 * and CLOCK_MONOTONIC time. */
typedef enum {
  TLSF_GR1_LIFT_STATS_SOURCE,
  TLSF_GR1_LIFT_STATS_TARGET_REDUCE,
  TLSF_GR1_LIFT_STATS_SEED_WINDOW,
  TLSF_GR1_LIFT_STATS_SEED_SOLVE,
  TLSF_GR1_LIFT_STATS_SCHEMA_LEARNING,
  TLSF_GR1_LIFT_STATS_CANDIDATE_INSTANTIATION,
  TLSF_GR1_LIFT_STATS_POLICY_EXPORT,
  TLSF_GR1_LIFT_STATS_INTERNAL_CHECK,
  TLSF_GR1_LIFT_STATS_PUBLISH,
  TLSF_GR1_LIFT_STATS_COUNT
} TlsfGr1LiftStatsStage;
typedef struct {
  /* calls counts BDD operations for schema learning, candidate instantiation,
   * and policy export; for other stages it counts stage invocations. */
  uint64_t wall_ns, cpu_ns, calls;
  int64_t rss_kb, peak_rss_kb;
  uint64_t arena, hblkhd, uordblks, fordblks;
} TlsfGr1LiftStageStats;
typedef struct {
  TlsfGr1LiftStageStats stages[TLSF_GR1_LIFT_STATS_COUNT];
  uint64_t seed_probes, seeds_selected, seed_solves;
  uint64_t target_latches, target_ands, seed_latches, seed_ands;
  uint64_t monitor_count_total, monitor_states_total;
  uint64_t schema_nodes_after_learning, schema_nodes_after_candidate;
  uint64_t candidate_bytes, policy_bytes, internal_checks,
      internal_check_peak_nodes;
  char final_stage[48];
  /* Summed over every seed and target reduction, plus lifting's own RSS
   * samples. */
  TlsfGr1ConstructionWork work;
} TlsfGr1LiftStats;

/* Lifting phase budgets. A zero member selects the matching
 * TLSF_GR1_LIFT_DEFAULT_* value above. */
typedef struct {
  uint64_t max_seed_probes, max_discovery_bdd_ops, max_policy_bdd_ops,
      policy_proof_ns;
} TlsfGr1LiftPhaseBudget;

typedef enum {
  TLSF_GR1_LIFT_POLICY_FIRST,
  TLSF_GR1_LIFT_REGION_FIRST
} TlsfGr1LiftProofOrder;

typedef struct {
  uint64_t deadline_mono_ns;
  int (*cancelled)(void *);
  void *cancel_ctx;
  size_t solver_nodes, solver_cache, checker_nodes, checker_cache;
  size_t schema_nodes, schema_cache, max_artifact_bytes;
  uint32_t max_monitor_states, max_sizes_per_axis, max_predicate_arity,
      max_subsets_per_predicate;
  /* The Python default is true. Set to 2 to disable confirmation. */
  uint32_t seed_confirmation;
  TlsfGr1LiftPhaseBudget phase_budget;
  /* Zero keeps policy-first for callers that need a policy artifact.
   * Region-first retries policy only after region capacity or deadline;
   * REGION_FAILED declines without claiming UNREAL or exporting a policy. */
  TlsfGr1LiftProofOrder proof_order;
  /* Fixed U candidate allowance, including its seeds. Zero selects 180 s.
   * N3 may provide a shorter allowance after factoring out shared seeds. */
  uint64_t env_candidate_ns;
  /* Zero preserves the combined R/U route. Nonzero discovers and solves only
   * R seeds; UNREAL seeds and R declines go straight to the direct route. */
  uint32_t disable_env_lift;
  /* U-only soft RSS share. Zero disables this additional check. It is read
   * live during candidate work and combined with budget.max_rss_bytes by
   * taking the smaller nonzero limit. Seed reductions receive the same cap. */
  TlsfGr1ConstructionBudget env_budget;
  /* Applied to every reduction and to lifting's own RSS checks. As for
   * reduction, zero members disable checks and the budget is read live. */
  TlsfGr1ConstructionBudget budget;
  /* Optional; null skips profiling. The callback, if any, receives each
   * finished stage row and runs only when stats is set. */
  TlsfGr1LiftStats *stats;
  void (*stats_callback)(void *, TlsfGr1LiftStatsStage,
                         const TlsfGr1LiftStageStats *);
  void *stats_context;
} TlsfGr1LiftOptions;

typedef struct {
  TlsfGr1LiftStatus status;
  char stage[48], message[256];
} TlsfGr1LiftError;

/* A null options pointer selects every default. Target overrides name actual
 * source PARAMETERS, as in the pipeline API.
 * Duplicates and unknown declarations are rejected. A successful result owns
 * in-memory target artifacts. Only a result with
 * TLSF_GR1_CHECK_VERIFIED or TLSF_GR1_CHECK_REGION_VERIFIED counts as REAL.
 * The proof is always system-side. Free with tlsf_gr1_lift_result_clear(). */
typedef struct {
  char *game_aag, *certificate_aag, *certificate_json;
  char *policy_aag, *policy_json, *check_json, *evidence_json;
  size_t game_size, certificate_size, certificate_json_size;
  size_t policy_size, policy_json_size, check_json_size, evidence_size;
  TlsfGr1ReductionSemantics semantics;
  TlsfGr1CheckMethod method;
  TlsfGr1CheckVerdict verdict;
} TlsfGr1LiftResult;

/* The target owns one immutable source snapshot and a copy of its prepared
 * game bytes, hashed at preparation and checked before verification.
 * Prepare it once, then lift against that exact game. The lift performs one
 * final independent check of a successful candidate. An inconclusive first
 * method may cause a second check using the other method. Initialize *target
 * to null before preparation; free a successful target with target_free. */
typedef struct TlsfGr1LiftTarget TlsfGr1LiftTarget;
TlsfGr1LiftStatus tlsf_gr1_lift_target_prepare(
    const uint8_t *source, size_t source_size,
    const ParamOverride *target_overrides, size_t target_override_count,
    const TlsfGr1LiftOptions *options, TlsfGr1LiftTarget **target,
    TlsfGr1LiftError *error);
/* Exact-only preparation for the combined G arm. A source without parameters
 * still prepares a trusted game so that the arm can take the direct route. */
TlsfGr1LiftStatus
tlsf_gr1_lift_target_prepare_exact(const uint8_t *source, size_t source_size,
                                   const TlsfGr1LiftOptions *options,
                                   TlsfGr1LiftTarget **target,
                                   TlsfGr1LiftError *error);
void tlsf_gr1_lift_target_free(TlsfGr1LiftTarget *target);
TlsfGr1LiftStatus tlsf_gr1_lift_from_target(const TlsfGr1LiftTarget *target,
                                            const TlsfGr1LiftOptions *options,
                                            TlsfGr1LiftResult *result,
                                            TlsfGr1LiftError *error);
/* Use after any caller-side mutation hooks, before accepting the result. */
int tlsf_gr1_lift_target_matches(const TlsfGr1LiftTarget *target,
                                 const TlsfGr1LiftResult *result);

/* First half of the environment lift. It produces candidate rank functions
 * only; a caller must never interpret success as a target verdict. The rank
 * circuit is combinational over the trusted game's latches and inputs.
 * The result is owned by the caller and cleared with the function below. */
typedef struct {
  char *rank_aag;
  size_t rank_size;
  uint64_t seed_probes, seed_reductions, seed_solves, seed_checks;
  uint64_t rank_nodes, rank_applies, rank_classes;
  uint64_t rank_cache_entries, rank_accounted_bytes;
  char *class_trace_json;
  size_t class_trace_size;
  uint64_t projection_classes, summary_classes, anchor_free_classes;
  uint64_t previous_classes;
} TlsfGr1EnvRankResult;

TlsfGr1LiftStatus tlsf_gr1_env_rank_from_target(
    const TlsfGr1LiftTarget *target, const TlsfGr1LiftOptions *options,
    TlsfGr1EnvRankResult *result, TlsfGr1LiftError *error);
void tlsf_gr1_env_rank_result_clear(TlsfGr1EnvRankResult *result);

/* A target environment candidate is never a verdict. The checked entry point
 * calls the independent certificate checker exactly once on the prepared
 * target game and returns OK only for a VERIFIED UNREAL certificate. */
typedef struct {
  TlsfGr1EnvRankResult rank;
  char *certificate_aag, *certificate_json, *policy_aag, *policy_json;
  char *check_json;
  size_t certificate_size, certificate_json_size, policy_size, policy_json_size,
      check_json_size;
  uint64_t policy_nodes, policy_applies, policy_cache_entries;
  uint64_t policy_accounted_bytes, target_checks;
  uint64_t seed_ns, preflight_ns, rank_ns, policy_ns, check_ns;
  TlsfGr1CheckVerdict verdict;
} TlsfGr1EnvLiftResult;

TlsfGr1LiftStatus tlsf_gr1_env_candidate_from_target(
    const TlsfGr1LiftTarget *target, const TlsfGr1LiftOptions *options,
    TlsfGr1EnvLiftResult *result, TlsfGr1LiftError *error);
TlsfGr1LiftStatus tlsf_gr1_env_lift_from_target(
    const TlsfGr1LiftTarget *target, const TlsfGr1LiftOptions *options,
    TlsfGr1EnvLiftResult *result, TlsfGr1LiftError *error);
void tlsf_gr1_env_lift_result_clear(TlsfGr1EnvLiftResult *result);

typedef enum {
  TLSF_GR1_BOTH_DIRECT,
  TLSF_GR1_BOTH_REAL_LIFT,
  TLSF_GR1_BOTH_ENV_LIFT
} TlsfGr1BothRoute;
typedef enum {
  TLSF_GR1_SEEDS_NONE,
  TLSF_GR1_SEEDS_REAL,
  TLSF_GR1_SEEDS_UNREAL,
  TLSF_GR1_SEEDS_MIXED,
  TLSF_GR1_SEEDS_UNKNOWN
} TlsfGr1SeedPolarity;
typedef struct {
  TlsfGr1LiftResult proof;
  TlsfGr1BothRoute route;
  TlsfGr1SeedPolarity seed_polarity;
  uint64_t target_checks, target_reductions, seed_probes, seed_reductions;
  uint64_t seed_solves, seed_checks, seed_cache_hits;
  char decline_stage[48];
  char decline_stages[256];
} TlsfGr1BothResult;
/* The candidate routes perform no target solve. A decline falls back to one
 * exact solve of the prepared game while the worker deadline permits. The
 * returned proof is sealed by target_matches and owns its artifact buffers. */
TlsfGr1LiftStatus tlsf_gr1_both_from_target(const TlsfGr1LiftTarget *target,
                                            const TlsfGr1LiftOptions *options,
                                            TlsfGr1BothResult *result,
                                            TlsfGr1LiftError *error);
void tlsf_gr1_both_result_clear(TlsfGr1BothResult *result);

TlsfGr1LiftStatus tlsf_gr1_lift(const uint8_t *source, size_t source_size,
                                const ParamOverride *target_overrides,
                                size_t target_override_count,
                                const TlsfGr1LiftOptions *options,
                                TlsfGr1LiftResult *result,
                                TlsfGr1LiftError *error);
void tlsf_gr1_lift_result_clear(TlsfGr1LiftResult *result);

#ifdef __cplusplus
}
#endif
#endif
