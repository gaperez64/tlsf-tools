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

#define TLSF_GR1_LIFT_ABI_VERSION 1
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
#define TLSF_GR1_LIFT_DEFAULT_POLICY_PROOF_FRACTION 0.75
#define TLSF_GR1_LIFT_DEFAULT_DISCOVERY_SHARE 0.20
#define TLSF_GR1_LIFT_DEFAULT_SOLVER_NODES (1u << 25)
#define TLSF_GR1_LIFT_DEFAULT_SOLVER_CACHE (1u << 23)
#define TLSF_GR1_LIFT_DEFAULT_CHECKER_NODES (1u << 26)
#define TLSF_GR1_LIFT_DEFAULT_CHECKER_CACHE (1u << 23)
#define TLSF_GR1_LIFT_DEFAULT_SCHEMA_NODES 4000000u
#define TLSF_GR1_LIFT_DEFAULT_SCHEMA_CACHE 400000u
#define TLSF_GR1_LIFT_DEFAULT_MAX_ARTIFACT_BYTES (16u << 20)
#define TLSF_GR1_LIFT_DEFAULT_MAX_MONITOR_STATES 10000u

typedef struct {
  uint32_t abi_version;
  size_t struct_size;
  uint64_t deadline_mono_ns;
  int (*cancelled)(void *);
  void *cancel_ctx;
  size_t solver_nodes, solver_cache, checker_nodes, checker_cache;
  size_t schema_nodes, schema_cache, max_artifact_bytes;
  uint32_t max_monitor_states, max_sizes_per_axis,
      max_predicate_arity, max_subsets_per_predicate;
  double policy_proof_fraction, discovery_share;
  /* The Python default is true. Set to 2 to disable confirmation. */
  uint32_t seed_confirmation;
} TlsfGr1LiftOptions;

typedef struct {
  TlsfGr1LiftStatus status;
  char stage[48], message[256];
} TlsfGr1LiftError;

/* Target overrides name actual source PARAMETERS, as in the pipeline API.
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

TlsfGr1LiftStatus tlsf_gr1_lift_v1(const uint8_t *source, size_t source_size,
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
