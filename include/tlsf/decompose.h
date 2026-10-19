#ifndef TLSF_DECOMPOSE_H
#define TLSF_DECOMPOSE_H

#include "tlsf/normalize.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum TlsfDecomposeFormat {
  TLSF_DECOMPOSE_FORMAT_LTLXBA = 0,
  TLSF_DECOMPOSE_FORMAT_LTL = 1,
} TlsfDecomposeFormat;

typedef enum TlsfDecomposeVerdict {
  TLSF_DECOMPOSE_VERDICT_UNKNOWN = 0,
  TLSF_DECOMPOSE_VERDICT_REALIZABLE = 1,
  TLSF_DECOMPOSE_VERDICT_UNREALIZABLE = 2,
} TlsfDecomposeVerdict;

typedef enum TlsfDecomposeTrust {
  TLSF_DECOMPOSE_TRUST_NONE = 0,
  TLSF_DECOMPOSE_TRUST_EXACT = 1,
  TLSF_DECOMPOSE_TRUST_UNDER = 2,
  TLSF_DECOMPOSE_TRUST_OVER = 3,
} TlsfDecomposeTrust;

typedef struct TlsfDecomposeOptions {
  /// Opt in to boolean-fragment verdict prechecks; unavailable means UNKNOWN.
  bool precheck;
  bool split;
  bool lowercase;
  TlsfDecomposeFormat format;
  const char *overwrite_semantics;
  const char *overwrite_target;
  /// Optional post-expansion normalization of preprocessed_ltl only.
  const char *normalization_schedule;
  TlsfNormPhase normalization_phase;
  uint32_t normalization_max_nodes;          ///< 0 = library default
  uint32_t normalization_max_growth_percent; ///< 0 = library default
} TlsfDecomposeOptions;

typedef struct TlsfDecomposeCluster {
  char *ltl;
  char **inputs;
  char **outputs;
  uint32_t n_inputs;
  uint32_t n_outputs;
} TlsfDecomposeCluster;

/// One source bus declaration, preserved after scalar expansion.  This is
/// declaration provenance, not a proof that the formula is symmetric under
/// permutations of the bus indices.
typedef struct TlsfDecomposeIndexedFamily {
  char *origin_name;
  char **members;
  uint32_t n_members;
  uint16_t lo;
  uint16_t hi;
  bool is_output;
  bool is_enum;
} TlsfDecomposeIndexedFamily;

typedef struct TlsfDecomposeResult {
  TlsfDecomposeCluster *clusters;
  uint32_t n_clusters;

  char *preprocessed_ltl;
  char *normalization_schedule;
  uint64_t normalization_nodes_before;
  uint64_t normalization_nodes_after;
  uint64_t normalization_time_ns;
  bool normalization_changed;
  bool normalization_bounds_rejected;
  char **inputs;
  char **outputs;
  uint32_t n_inputs;
  uint32_t n_outputs;

  TlsfDecomposeIndexedFamily *indexed_families;
  uint32_t n_indexed_families;

  char *semantics;
  char *target;
  int32_t gr_level;

  TlsfDecomposeVerdict verdict;
  TlsfDecomposeTrust verdict_trust;
  TlsfDecomposeTrust residual_trust;
} TlsfDecomposeResult;

[[nodiscard]] TlsfDecomposeResult *
tlsf_decompose_file(FILE *fp, const TlsfDecomposeOptions *opts);

[[nodiscard]] TlsfDecomposeResult *
tlsf_decompose_string(const char *spec_text, const TlsfDecomposeOptions *opts);

void tlsf_decompose_result_free(TlsfDecomposeResult *r);

#ifdef __cplusplus
}
#endif

#endif // TLSF_DECOMPOSE_H
