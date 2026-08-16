#ifndef TLSF_DECOMPOSE_H
#define TLSF_DECOMPOSE_H

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
  bool split;
  bool lowercase;
  bool syfco_compatibility;
  TlsfDecomposeFormat format;
  const char *overwrite_semantics;
  const char *overwrite_target;
} TlsfDecomposeOptions;

typedef struct TlsfDecomposeCluster {
  char *ltl;
  char **inputs;
  char **outputs;
  uint32_t n_inputs;
  uint32_t n_outputs;
} TlsfDecomposeCluster;

/// One source bus declaration, preserved after scalar expansion.  Consumers
/// can use this as syntax-derived indexed-family evidence without guessing
/// from the mangled scalar names.
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
