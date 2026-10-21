#ifndef TLSF_CONVERT_H
#define TLSF_CONVERT_H

#include "tlsf/decompose.h"

#ifdef __cplusplus
extern "C" {
#endif

/// Whole infinite-word objective for a synthesis consumer. All strings and
/// arrays are owned by this result, independently of the source and parser.
/// Signals use the lowercase ltlxba convention, including unused declarations.
/// Scalars precede buses and enum buses, declarations are reversed within each
/// group, and bus members retain ascending index order (Acacia serialization).
/// Families retain declaration order; has_indexed_conjunction records the
/// source-text `&&` followed by optional whitespace and `[` policy for hints.
typedef struct TlsfConversionResult {
  char *preprocessed_ltl;
  char **inputs;
  char **outputs;
  uint32_t n_inputs;
  uint32_t n_outputs;
  TlsfDecomposeIndexedFamily *indexed_families;
  uint32_t n_indexed_families;
  bool has_indexed_conjunction;
  char *semantics;
  char *original_target;
  char *effective_target;
  int32_t gr_level;
} TlsfConversionResult;

/// Parse, validate, expand and adapt once, then print the whole objective.
/// effective_target is "Mealy", "Moore", or NULL to retain the source target.
/// Returns NULL on invalid/unsupported input or allocation failure; diagnostics
/// follow the library's diagnostic stream. Finite semantics are unsupported.
/// No cover, certificates, composition or residual clusters are constructed.
[[nodiscard]] TlsfConversionResult *tlsf_convert(const char *spec_text,
                                                 const char *effective_target);
/// Accepts NULL. Frees the result and every owned string/array.
void tlsf_conversion_result_free(TlsfConversionResult *result);

#ifdef __cplusplus
}
#endif
#endif
