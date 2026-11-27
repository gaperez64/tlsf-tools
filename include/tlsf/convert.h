#ifndef TLSF_CONVERT_H
#define TLSF_CONVERT_H

#include "tlsf/decompose.h"
#include "tlsf/ast_api.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct TlsfValueBus {
  const struct TlsfValueBus *next;
  const char *const *bits;       ///< Source spelling, ascending physical index.
  const uint16_t *parameter_ids; ///< One-based GLOBAL parameter ordinals.
  uint32_t declaration_id;       ///< One-based within its owner.
  uint32_t bit_count;
  uint16_t lo, parameter_count;
  bool is_output, is_enum, proved_bit_width;
} TlsfValueBus;

typedef enum TlsfValueSection {
  TLSF_VALUE_INITIALLY,
  TLSF_VALUE_REQUIRE,
  TLSF_VALUE_ASSUME,
  TLSF_VALUE_PRESET,
  TLSF_VALUE_ASSERT,
  TLSF_VALUE_GUARANTEE,
} TlsfValueSection;

typedef struct TlsfValueDomain {
  const struct TlsfValueDomain *next;
  const struct TlsfValueBinding *outer;
  const int64_t *coordinates;
  const uint16_t *parameter_ids;
  uint32_t source_formula_id, binder_id, count;
  uint16_t parameter_count;
} TlsfValueDomain;

typedef struct TlsfValueBinding {
  const TlsfValueDomain *domain;
  int64_t coordinate;
} TlsfValueBinding;

typedef struct TlsfValueInstance {
  const struct TlsfValueInstance *next;
  /// Source AP spelling. Target adaptation can shift child links.
  const TlsfAstNode *expanded;
  const TlsfValueBinding *bindings;
  uint64_t bit_operand_bound;  ///< Max extracted operand + 1; 0 if absent, UINT64_MAX if negative.
  uint32_t source_formula_id, source_node_id;
  TlsfValueSection section;
} TlsfValueInstance;

/// Conversion-local evidence. Buses follow the indexed-family order. Domain
/// and occurrence lists are in reverse capture order. Incomplete bindings
/// must not be used as evidence. All storage lives with the expanded AST.
typedef struct TlsfValueOrigins {
  const TlsfValueBus *buses;
  const TlsfValueDomain *domains;
  const TlsfValueInstance *instances;
  bool complete;
} TlsfValueOrigins;

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
  TlsfAst *ast; ///< Owned expanded objective; no decomposition is constructed.
  const TlsfValueOrigins *value_origins; ///< Optional, owned by ast.
} TlsfConversionResult;

/// Parse, validate, expand and adapt once, then print the whole objective.
/// effective_target is "Mealy", "Moore", or NULL to retain the source target.
/// Returns NULL on invalid/unsupported input or allocation failure; diagnostics
/// follow the library's diagnostic stream. Finite semantics are unsupported.
/// No cover, certificates, composition or residual clusters are constructed.
[[nodiscard]] TlsfConversionResult *tlsf_convert(const char *spec_text,
                                                 const char *effective_target);
/// Request bounded source evidence. Capture exhaustion leaves value_origins
/// null and has no effect on conversion success.
[[nodiscard]] TlsfConversionResult *
tlsf_convert_ex(const char *spec_text, const char *effective_target,
                bool capture_value_origins);
/// Accepts NULL. Frees the result and every owned string/array.
void tlsf_conversion_result_free(TlsfConversionResult *result);

#ifdef __cplusplus
}
#endif
#endif
