#ifndef TLSF_EXPAND_H
#define TLSF_EXPAND_H

/// expand.h — high-level construct expansion pass.
///
/// expand() takes a TlsfSpec whose GLOBAL section may contain PARAMETERS and
/// DEFINITIONS (including bus notation and pattern calls), and produces an
/// equivalent spec in the basic fragment: no GLOBAL section, all formula lists
/// contain only basic LTL nodes (no NODE_DEF_CALL, NODE_BUS_INDEX,
/// NODE_PATTERN, NODE_INT_VAR, NODE_SET, NODE_SET_ENUM, NODE_FORALL,
/// NODE_EXISTS).
///
/// Expansion order (matches syfco):
///   1. Resolve parameters  — evaluate integer expressions, bind values.
///   2. Inline definitions  — substitute DEF_CALL nodes with (possibly
///      instantiated) definition bodies; handles recursion detection.
///   3. Unroll bus signals  — expand bus[i] references, replace set
///      comprehensions with explicit conjunctions/disjunctions.
///   4. Instantiate patterns — expand high-level pattern nodes.
///
/// Parameter overrides allow the caller to set parameter values different
/// from the spec defaults (used by the --param CLI flag).
///
/// Returns 0 on success, -1 on error (message written to stderr).

#include "tlsf/spec.h"

/// A single parameter override: name=value pair.
typedef struct {
  const char *name;  ///< parameter name (need not be interned)
  int64_t value;
} ParamOverride;

/// Expand all high-level constructs in-place.
///
/// @param spec       The specification to expand (modified in-place).
/// @param overrides  Array of parameter overrides (may be nullptr).
/// @param n_overrides  Length of overrides array.
/// @returns 0 on success, -1 on failure.
[[nodiscard]] int expand(TlsfSpec *spec,
                          const ParamOverride *overrides,
                          size_t n_overrides);

#endif // TLSF_EXPAND_H
