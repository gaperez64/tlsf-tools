#ifndef TLSF_OBFUSCATE_H
#define TLSF_OBFUSCATE_H

/// obfuscate.h — semantics-preserving TLSF obfuscation.
///
/// tlsf_obfuscate() parses a TLSF specification, removes the cues a solver
/// should not depend on, prints the result as standard TLSF (GLOBAL section
/// kept, so parametric input stays parametric), and verifies it before
/// returning it:
///
///   - RENAME gives every identifier a neutral name: signals and buses,
///     parameters, definitions and their arguments, enum types and labels,
///     big-operator binders and pattern variables. The renaming is one
///     bijection on spellings, so it preserves which occurrences share a
///     name, and with it scoping, shadowing and arity overloading. Names are
///     a kind letter and a number, numbered by a seeded permutation of first
///     occurrence order; they never derive from the original spelling. INFO
///     TITLE and DESCRIPTION become neutral text and TAGS are dropped.
///     SEMANTICS and TARGET are kept.
///   - REORDER permutes INPUTS and OUTPUTS declarations, the formulas of each
///     section, parameters, definitions and enum types, and swaps the
///     operands of `&&` and `||` in section formulas. Swaps skip operands
///     whose shape is observable: guards, call arguments, set elements and
///     index or bound expressions, and every formula of a spec that uses a
///     structural pattern guard (`~`). Bus bit order, binder ranges, case
///     order and parameter values never change.
///
/// Comments are never printed, so the //#!SYNTCOMP trailer goes in any mode.
/// The same input, options and seed always give byte-identical output.
///
/// Self-check: the output is parsed again, and both it and the input are
/// expanded (the input with the overrides; the output carries them as
/// parameter values). The two expansions must declare the same inputs and
/// outputs under the renaming, have the same SEMANTICS and TARGET, and have
/// equal multisets of formulas in every section, comparing formulas up to the
/// renaming and up to associativity and commutativity of `&&` and `||`
/// (which also tolerates name-dependent ordering inside the expander).
/// Bounded-temporal metadata takes part in the comparison. The check needs
/// every parameter to have a value.

#include "tlsf/expand.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum TlsfObfuscateMode {
  TLSF_OBFUSCATE_RENAME = 1u << 0,
  TLSF_OBFUSCATE_REORDER = 1u << 1,
  TLSF_OBFUSCATE_ALL = TLSF_OBFUSCATE_RENAME | TLSF_OBFUSCATE_REORDER,
} TlsfObfuscateMode;

typedef enum TlsfObfuscateStatus {
  TLSF_OBFUSCATE_OK,
  TLSF_OBFUSCATE_INVALID,      ///< bad options, or the input does not parse
  TLSF_OBFUSCATE_UNEXPANDABLE, ///< the input does not expand for the check
  TLSF_OBFUSCATE_CHECK_FAILED, ///< the output is not equivalent to the input
  TLSF_OBFUSCATE_NO_MEMORY,
} TlsfObfuscateStatus;

/// What an original name denoted. A spelling used for several things (say a
/// parameter and a function argument that shadows it) has one entry per kind,
/// all with the same obfuscated name.
typedef enum TlsfObfuscateKind {
  TLSF_OBFUSCATE_INPUT,
  TLSF_OBFUSCATE_OUTPUT,
  TLSF_OBFUSCATE_PARAMETER,
  TLSF_OBFUSCATE_ENUM_TYPE,
  TLSF_OBFUSCATE_ENUM_LABEL,
  TLSF_OBFUSCATE_DEFINITION,
  TLSF_OBFUSCATE_ARGUMENT, ///< a definition's formal argument
  TLSF_OBFUSCATE_BINDER,   ///< a big-operator bound variable
  TLSF_OBFUSCATE_PATTERN,  ///< a structural pattern variable
  TLSF_OBFUSCATE_FREE,     ///< an identifier nothing declares
  /// An expanded signal (a scalar, or bus bit `name_i`) as it appears in the
  /// basic fragment, LTL output and AIGER symbol tables.
  TLSF_OBFUSCATE_INPUT_SIGNAL,
  TLSF_OBFUSCATE_OUTPUT_SIGNAL,
} TlsfObfuscateKind;

typedef struct TlsfObfuscateEntry {
  const char *original;
  const char *obfuscated;
  TlsfObfuscateKind kind;
} TlsfObfuscateEntry;

typedef struct TlsfObfuscateOptions {
  unsigned mode; ///< TlsfObfuscateMode bits; zero is invalid
  uint64_t seed;
  const ParamOverride *overrides; ///< applied as tlsf2tlsf --param does
  size_t n_overrides;
  /// Test hook, zero otherwise. After the transform: 1 exchanges the first
  /// input and output declarations, 2 negates the first formula of the first
  /// non-empty section, 3 flips TARGET, 4 truncates the printed text, and 5
  /// renames the first definition but not its calls. The self-check must
  /// reject each.
  unsigned test_fault;
} TlsfObfuscateOptions;

typedef struct TlsfObfuscateResult {
  char *text; ///< obfuscated TLSF, NUL-terminated; null unless OK
  size_t size;
  /// Renaming in discovery order (declarations first), then the expanded
  /// signals. Empty when RENAME is not set. Owned by the result.
  TlsfObfuscateEntry *entries;
  size_t entry_count;
  char message[256]; ///< why the call failed
  void *storage;     ///< internal
} TlsfObfuscateResult;

/// Obfuscate `size` bytes of TLSF source. On any status but OK, `text` is
/// null and `message` says why. Clear the result after every call.
[[nodiscard]] TlsfObfuscateStatus
tlsf_obfuscate(const char *source, size_t size,
               const TlsfObfuscateOptions *options,
               TlsfObfuscateResult *result);

void tlsf_obfuscate_result_clear(TlsfObfuscateResult *result);

/// "input", "output", "parameter", "enum-type", "enum-label", "definition",
/// "argument", "binder", "pattern", "free", "input-signal", "output-signal".
[[nodiscard]] const char *tlsf_obfuscate_kind_name(TlsfObfuscateKind kind);

/// The obfuscated spelling of `original` as `kind`, or null.
[[nodiscard]] const char *
tlsf_obfuscate_lookup(const TlsfObfuscateResult *result, const char *original,
                      TlsfObfuscateKind kind);

/// Write the renaming as TSV: a header `original obfuscated kind`, then one
/// line per entry. Returns false on a write error.
[[nodiscard]] bool tlsf_obfuscate_write_map(FILE *out,
                                            const TlsfObfuscateResult *result);

#ifdef __cplusplus
}
#endif

#endif // TLSF_OBFUSCATE_H
