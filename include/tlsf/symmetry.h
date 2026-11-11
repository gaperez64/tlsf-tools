#ifndef TLSF_SYMMETRY_H
#define TLSF_SYMMETRY_H

#include "tlsf/convert.h"
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
  TLSF_SYMMETRY_OK,
  TLSF_SYMMETRY_INVALID,
  TLSF_SYMMETRY_NO_MEMORY,
  TLSF_SYMMETRY_ERROR,
} TlsfSymmetryStatus;

typedef enum {
  TLSF_SYMMETRY_ADJACENT,
  TLSF_SYMMETRY_ROTATION,
} TlsfSymmetryKind;

typedef enum {
  TLSF_SYMMETRY_NONE,
  TLSF_SYMMETRY_CYCLIC,
  TLSF_SYMMETRY_SYMMETRIC,
} TlsfSymmetryVerdict;

typedef struct {
  size_t range; ///< Index into result->ranges.
  TlsfSymmetryKind kind;
  const size_t *image; ///< n_aps entries: inputs followed by outputs.
} TlsfSymmetryGenerator;

/// Census diagnostics, including unsuccessful candidates. Only generators
/// contain AP permutations; generator is SIZE_MAX when verification failed.
typedef struct {
  TlsfSymmetryKind kind;
  const uint16_t *image; ///< hi-lo+1 entries: image[i] is the image of lo+i.
  size_t generator;      ///< Index into result->generators, or SIZE_MAX.
  const char *reason;    ///< NULL for a verified candidate.
} TlsfSymmetryCandidate;

typedef struct {
  uint16_t lo, hi;
  const uint32_t *families; ///< Indices into conversion->indexed_families.
  size_t n_families;
  const TlsfSymmetryCandidate *candidates;
  size_t n_candidates;
  TlsfSymmetryVerdict verdict;
  const char *reason; ///< NULL unless family metadata prevents verification.
} TlsfSymmetryRange;

typedef struct {
  size_t n_aps;
  const TlsfSymmetryRange *ranges;
  size_t n_ranges;
  const TlsfSymmetryGenerator *generators;
  size_t n_generators;
  const char *reason; ///< NULL, or why the objective could not be verified.
} TlsfSymmetryResult;

/// Verify declared index permutations of the converted whole objective.
/// Families with identical bounds move together; other APs remain fixed.
/// Ranges are sorted by (lo, hi); candidates are adjacent transpositions then
/// rotation. Ranges with fewer than two indices have verdict NONE and no
/// candidates or generators. Only verified, nonidentity, bijective,
/// input/output-preserving AP maps appear in generators, in candidate order.
///
/// Equality uses AND/OR associativity and commutativity and EQUIV
/// commutativity. Inequality is inconclusive. For at least two indices,
/// SYMMETRIC means every adjacent swap verified; otherwise CYCLIC means the
/// rotation verified, otherwise NONE.
/// This is a lower bound, not a largest-subgroup claim. Enum families permute
/// bits. Unsupported/deep objectives succeed with a reason and no generators.
///
/// Borrows an immutable conversion for this call only. The result owns all
/// returned storage and survives conversion destruction; its indices retain
/// the conversion's ordering. No global state or diagnostic stream is used.
/// Sets *result to NULL on error, including allocation failure (NO_MEMORY).
/// NULL arguments or an invalid AP partition return INVALID. No exception
/// crosses the C API. Free a successful result with tlsf_symmetry_result_free.
[[nodiscard]] TlsfSymmetryStatus
tlsf_symmetry_detect(const TlsfConversionResult *conversion,
                     TlsfSymmetryResult **result);

/// Accepts NULL. Frees the result and every owned array/string.
void tlsf_symmetry_result_free(TlsfSymmetryResult *result);

#ifdef __cplusplus
}
#endif
#endif
