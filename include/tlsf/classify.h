#ifndef TLSF_CLASSIFY_H
#define TLSF_CLASSIFY_H

/// classify.h — safety/liveness classification of NNF formulas.
///
/// A formula is classified as SAFETY if, after NNF, it contains no
/// NODE_F, NODE_U, or NODE_M nodes anywhere in its syntax tree.
/// (In NNF these are exactly the liveness modalities under positive polarity.)
///
/// classify_spec() partitions the GUARANTEE and ASSERT formula lists
/// into safety and liveness buckets.  ASSUME/REQUIRE/INITIALLY/PRESET
/// are left in their original lists and tagged as environment constraints.
///
/// The classification result is returned as a ClassifiedSpec; the node
/// pointers are shared with the original TlsfSpec (no copying).

#include "tlsf/ast.h"
#include "tlsf/spec.h"

typedef enum FormulaClass {
  FCLASS_SAFETY,   ///< no F/U/M after NNF
  FCLASS_LIVENESS, ///< contains F, U, or M
} FormulaClass;

typedef struct {
  Node *formula;
  FormulaClass cls;
} ClassifiedFormula;

typedef struct {
  // Guarantee (system) side: partitioned
  ClassifiedFormula *guarantees; ///< arena-allocated array
  uint32_t guarantee_count;

  // Assert (system invariants): partitioned
  ClassifiedFormula *asserts;
  uint32_t assert_count;

  // Environment side: kept as-is (liveness by convention)
  Node **initially;
  uint32_t initially_count;
  Node **preset;
  uint32_t preset_count;
  Node **require;
  uint32_t require_count;
  Node **assume;
  uint32_t assume_count;
} ClassifiedSpec;

/// Classify all formulas in `spec`.
/// NNF must have been applied to all formula lists before calling this.
/// The ClassifiedSpec is allocated in `spec->arena`.
/// Returns nullptr on OOM.
[[nodiscard]] ClassifiedSpec *classify_spec(TlsfSpec *spec);

/// Classify a single NNF formula node.
[[nodiscard]] FormulaClass classify_formula(const Node *n);

#endif // TLSF_CLASSIFY_H
