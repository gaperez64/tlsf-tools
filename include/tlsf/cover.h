#ifndef TLSF_COVER_H
#define TLSF_COVER_H

/// cover.h — the TLSF *constraint cover*: the structured view of an expanded
/// spec before it is flattened to one LTL implication.  Each TLSF section
/// formula becomes one Constraint that keeps its role, assumption/guarantee
/// side, invariant-wrapping, syntactic safety/liveness class, and input/output
/// support (with occurrence polarity and current/next timing).
///
/// Template-candidate recognition (recognize.h) annotates these constraints; it
/// never removes or rewrites them — the cover is candidate-only.

#include "tlsf/apset.h"
#include "tlsf/ast.h"
#include "tlsf/spec.h"

typedef enum {
  TLSF_ROLE_INITIALLY,
  TLSF_ROLE_PRESET,
  TLSF_ROLE_REQUIRE,
  TLSF_ROLE_ASSERT,
  TLSF_ROLE_ASSUME,
  TLSF_ROLE_GUARANTEE,
} Role;

const char *role_name(Role r); ///< uppercase TLSF section name

typedef struct {
  uint32_t id;
  Role role;
  bool assumption_side;
  bool guarantee_side;
  bool invariant_wrapped; ///< REQUIRE/ASSERT (implicitly under G)
  bool is_safety;         ///< syntactic class (classify_formula on nnf)

  Node *formula; ///< original (expanded) AST
  Node *nnf;     ///< NNF copy (original is left intact)

  ApSet inputs, outputs;
  ApSet pos_outputs, neg_outputs;  ///< output occurrence polarity (in NNF)
  ApSet cur_outputs, next_outputs; ///< output timing (under X or not)

  const char **candidates; ///< template-candidate names (recognize.h)
  uint16_t candidate_count;
  uint16_t candidate_cap;

  // Recognizer-extracted roles (-1 / empty when not applicable).
  int32_t resp_guard;   ///< request AP index (response)
  int32_t resp_target;  ///< grant AP index (response)
  int32_t def_output;   ///< defined output AP index (definition)
  int32_t rec_output;   ///< recurrence target output AP index (G F o)
  int32_t reach_output; ///< reachability target output AP index (F o)
  int32_t pers_output;  ///< persistence target output AP index (F G o)
  int32_t
      ddef_output; ///< delayed-definition output AP index (G(X o <-> theta))
  int32_t
      toggle_output;   ///< toggle-register output AP index (G(t -> (X o<->!o)))
  ApSet mutex_members; ///< output AP indices in a mutex
  bool has_mutex;
} Constraint;

/// A multi-constraint template candidate (e.g. arbiter = responses + mutex).
typedef struct {
  const char *template_name;
  uint32_t *constraint_ids;
  uint32_t count;
} TemplateBlock;

typedef struct {
  Arena *arena;
  TlsfSpec *spec;
  ApTable aps;
  Constraint *items;
  uint32_t count;
  uint32_t cap; ///< allocated `items` slots (grow-by-doubling)
  TemplateBlock *blocks;
  uint32_t block_count;
} ConstraintCover;

/// Build the constraint cover from an already-expanded spec.  When `split` is
/// true each section formula is decomposed into its top-level conjuncts (one
/// constraint each, equivalence-preserving).  Returns nullptr on OOM.
[[nodiscard]] ConstraintCover *cover_build(TlsfSpec *spec, bool split);

/// Append a candidate template name to a constraint (used by recognize.c).
void constraint_add_candidate(ConstraintCover *cov, Constraint *c,
                              const char *name);

#endif // TLSF_COVER_H
