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
#include "tlsf/normalize.h"
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

typedef enum {
  CAND_RESPONSE,
  CAND_DEFINITION,
  CAND_RECURRENCE,
  CAND_REACHABILITY,
  CAND_PERSISTENCE,
  CAND_DELAYED_DEF,
  CAND_TOGGLE,
  CAND_FIXED_DELAY,
  CAND_MUTEX,
  CAND_ARBITER,
} CandidateKind;

typedef struct {
  int32_t guard;
  int32_t target;
} ResponseCandidate;

typedef struct {
  int32_t output;
} DefinitionCandidate;
typedef struct {
  int32_t output;
} RecurrenceCandidate;
typedef struct {
  int32_t output;
} ReachabilityCandidate;
typedef struct {
  int32_t output;
} PersistenceCandidate;
typedef struct {
  int32_t output;
} DelayedDefCandidate;
typedef struct {
  int32_t output;
} ToggleCandidate;

typedef struct {
  int32_t output;
  uint32_t steps;
} FixedDelayCandidate;

typedef struct {
  ApSet members;
} MutexCandidate;

typedef struct {
  CandidateKind kind;
  uint32_t *constraint_ids;
  uint32_t nconstraints;
  union {
    ResponseCandidate response;
    DefinitionCandidate definition;
    RecurrenceCandidate recurrence;
    ReachabilityCandidate reachability;
    PersistenceCandidate persistence;
    DelayedDefCandidate delayed_def;
    ToggleCandidate toggle;
    FixedDelayCandidate fixed_delay;
    MutexCandidate mutex;
  } u;
} TemplateCandidate;

typedef struct {
  uint32_t id;
  Role role;
  bool assumption_side;
  bool guarantee_side;
  bool invariant_wrapped; ///< REQUIRE/ASSERT (implicitly under G)
  bool is_safety;         ///< syntactic class (classify_formula on nnf)

  Node *formula;       ///< original (expanded) AST; semantic source
  Node *nnf;           ///< NNF copy (original is left intact)
  Node *match_formula; ///< equivalent formula for recognizers/certifiers
  Node
      *route_formula; ///< equivalent formula for residual/routing (may be NULL)

  ApSet inputs, outputs;
  ApSet pos_outputs, neg_outputs;  ///< output occurrence polarity (in NNF)
  ApSet cur_outputs, next_outputs; ///< output timing (under X or not)

  const char **candidates; ///< template-candidate names (recognize.h)
  uint16_t candidate_count;
  uint16_t candidate_cap;
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
  TemplateCandidate *template_candidates;
  uint32_t template_candidate_count;
  uint32_t template_candidate_cap;
} ConstraintCover;

/// The formula recognizers/certifiers should parse: the normalized
/// `match_formula` when set, else the original.  Equivalence-preserving, so a
/// candidate found here is valid for the original constraint.
static inline Node *constraint_match_formula(const Constraint *c) {
  return c->match_formula ? c->match_formula : c->formula;
}

/// The formula residual/routing should use: the normalized `route_formula` when
/// set, else the original.
static inline Node *constraint_route_formula(const Constraint *c) {
  return c->route_formula ? c->route_formula : c->formula;
}

/// Build the constraint cover from an already-expanded spec.  When `split` is
/// true each section formula is decomposed into its top-level conjuncts (one
/// constraint each, equivalence-preserving).  Returns nullptr on OOM.
[[nodiscard]] ConstraintCover *cover_build(TlsfSpec *spec, bool split);

/// Set each constraint's `match_formula` to the normalization of its `formula`
/// under `opts` (does not mutate `formula`).  No-op when the schedule is empty.
bool cover_apply_match_normalization(ConstraintCover *cov,
                                     const TlsfNormOptions *opts,
                                     TlsfNormStats *stats);

/// Parse `schedule`, soundness-check it for the match phase (rejecting unsafe /
/// finite-word-incompatible rules via `tool`), and apply it to the cover's
/// `match_formula`.  Returns false on a parse or soundness error.
bool cover_match_normalize(ConstraintCover *cov, const char *schedule,
                           bool finite, const char *tool, TlsfNormStats *stats);

/// Append a candidate template name to a constraint (used by recognize.c).
void constraint_add_candidate(ConstraintCover *cov, Constraint *c,
                              const char *name);

/// Append/find typed recognizer payloads for candidate-specific data.
[[nodiscard]] TemplateCandidate *
constraint_add_candidate_payload(ConstraintCover *cov, Constraint *c,
                                 CandidateKind kind);
[[nodiscard]] const TemplateCandidate *
constraint_find_candidate_payload(const ConstraintCover *cov,
                                  const Constraint *c, CandidateKind kind);

#endif // TLSF_COVER_H
