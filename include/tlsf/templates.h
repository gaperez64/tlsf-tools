#ifndef TLSF_TEMPLATES_H
#define TLSF_TEMPLATES_H

/// templates.h — move recognized template *candidates* (GSNF) to *certified* /
/// *solved* blocks (CSNF).  A block is only SOLVED when a sound side condition
/// passes and a controller/decoder + certificate is produced; otherwise it
/// stays CANDIDATE (or, for a standalone mutex, CERTIFIED as a safety
/// invariant).  Nothing is removed from the problem here (residual is M6).
///
/// Side conditions are *syntactic and conservative*: they may decline to
/// certify a solvable block, but never certify an unsound one.

#include "tlsf/cover.h"
#include <stdio.h>

typedef enum {
  CSNF_CANDIDATE, ///< recognized, not certified
  CSNF_CERTIFIED, ///< side condition checked + certificate (e.g. mutex safety)
  CSNF_SOLVED,    ///< certified and a controller/decoder produces its outputs
} CsnfStatus;

typedef struct Csnf Csnf;

/// Certify the cover's templates.  `want` is a bitmask of TPL_* (0 = all).  If
/// `certify` is false every block is left CANDIDATE (the `--candidates` view).
/// Returns a malloc-backed model; free with csnf_free.  nullptr on OOM.
enum {
  TPL_DEFINITION = 1u << 0,
  TPL_ROUND_ROBIN = 1u << 1,
  TPL_GUARDED_NEXT = 1u << 2,
  TPL_MUTEX = 1u << 3,
  TPL_ARBITER = 1u << 4,
  TPL_RESPONSE = 1u << 5,
  TPL_PERSISTENCE = 1u << 6,
  TPL_REACHABILITY = 1u << 7,
  TPL_REACTION = 1u << 8,
  TPL_DELAYED_DEF = 1u << 9,
  TPL_INVARIANT = 1u << 10,
  TPL_SET_RESET = 1u << 11,
  TPL_TOGGLE = 1u << 12,
  TPL_ALL = 0,
};

[[nodiscard]] Csnf *templates_certify(ConstraintCover *cov, unsigned want,
                                      bool certify);
void csnf_free(Csnf *c);

// ---------------------------------------------------------------------------
// Composition: turn the per-block local certificates into a sound whole-spec
// decomposition.  Each certifier is local; two SOLVED blocks could in principle
// drive the same output, or a decoder could read an output another block (or a
// residual constraint) constrains.  csnf_compose keeps a maximal subset of
// SOLVED blocks whose owned outputs are conflict-free, globally free w.r.t. the
// residual, and acyclic across combinational decoders; the rest fall back into
// the residual.  Sound: the accepted controllers compose with each other and
// with any controller for the residual.
// ---------------------------------------------------------------------------

typedef enum {
  CONFLICT_DUP_OUTPUT,    ///< two accepted blocks drive the same output
  CONFLICT_SHARED_OUTPUT, ///< an accepted output is constrained in the residual
  CONFLICT_DECODER_CYCLE, ///< combinational decoders form a dependency cycle
} ConflictKind;

typedef struct {
  ConflictKind kind;
  int32_t output; ///< AP index of the offending output
  uint32_t block; ///< the ejected block
} Conflict;

/// A solved combinational output and the value its controller assigns it
/// (`o := value`): definition θ, reaction ⋁guards, reachability/persistence
/// `true`.  Substituting `value` for `o` in the residual eliminates `o`
/// soundly.
typedef struct {
  int32_t output;    ///< AP index of the eliminated output
  const Node *value; ///< its combinational value (in the cover arena)
} Elim;

typedef struct {
  bool fully_solved;         ///< residual empty after composition
  uint32_t naccepted;        ///< SOLVED blocks kept in the decomposition
  uint32_t nresidual;        ///< constraints left in the residual
  bool *accepted_block;      ///< per block: kept (length = block count)
  bool *residual_constraint; ///< per constraint: in the residual
  Conflict *conflicts;
  uint32_t nconflicts;
  // Residual reduction (composable certification):
  Elim *elim;            ///< combinational outputs eliminated by substitution
  uint32_t nelim;        ///< == eliminated combinational outputs
  bool *elim_constraint; ///< per constraint: discharged by a combinational ctrl
  uint32_t neliminated;  ///< constraints discharged (not in the residual)
  uint32_t nowned_outputs; ///< outputs determined by a sound controller
} CsnfComposition;

/// Substitute `value` for every leaf occurrence of the AP named `name` in `n`,
/// returning a (possibly new) node in `a`.  Used to eliminate solved
/// combinational outputs from the residual.
[[nodiscard]] const Node *node_subst(Arena *a, const Node *n, const char *name,
                                     const Node *value);

/// Compute a sound composition of the certified model.  Returns a malloc-backed
/// result; free with csnf_composition_free.  nullptr on OOM.
[[nodiscard]] CsnfComposition *csnf_compose(const Csnf *c);
void csnf_composition_free(CsnfComposition *r);

/// Emit the model: `text` is human-readable, `csnf` is the DIMACS-style line
/// format (see README).
void csnf_emit_text(FILE *out, const Csnf *c, bool solve);
void csnf_emit_lines(FILE *out, const Csnf *c, const char *source, bool solve);

/// Tally block statuses and derived counts (any out-pointer may be nullptr).
/// `dependent` counts SOLVED definition decoders; `residual` counts
/// constraints not in any SOLVED block.
void csnf_counts(const Csnf *c, uint32_t *solved, uint32_t *certified,
                 uint32_t *candidate, uint32_t *residual, uint32_t *dependent);

/// The template names recognized so far (for --list-templates).
extern const char *const TEMPLATE_NAMES[];
extern const int TEMPLATE_NAMES_COUNT;

#endif // TLSF_TEMPLATES_H
