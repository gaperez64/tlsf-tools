#ifndef TLSF_TEMPLATES_INTERNAL_H
#define TLSF_TEMPLATES_INTERNAL_H

/// templates_internal.h — the private CSNF model (`Block`, `struct Csnf`)
/// shared between templates.c (dispatcher, composition, emission) and
/// templates_certify.c (per-template recognizers + certifiers).  These types
/// are deliberately opaque to the rest of the codebase (only `typedef struct
/// Csnf Csnf;` is public, in templates.h); this header is internal to libtlsf's
/// templates module and is not installed.

#include "tlsf/ast.h"
#include "tlsf/cover.h"
#include "tlsf/templates.h" // CsnfStatus, the opaque Csnf typedef

#include <stdint.h>

typedef struct {
  const char *name; // template name
  CsnfStatus status;
  const char *cert; // certificate type, or nullptr
  uint32_t *cids;   // member constraint ids
  uint32_t ncids;
  // artifacts (borrowed Node* into the cover arena; indices into cov->aps):
  int32_t dec_output; // definition decoder output (-1 none)
  const Node *dec_theta;
  int32_t nsf_output; // guarded-next assigned output (-1 none)
  const Node **nsf_guards;
  uint32_t nsf_nguards;
  int32_t sr_output; // set-reset register output (-1 none)
  const Node **sr_set_guards;
  uint32_t sr_nsets;
  const Node **sr_reset_guards;
  uint32_t sr_nresets;
  int32_t tog_output; // toggle register output (-1 none)
  const Node **tog_guards;
  uint32_t tog_nguards;
  int32_t fdelay_output; // fixed-delay response output (-1 none)
  const Node **fdelay_guards;
  uint32_t *fdelay_steps;
  uint32_t fdelay_n;
  int32_t db_output; // deterministic-Buchi switch output (-1 none)
  const Node *db_guard;
  int32_t *cyc_outputs; // round-robin one-hot cycle outputs
  uint32_t cyc_n;
  // free-liveness family (controller is the constant out := true):
  int32_t one_output;  // reachability F o   (-1 none)
  int32_t hold_output; // persistence  FG o  (-1 none)
  int32_t resp_output; // response G(r -> F o) (-1 none); guard read from cid[0]
  int32_t *arb_outputs; // fair-arbiter grant set
  uint32_t arb_n;
  int32_t asg_output; // immediate reaction G(a -> o) assigned output (-1 none)
  const Node **asg_guards;
  uint32_t asg_nguards;
  int32_t reg_output; // delayed-definition register output (-1 none)
  const Node *reg_theta;
  int32_t *inv_outputs;    // safety-invariant Skolem'd outputs
  const Node **inv_values; // their inputs-only Skolem values (o := inv_value)
  uint32_t inv_n;
} Block;

struct Csnf {
  ConstraintCover *cov;
  Block *blocks;
  uint32_t nblocks, bcap;
  bool *solved;  // per constraint: in a SOLVED block
  bool *claimed; // per constraint: already placed in some block
  uint32_t nconstraints;
};

// Verdict-trust class of a certifier (the registry; see block_trust).  An
// UNDER-approximation commits a *strategy* for a liveness obligation — the
// eliminated output has several valid strategies, so substituting the chosen
// one STRENGTHENS the residual: sound for a REALIZABLE verdict, but its
// UNREALIZABLE verdict is not trustworthy.  An EXACT certifier extracts the
// value the constraint *forces* (a definition/register/exclusive reaction) and
// substitutes it, which is equivalence-preserving.  No certifier weakens
// (OVER-approximates); false-REALs would come from OVER paths and are caught by
// the `--verify` controller model-check.
typedef enum {
  TRUST_EXACT, // forced-value substitution (equivalence-preserving)
  TRUST_UNDER, // strategy commitment (strengthening): UNREAL not trustworthy
} VerdictTrust;

// Classify a block's certifier by name.  UNDER certifiers rely on a coupling
// guard to stay sound: reachability/persistence on the output being free
// (output_constrained_elsewhere); the scheduler families (round-robin / arbiter
// / server / global-recurrence) on the grants being free outside the block;
// safety-invariant on a memoryless Skolem choice.
VerdictTrust block_trust(const Block *b);

// Shared AST helper (defined in templates.c; used by the certifiers).
bool occurs_in(const Node *n, const char *name);

// Per-template certifiers (defined in templates_certify.c; dispatched from
// templates_certify() in templates.c).  Each scans the cover for its template
// shape and, when `certify`, fills in the matching Block artifacts.
void certify_round_robin(Csnf *c, unsigned want, bool certify);
void certify_definition(Csnf *c, unsigned want, bool certify);
void certify_set_reset_register(Csnf *c, unsigned want, bool certify);
void certify_toggle_register(Csnf *c, unsigned want, bool certify);
void certify_fixed_delay_response(Csnf *c, unsigned want, bool certify);
void certify_global_recurrence_switch(Csnf *c, unsigned want, bool certify);
void certify_guarded_next(Csnf *c, unsigned want, bool certify);
void certify_mutex(Csnf *c, unsigned want, bool certify);
void certify_arbiter(Csnf *c, unsigned want, bool certify);
void certify_response(Csnf *c, unsigned want, bool certify);
void certify_persistence(Csnf *c, unsigned want, bool certify);
void certify_reachability(Csnf *c, unsigned want, bool certify);
void certify_reaction(Csnf *c, unsigned want, bool certify);
void certify_delayed_definition(Csnf *c, unsigned want, bool certify);
void certify_invariant(Csnf *c, unsigned want, bool certify);

#endif // TLSF_TEMPLATES_INTERNAL_H
