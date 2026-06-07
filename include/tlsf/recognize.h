#ifndef TLSF_RECOGNIZE_H
#define TLSF_RECOGNIZE_H

/// recognize.h — syntactic template-candidate recognition over a constraint
/// cover.  These are *candidates only*: a match annotates a constraint (and may
/// group several into a template block) but never asserts the block is
/// solvable. Side-condition checking and certification belong to a later
/// milestone.
///
/// Recognized single-constraint shapes: response `G(r -> F g)`, mutex
/// `G(!(a && b) ...)`, pure-recurrence `G F x`, persistence `F G x`,
/// reachability `F g`, guarded-next-assignment `G(alpha -> X o)` / `X[!] o`,
/// toggle-register `G(t -> (X o <-> !o))`, reaction `G(alpha -> o)`,
/// fixed-delay-response `G(r -> X^k o)`, definition `G(o <-> theta)`,
/// delayed-definition `G(X o <-> theta)` / `X[!] o`, safety-invariant `G(B)`
/// with `B` temporal-free.
/// Multi-constraint block: responses + a grant mutex ⇒ `arbiter_candidate`.

#include "tlsf/cover.h"

/// Annotate every constraint in `cov` with its template candidates and build
/// the template blocks.  Idempotent; allocates from `cov->arena`.
void recognize_all(ConstraintCover *cov);

#endif // TLSF_RECOGNIZE_H
