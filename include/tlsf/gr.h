#ifndef TLSF_GR_H
#define TLSF_GR_H

/// gr.h — Generalized Reactivity (GR(1)) fragment recognition.
///
/// A specification is in the GR(1) fragment when its LTL formula has the shape
///
///   (θe ∧ G ρe ∧ ⋀ GF Je)  →  (θs ∧ G ρs ∧ ⋀ GF Js)
///
/// i.e. every conjunct of the environment and system sides is one of:
///   - an initial condition  θ : a purely Boolean (propositional) formula;
///   - a transition/safety   G ρ : G of a Boolean formula over the current and
///     next (single X) values of the signals; or
///   - a justice/fairness    G F J : "infinitely often" a Boolean (or
///     transition) formula.
///
/// The TLSF sections map onto these: INITIALLY/PRESET are initial conditions,
/// REQUIRE/ASSERT are invariants (implicitly under G), and ASSUME/GUARANTEE
/// are general formulas.
///
/// The spec must be expanded first (no high-level nodes remaining).

#include "tlsf/spec.h"

/// GR fragment level: 0 for GR(0) (safety only), 1 for GR(1) (with justice),
/// or -1 if the spec is not in the GR fragment.
int gr_level(const TlsfSpec *spec);

#endif // TLSF_GR_H
