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

/// Generalized Reactivity level: 0 for GR(0) (safety only), k >= 1 for GR(k),
/// or -1 if the spec is not in the GR fragment.
///
/// k is the number of distinct antecedents in the CNF of the liveness
/// implication (⋀ assumption GF/FG) -> (⋀ guarantee GF/FG), over the GF
/// literals (FG x is treated as ¬GF¬x); the antecedent of a clause is the set
/// of GF literals occurring negatively in it.
int gr_level(TlsfSpec *spec);

#endif // TLSF_GR_H
