#ifndef TLSF_PRECHECK_UNREAL_H
#define TLSF_PRECHECK_UNREAL_H

/// precheck_unreal.h — fast, sound structural UNREALIZABLE pre-check at the
/// TLSF level (the analog of ltlsynt's `try_create_direct_strategy`
/// input-only-`G` shortcut).  It inspects the propositional safety fragment of
/// the expanded cover and proves unrealizability via a one-step
/// environment-win BDD test:
///
///   EnvWin(i) = ∀o. ( A(i,o) ∧ ¬G(i,o) ) = ¬ ∃o. ¬(A ∧ ¬G)
///
/// where `G` is the conjunction of all step-0 boolean *guarantee* bodies and
/// `A` the conjunction of all step-0 boolean *assumption* bodies.  When
/// `EnvWin ≠ ∅` the environment has an input it can replay forever that keeps
/// every (boolean) assumption true while no controller output can satisfy the
/// guarantees — a sound UNREALIZABLE certificate.
///
/// Verdict-trust class: OVER-approximation (`TRUST_OVER`).  It refutes a
/// *weakening* of the spec — it keeps every assumption and drops only
/// *temporal* guarantees — so its UNREALIZABLE verdict is the trustworthy
/// direction (fewer guarantees still UNREAL ⟹ original UNREAL) and it never
/// claims REALIZABLE.  It bails (returns false) whenever an assumption is
/// temporal, since dropping such an assumption would instead *strengthen* the
/// environment and risk a false UNREAL — a strict superset of the
/// `cover_has_liveness_assumption` UNREAL-trust concern, so no re-validation of
/// its verdict is needed.
///
/// Only compiled into `tlsfcompose`, which is built only with OxiDD.

#include "tlsf/cover.h"

#include <stdbool.h>

/// True iff the spec is provably unrealizable by the boolean-fragment
/// one-step environment-win argument.  Returns false ("not proven") on any
/// non-easy shape, finite semantics, OOM, or unsupported node — it never
/// reports realizable.
[[nodiscard]] bool precheck_trivially_unreal(const ConstraintCover *cov);

/// Dual of the above: true iff the spec is provably *realizable* by a one-step
/// combinational-controller win.  When every guarantee is boolean-`G` (no
/// temporal guarantee) and `∃outputs. G_bool` is valid over all inputs, the
/// Skolem function `o = f(i)` is a memoryless Mealy controller that satisfies
/// the guarantees regardless of the environment.
///
/// Verdict-trust class: UNDER-approximation (`TRUST_UNDER`).  It refutes
/// unrealizability of a *strengthening* of the spec — it drops every assumption
/// (env unrestricted) and bails on any temporal guarantee — so its REALIZABLE
/// verdict is trustworthy (the harder, assumption-free spec being realizable
/// implies the original is) and it never claims UNREALIZABLE.  Mealy-only: the
/// Skolem controller reads the current input, so it bails on Moore (and on
/// finite) semantics.  Emits only a verdict (no controller), so the caller
/// short-circuits in plan mode, not under `--aiger`.
[[nodiscard]] bool precheck_trivially_real(const ConstraintCover *cov);

#endif // TLSF_PRECHECK_UNREAL_H
