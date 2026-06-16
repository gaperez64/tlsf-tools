#ifndef TLSF_GR1_OXIDD_H
#define TLSF_GR1_OXIDD_H

#include "tlsf/aiger.h"

/// Solve a GR(1) game encoded in `game` (the standard AbsSynthe AIGER format:
/// controllable inputs prefixed `controllable_`, `bad` output for safety,
/// justice[] for system Büchi goals, fair[] for environment fairness) using the
/// Piterman-Pnueli-Sa'ar tri-nested fixpoint on OxiDD BDDs.
///
/// Ownership: takes and frees `game`.  On win, returns a strategy `Aig` with
/// uncontrollable inputs, the game's latches plus m one-hot goal-counter
/// latches, and each controllable driven by a `controllable_<sig>` output.
/// On loss sets `*unreal = 1` and returns nullptr.  On internal error returns
/// nullptr without setting `*unreal` (caller should fall back).
[[nodiscard]] Aig *solve_gr1_oxidd(Aig *game, int *unreal);

#endif // TLSF_GR1_OXIDD_H
