#ifndef TLSF_GRK_OXIDD_H
#define TLSF_GRK_OXIDD_H

#include "tlsf/aiger.h"

/// Solve a generalized-reactivity (Streett) game encoded in `game` (the
/// standard AIGER format with pair-tagged justice[]/fair[] records — see
/// aig_justice_pair/aig_fairness_pair) using the symbolic Piterman-Pnueli Rabin
/// fixpoint (Banerjee-Majumdar-Mallik-Schmuck-Soudjani, arXiv:2202.07480, eq 7)
/// specialized to the no-live-edge case (Apre == Cpre).
///
/// Ownership: takes and frees `game`.  Currently computes the winning region /
/// realizability (gated to the two-single-set-pair case); finite-memory
/// strategy extraction is staged, so it returns nullptr (caller falls back to
/// ltlsynt). Sets `*unreal = 1` when the game is unrealizable.
[[nodiscard]] Aig *solve_grk_oxidd(Aig *game, int *unreal);

#endif // TLSF_GRK_OXIDD_H
