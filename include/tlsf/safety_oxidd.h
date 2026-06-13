#ifndef TLSF_SAFETY_OXIDD_H
#define TLSF_SAFETY_OXIDD_H

/// safety_oxidd.h — in-process safety-game solver on OxiDD BDDs.
///
/// A drop-in replacement for the AbsSynthe subprocess solve step: instead of
/// writing the `Aig` game to AIGER, spawning AbsSynthe, and reading a strategy
/// AIGER back, it compiles the game's cones into BDDs, runs the controllable
/// predecessor (`cpre`) safety fixpoint in process, and extracts a Skolem
/// strategy as an `Aig`.  See `architecture.md`.
///
/// Only compiled when the OxiDD feature is enabled (`HAVE_OXIDD`).

#include "tlsf/aiger.h"

/// Solve the safety game `game` (env-first / Mealy; inputs whose name starts
/// with `controllable_` are the controllable moves, output `bad` is the unsafe
/// predicate, latches are state with reset values).  Takes ownership of `game`
/// and frees it.
///
/// On a realizable game, returns a strategy `Aig` in the same shape AbsSynthe's
/// read-back produced: uncontrollable inputs as inputs, the game's latches as
/// memory, each controllable driven by an output named `controllable_<sig>`
/// (so the caller's `aig_strip_output_prefix("controllable_")` recovers the
/// spec output name).  On an unrealizable game sets `*unreal = 1` and returns
/// nullptr; on an internal error returns nullptr with `*unreal = 0` (caller
/// falls back to ltlsynt, exactly like the AbsSynthe path).
[[nodiscard]] Aig *solve_safety_oxidd(Aig *game, int *unreal);

#endif // TLSF_SAFETY_OXIDD_H
