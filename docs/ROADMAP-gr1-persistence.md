# Generalized Rabin(1): add FG-persistence guarantees to the OxiDD GR(1) solver

> Roadmap for the next preprocessor reach push. Status: planned.

## Context

`tlsf-tools` is a TLSF synthesis **preprocessor**: in-process OxiDD BDD solvers
carve off safety + GR(1) clusters; the hard liveness residual goes to `ltlsynt`.
The first accurate post-W/R-fallback benchmark (commit `bb2c5f7`) shows the
preprocessor's real value is **specs ltlsynt times out on** (77 today) and
self-contained reach (25.8%). Against a fast ltlsynt 2.14.1, broad speedup is
~parity, so growth must come from the **"ltlsynt can't do it" axis**.

Benchmark data (`BENCHGRAPH.tsv`) on what's *not* self-contained:

| class | count | note |
|---|---|---|
| pure liveness (F/U/GF/Büchi) | 1478 | correctly ltlsynt's job (automata) |
| W/R-safety | 103 | ltlsynt-fast → marginal speed value |
| **GR(2+) generalized reactivity** | **98** | **ltlsynt-slow / times out → BDD wins** |

The 98 GR(2+) include the 21 `amba/amba_gr1/specs/amba_gr+_pb_*` family (the
marquee ltlsynt-timeout specs) + 60 selection-ltl-2025.

**Decisions:** target the GR(2) family (scoped, not full generalized-Rabin); keep
**speedup** as the primary headline metric (consistent — amba_gr+ are ltlsynt
*timeouts*, so solving them fast is a large speedup win).

**Root cause (verified by reading the residual of `amba_gr+_pb_2`):** its
cluster-0 liveness is `(GF a) → (GF γ₁ ∧ GF γ₂ ∧ FG δ)` — a single GF
assumption (GR(1)-fine), multiple GF guarantees (GR(1) already handles the `⋀_j`),
plus **one persistence guarantee `FG δ`**. The *only* thing beyond GR(1) is the
`FG` (persistence). `gr1_collect` (`src/compose_analysis.c:451`) has no FG case,
so it falls through `global_ok` → returns false → routed to ltlsynt as "GR(2+)".

Scoped target: **Generalized Rabin(1)** (Ehlers 2011) — GR(1) + a conjunction of
`FG cₖ` persistence guarantees. A *bounded, known* fixpoint extension of the
existing PPS solver, NOT a full Rabin/Streett rewrite.

## Goal

Recognize and solve `(⋀ᵢ GF aᵢ) → (⋀ⱼ GF bⱼ ∧ ⋀ₖ FG cₖ)` in-process so the
amba_gr+ family (and the GR(1)+persistence subset of the 98) become
self-contained and contribute timeout-wins to the speedup metric. The
self-verification gate (`controller_violates_spec`, `compose_solve.c`) keeps any
wrong encoding sound — a mis-synthesis falls back to ltlsynt.

## Approach

### 1. Recognizer — `src/compose_analysis.c` + `include/tlsf/compose_internal.h`
- Add `match_fg(n)`: `F G x` with `x` Boolean → `x` (mirror `match_gf`, line 428).
- Extend `Gr1Parts` (compose_internal.h:45):
  `const Node *persistence[GR1_MAX_JUSTICE]; uint32_t npersistence;`.
- In `gr1_collect` (line 451), guarantee-side `else` branch: after
  `match_gf` / `match_response` / `NODE_W`, add a `match_fg` case → `persistence[]`.
  Assumption-side FG is out of scope (reject → ltlsynt).
- `aig_gr1_parts` (line 575): accept clusters with `npersistence > 0`.

### 2. Game builder — `src/compose_games.c` (`build_aig_gr1_game`, ~857)
- Expose each `cₖ` as a combinational signal (compiled at the cluster's X-depth,
  like the safety bodies) and pass them via a new `Aig.persist[]` mirroring
  `Aig.just[]` in `include/tlsf/aiger.h` + `src/aiger.c`. No Büchi "pending"
  monitor needed for persistence.

### 3. Solver — `src/gr1_oxidd.c` (`solve_gr1_oxidd`, PPS fixpoint at 288–370) — the core work
Let `C = ⋀ₖ cₖ` (persistence region). The system must eventually confine play to
`C` forever while meeting the Büchi goals under fairness. Extend the existing
ν_Z / ⋀_j μ_Y / ν_X fixpoint:

```
W = νZ. ⋀ⱼ μY. νX. cpre[(Z ∩ bⱼ ∩ C) ∪ (Y ∩ C) ∪ (X ∩ ¬fair)]
```

— Büchi progress + the `Y` "wait" are confined to `C`; the `¬fair` escape is not
(system may leave `C` only when env is unfair). Validate the exact form against
Spot empirically with the test harness. **When `npersistence == 0` it must reduce
exactly to today's fixpoint** (regression safety). Extend Skolem strategy
extraction (lines 458–617) to drive controllables toward `C` once the Büchi rank
is met.

### 4. Routing — `src/main_tlsfcompose.c`
`use_gr1` already calls `aig_gr1_parts`; with persistence accepted it routes
amba_gr+ to `solve_gr1_game`. The existing `if (!sub) → ltlsynt fallback` stays
(sound on any miss). No new routing logic.

## Critical files
- `include/tlsf/compose_internal.h` — `Gr1Parts.persistence[]`
- `src/compose_analysis.c` — `match_fg`, `gr1_collect`, `aig_gr1_parts`
- `include/tlsf/aiger.h` + `src/aiger.c` — `Aig.persist[]` (mirror `just[]`)
- `src/compose_games.c` — `build_aig_gr1_game` emit persistence signals
- `src/gr1_oxidd.c` — generalized Rabin(1) fixpoint + Skolem (the hard part)
- `meson.build` + `test/cases/` — new Spot-verified gr1 persistence test(s)

## Verification
- **Reduction safety:** with `npersistence==0`, `solve_gr1_oxidd` bit-identical to
  today; existing `verify_aiger_oxidd_gr1_*` (15 tests) stay green.
- **New unit:** a tiny `(GF a) → (GF b ∧ FG c)` spec under
  `scripts/verify_aiger_ltl.py` (Spot equivalence) + an unrealizable variant (xfail).
- **Acceptance:** `TLSFCOMPOSE_DEBUG=1 build-oxidd/tlsfcompose --split --aiger
  --ltlsynt ltlsynt amba_gr+_pb_2_pe_.tlsf` routes cluster 0 to OxiDD GR(1) and
  Spot-verifies; the self-verification gate passes (no fallback).
- **Sanitizers:** `CC=clang meson test -C build-san` clean (gcc libasan absent).
- **Benchmark delta:** rerun `scripts/benchgraph.py` (6 GB cgroup cap, quiet box);
  expect amba_gr+ + the GR(1)+persistence subset of the 98 to move
  "GR(2+)"→self-contained, growing unique-solves/speedup.

## Risks / effort
- **Solver fixpoint is the risk** (high effort, correctness-delicate): the exact
  generalized Rabin(1) formula + Skolem extraction. Mitigation: the
  self-verification gate makes any wrong encoding *sound* (falls back to ltlsynt),
  and Spot tests catch wrongness before benchmarking. Recognizer/builder are
  moderate.
- Specs in the 98 that are NOT GR(1)+persistence (conditional-fairness
  `GF a→GF b` assumptions, multiple Rabin pairs) stay on ltlsynt. Measure how many
  of the 98 the persistence-only extension captures; conditional-fairness
  (reducible to plain GF via a pending-latch monitor) is a clean **follow-up**.
