# TASKS — towards a fast, effective synthesis preprocessor

**Goal.** tlsf-tools decomposes a TLSF spec, certifies what it can with closed-form
templates, solves residual *safety* clusters with AbsSynthe, and forwards only the
hard *liveness* residual to `ltlsynt`/`strix` — aiming to be **net faster** and
**never less complete** than bare `ltlsynt`.

Current state, corpus solve-rate, speed-vs-`ltlsynt`, and honest caveats live in
[`BENCHGRAPH.md`](BENCHGRAPH.md) (rerun with `scripts/benchgraph.py`). The
synthesis pipeline (`tlsfgraph` → `tlsftemplates` → `tlsfresidual` → `tlsfcompose`,
with the vendored AbsSynthe safety/GR(1) backend, the self-verification gate, and
W/R-safety + GR(1) encodings) is built and tested. This file tracks only the
**open levers**.

## Goals (metrics)

Measured by `scripts/benchgraph.py` over `benchmarks/tlsf` (2545 specs, 20 s /
6 GB caps), against standalone `ltlsynt --tlsf`. "A fast preprocessor" =
**never less complete, and net-faster.** Baseline is the latest BENCHGRAPH.md run.

| Metric | Now (`62fec9d`) | Target | Moved by |
|---|---|---|---|
| **Completeness deficit** — ltlsynt solves, we don't | **~10** | **0** (hard req: never worse) | §1 |
| ↳ false-UNREAL (output-free assumption clusters) | **0** (fixed) | 0 | §1 gap #2 ✓ |
| ↳ backend FAILED / timed out | 2 / 8 | 0 | §1, §2 |
| **Speed, aggregate** `base/ours` (both-solved) | **×0.44** | **≥ 1.0** (net-faster) | §2 (OxiDD) |
| Speed, median | parity (22 vs 16 ms) | ≥ 1.0 | §2 (OxiDD + cost routing) |
| **Wins** — ltlsynt can't do in budget, we can | 17 | grow | §3 |
| Self-contained (no ltlsynt) | 192 (7.5 %) | grow | §1, §3 |

Order of attack: **§1 completeness to 0** (correctness floor — gap #2 alone is
~−74), then **§2 speed to ≥1.0** (the actual product claim), then **§3 reach** for
upside. Rerun the benchmark after each lever; the deficit and aggregate-speed
cells are the two that define success.

## 1 · Completeness — never fail where `ltlsynt` succeeds (PRIORITY)

The benchmark's "completeness gaps" (we FAIL where bare `ltlsynt` solves) are the
one place we are strictly worse. The uppercase-atom parse bug is fixed; the
remaining gaps are:

- [x] **Input-only assumption clusters.** Fixed in `62fec9d`: clusters whose
  clustering key equals `A` (cov->aps.count sentinel = no output APs) are now
  skipped in both `--aiger` and text-plan paths.  Dropped ~74 false-UNREAL cases
  on the sweap corpus; verified by golden test `input_gua_skip`.
- [ ] **Composition-soundness edge.** A guarantee whose only outputs are
  template-eliminated can leave an input-only unrealizable residual (e.g.
  `G(req → F false)` from free-output substitution of a response's grant). Audit
  the free-output rule so substitution never strands a still-referenced obligation.

## 2 · Speed — be net-faster, not just self-contained

On the corpus the median AbsSynthe-contributing spec is rough parity but the
aggregate is *slower* (BENCHGRAPH.md): a fixed AbsSynthe spawn + CUDD-init cost
hurts on specs `ltlsynt` does in milliseconds, plus a tail of slow BDD solves.

- [ ] **Replace the AbsSynthe subprocess with an in-process BDD solver on OxiDD**
  — the slowness is the fixed spawn + CUDD-init cost, not algorithms. Detailed
  prototype plan in [`architecture.md`](architecture.md): keep the game encoders,
  swap only the solve step (`run_abssynthe_game` → `solve_safety_oxidd`); unlocks a
  persistent manager, parallel clusters, and WL-keyed controller reuse. Safety
  first behind a feature flag, GR(1) after; AbsSynthe stays as fallback.
- [ ] **Gate AbsSynthe (or its OxiDD successor) behind a cheap cost heuristic**
  (cluster size / fan-out / AP count) so the heavy backend only runs where it
  wins; forward trivially-easy clusters straight to `ltlsynt`. The wins to
  preserve: specs `ltlsynt` cannot do in the time budget that we solve.

## 3 · Reach — solve more of the residual

- [ ] **Liveness backend (the biggest block).** ~2/3 of residuals are pure
  liveness (F/U/GF/Büchi) that need a real liveness game, not a syntactic
  certificate. Either a fixpoint backend or trusting the complete solver more
  (see §4). ~27 % of this tail are genuinely *unrealizable* specs.
- [ ] **Remaining W/R-safety shapes** (gate-protected, exactly encodable):
  nested weak-until `G(req → (A W B))` with inner `W`/`R` (needs sub-monitors);
  U-shaped responses `G(req → X(a U b))` (*first* confirm the unsound cases are
  Spot-tractable, else it repeats the lever-2 trap); the `zoo5` over-constraint
  (an `X`-bearing input-only guarantee invariant whose late-detected violation
  mis-times against the `!released` gate — currently a sound fallback).
- [ ] **GR(2) / generalized-Rabin** for the `amba_gr+` family (beyond GR(1)).
- [ ] **AbsSynthe BDD perf / GR(1)-aware abstraction** for big amba (`pb_10+`).

## 4 · Trust & verification

- [ ] **Trust the complete solver's UNREALIZABLE verdict** on exactly-encoded
  clusters (would close the ~27 % unrealizable share of the liveness tail without a
  liveness solver).
- [ ] **Scalable verifier** (BDD/symbolic, not Spot) to lift the self-verification
  gate's check-tractability ceiling, so widenings can be admitted on big specs.

## Dead ends (measured — do not redo)

- **Finer per-cluster assumption scoping** — sound, but +0 on the SYNTCOMP needle.
- **Bounded liveness reduction** — plateaus (+0); fairness is the lever, not more
  bounded operators.
- **`G`-over-∧ distribution (lever 2) behind the gate** — ~0 sound lift, and the
  gate can't protect the big unsound specs (Spot OOMs there).
- **More recognizer shapes without a solver** — lift is recognizer-gated only up
  to the GR(1) wall; the solver, not more patterns, is what moves the needle there.

## Invariants (every change)
clang-format (LLVM) + clang-tidy clean · tests green · coverage ≥75% via
`gcovr` with the compiler's matching `gcov` · valgrind clean · no JSON
(DIMACS-style lines) · self-contained where CI runs (flex/bison/gcc/valgrind
only — no spot/ltlsynt/AbsSynthe). Heavy runs bounded (`ulimit -v` + `timeout`).
