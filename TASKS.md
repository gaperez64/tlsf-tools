# TASKS — towards a fast, effective synthesis preprocessor

**Goal.** tlsf-tools decomposes a TLSF spec, certifies what it can with closed-form
templates, solves residual *safety* and *GR(1)* clusters with OxiDD (in-process BDD
solver), and forwards only the hard *liveness* residual to `ltlsynt`/`strix` — aiming
to be **net faster** and **never less complete** than bare `ltlsynt`.

Current state, corpus solve-rate, speed-vs-`ltlsynt`, and honest caveats live in
[`BENCHGRAPH.md`](BENCHGRAPH.md) (rerun with `scripts/benchgraph.py`). The
synthesis pipeline (`tlsfgraph` → `tlsftemplates` → `tlsfresidual` → `tlsfcompose`,
with the in-process OxiDD BDD backend (safety + GR(1)), the self-verification gate, and
W/R-safety + GR(1) encodings) is built and tested. This file tracks only the
**open levers**.

## Goals (metrics)

Measured by `scripts/benchgraph.py` over `benchmarks/tlsf` (2545 specs, 20 s /
6 GB caps), against standalone `ltlsynt --tlsf`. "A fast preprocessor" =
**never less complete, and net-faster.** Baseline is the latest BENCHGRAPH.md run.

| Metric | Now (`5fd19e5`) | Target | Moved by |
|---|---|---|---|
| **Completeness deficit** — ltlsynt solves, we don't | **8** (false-UNREALs) | **0** (hard req: never worse) | §1 |
| ↳ false-UNREAL (output-free assumption clusters) | **8** (selection-ltl×4, tsl_paper×4) | 0 | §1 gap |
| ↳ backend FAILED | **0** | 0 | ✓ |
| ↳ timed out | **0** | 0 | ✓ |
| **Speed, aggregate** `base/ours` (both-solved) | **×35.18** (ours 4.8 s vs base 170.4 s) | **≥ 1.0** ✓ | §2 ✓ |
| Speed, median OxiDD-contributing | **×4.66** (4 ms vs 23 ms) | ≥ 1.0 ✓ | §2 ✓ |
| **Wins** — ltlsynt can't do in budget, we can | **150** (selection-ltl×77, sweap×73) | grow | §3 |
| Self-contained (no ltlsynt) | **787 / 2545 (30.9 %)** | grow | §1, §3 |

**Last benchgraph run: 2026-06-14 (`5fd19e5`).** OxiDD is the sole backend (safety +
GR(1)); benchmark shows ×35 aggregate speedup on both-solved, 787/2545 self-contained,
150 wins where ltlsynt times out. Completeness deficit is 8 false-UNREALs from
output-free assumption clusters (see §1 open item below). §2 speed goal met. Remaining
work is §3 reach and closing the 8 false-UNREALs.

## 1 · Completeness — never fail where `ltlsynt` succeeds (PRIORITY)

The benchmark's "completeness gaps" (we FAIL where bare `ltlsynt` solves) are the
one place we are strictly worse. The uppercase-atom parse bug is fixed; the
remaining gaps are:

- [x] **Input-only assumption clusters.** Fixed in `62fec9d`: clusters whose
  clustering key equals `A` (cov->aps.count sentinel = no output APs) are now
  skipped in both `--aiger` and text-plan paths.  Dropped ~74 false-UNREAL cases
  on the sweap corpus; verified by golden test `input_gua_skip`.
- [x] **Backend FAILED cases.** Confirmed gone: per-family gap scan (lily/tsl_paper/
  sweap/ltl2dpa/gui_glue_code_synthesis) found 0 specs where ltlsynt succeeds but
  our tool fails without UNREALIZABLE verdict. The 2 pre-fix backend FAILEDs were
  likely output-free cluster synthesis attempts that also triggered the ltlsynt
  fallback in an unresolvable way; the key=A skip resolved them.
- [x] **Remaining ~8 timeouts.** Confirmed gone: 0 timeouts in current benchgraph run.
- [ ] **8 false-UNREALs (open).** selection-ltl-2025×4, tsl_paper×4 — output-free
  assumption clusters that OxiDD correctly calls unrealizable (the cluster has no
  outputs), but ltlsynt solves the whole spec via a different decomposition. Root
  cause: the `key=A` skip only drops clusters whose *clustering key* is `A`; these
  particular clusters have outputs but their safety game has none (assumption-only
  safety constraints). Diagnosis and fix TBD.
- [ ] **Composition-soundness edge (theoretical).** A guarantee whose only outputs are
  template-eliminated can leave an input-only unrealizable residual (e.g.
  `G(req → F false)` from free-output substitution of a response's grant). No
  observed cases in the corpus; worth auditing the free-output rule but not blocking.

## 2 · Speed — be net-faster, not just self-contained

The OxiDD in-process solver removes subprocess spawn and CUDD re-init overhead;
aggregate benchmark is pending rerun (corpus not present locally).

- [x] **Replace the AbsSynthe subprocess with an in-process BDD solver on OxiDD**
  — safety solver in `src/safety_oxidd.c` (phases 1–3 complete); GR(1) solver in
  `src/gr1_oxidd.c` (PPS tri-nested fixpoint). OxiDD vendored as `external/oxidd` git
  submodule; mandatory (no AbsSynthe fallback). All safety + GR(1) clusters solved
  in-process. 16 verify-aiger-oxidd safety tests + 9 verify-aiger-oxidd-gr1 tests pass;
  benchmark rerun pending.

## 3 · Reach — solve more of the residual

- [ ] **Liveness backend (the biggest block).** ~2/3 of residuals are pure
  liveness (F/U/GF/Büchi) that need a real liveness game, not a syntactic
  certificate. Either a fixpoint backend or trusting the complete solver more
  (see §4). ~27 % of this tail are genuinely *unrealizable* specs.
- [x] **W/R R-collapse with complex rhs.** `G(a R b)` now recurses into `b`
  via `g_body_wr_supported`/`wr_emit_g_body*`, enabling specs where `b` itself
  contains W/R responses (e.g. Automata, SensorInit, SensorPart families).
- [x] **W/R AIG x-depth undercount.** Added `wr_body_x_depth` that recurses
  into W/R operands; used in `abssynthe_safety_wr_x_depth` for G nodes so that
  X operators nested inside W/R sub-expressions (e.g. G(req→X(a R (b→X c))))
  contribute the correct AIG history-latch depth. Fixes KitchenTimerV4-V9 and
  SensorPart in the selection-ltl set (18/23 now self-contained, up from 11).
- [x] **abssynthe_eligible conflict.** Extended g_body_wr_supported patterns
  (Pattern A/B) were leaking into abssynthe_eligible, routing W/R formulas to
  build_abssynthe_game (wrong path). Fixed by introducing strict
  g_body_direct_supported / abssynthe_safety_direct_supported used only in the
  direct-path gate.
- [ ] **Remaining W/R-safety shapes** (gate-protected, exactly encodable):
  nested weak-until `G(req → (A W B))` with inner `W`/`R` in operands (needs
  sub-monitors; MusicAppFeedback pattern); X in initial-constraint conjuncts
  (KitchenTimerV10); SensorSelector `AND(G, IMPL)` top-level structure needs
  direct-path to handle IMPL-under-AND; U-shaped responses `G(req → X(a U b))`.
  The 5 remaining selection-ltl failures are: Sensor, MusicAppSimple (liveness),
  KitchenTimerV10 (X in initial), MusicAppFeedback (deeply nested W-in-W),
  SensorSelector (IMPL-under-AND without W/R, not handled by any current path).
- [ ] **GR(2) / generalized-Rabin** for the `amba_gr+` family (beyond GR(1)).
- [ ] **OxiDD BDD perf / GR(1)-aware abstraction** for big amba (`pb_10+`).

## 4 · Trust & verification

- [x] **Trust W/R UNREALIZABLE verdict.** W/R monitor encoding is exact; UNREALIZABLE
  from the OxiDD solver on a W/R game is propagated rather than reset to 0 and re-tried
  with ltlsynt. (Direct/strict/GR(1) paths all trust UNREALIZABLE.)
- [ ] **Trust UNREALIZABLE on bounded/GR(1) paths** (over-constraining encodings;
  requires careful analysis before trusting — currently correct to fall back).
- [ ] **Trust complete solver UNREALIZABLE on liveness tail** (would close ~27 %
  unrealizable share without a liveness solver).
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
only — no spot/ltlsynt). Heavy runs bounded (`ulimit -v` + `timeout`).
