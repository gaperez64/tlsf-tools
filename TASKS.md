# TASKS — raise the self-contained solve rate

Working branch: `tlsfgraph` (do **not** merge). Full rationale + measurements in
the approved plan (`.claude/plans/sorted-meandering-thompson.md`).

Strategy (two prongs): route the **safety** residual to **AbsSynthe** (the LTL
residual is ~99% safety; `ltlsynt` is overkill), and add cheap **closed-form
templates** to pre-discharge outputs and shrink the game.

Status legend: `[ ]` pending · `[~]` in progress · `[x]` done · `[!]` blocked/revised

## Complexity measurement (monolith → residual)
Goal: stop scoring on the binary "fully solved" metric and instead measure
whether decomposition lowers the complexity handed to the synthesis backends.
Synthesis cost is ~exponential in controllable outputs and in operator class
(parity vs safety vs solved), so a spec we never fully close can still be
exponentially cheaper after templates + clustering.
- [x] **Residual-complexity columns in `tlsfbenchgraph`** — per spec, alongside
  the monolith vector, emit `residual_clusters`, `residual_outputs`,
  `largest_residual_cluster_outputs`, `residual_liveness_clusters`,
  `residual_size_norm`. The residual is the **composition residual** (every
  accepted SOLVED block removed via `!comp->residual_constraint[i]`, so
  `fully_solved` ⇔ empty residual), partitioned into output-disjoint clusters
  with the shared `residual_cluster_keys`/`residual_build_cluster` helpers and
  classified with the same `to_nnf`+`classify_formula` path as the monolith
  safety/liveness columns. Goldens `test/cases/bench.tsv` (now also covers a
  factored safety spec + a liveness residual) and `test/cases/bounded_corpus.tsv`
  updated.
- [x] **Aggregate the monolith→residual delta** in `scripts/bounded_corpus.py`
  (hardest sub-game dimensionality, liveness→safety class drops, factoring,
  residual size) and add residual-class + hardest-game plots/tables to
  `scripts/benchgraph_plots.py`.
- [x] **Corpus baseline + BENCHGRAPH.md** — full bounded `--split` runs over
  `tlsf` (2545) / `tlsf-fin` (2487); regenerated `docs/benchgraph/` plots
  (`residual_class.png` cluster-level safety/liveness, `residual_gamesize.png`
  monolith-vs-residual hardest game) and added the "Residual complexity
  (monolith → residual)" BENCHGRAPH.md section + a key takeaway. Findings:
  - Templates barely shrink the hardest game (`tlsf` 5.0→4.9, `tlsf-fin`
    50.3→50.3 mean outputs in the largest cluster) — the big multi-output
    transition cores survive.
  - **Clustering is the lever**: **746/2545 (29%) `tlsf` and 1422/2487 (57%)
    `tlsf-fin` specs factor into ≥2 independent output-disjoint games**; residual
    formula is 76.7% of the monolith on `tlsf`.
  - Liveness is sparse per clause but pervasive per spec; clustering isolates it,
    so **43% of `tlsf` (21% of `tlsf-fin`) residual independent games are
    pure-safety / AbsSynthe-eligible**. Next lever: finer clustering that peels
    each safety game off the per-spec liveness tail (not more closed-form
    templates).

## Finer clustering (per-cluster relevant-assumption scoping)
- [x] **Relevant-assumption scoping in `residual_build_cluster`** (`src/residual.c`).
  Each cluster keeps its own `key==kk` constraints and attaches from the global
  (input-only) assumption pool only those *relevant*: a transitive **cone of
  influence** over shared signals, dropping **liveness assumptions from
  safety-only clusters** (a liveness assumption can never prevent a finite-time
  safety violation). Sound: synthesizing against `Eᵢ ⊆ E` still yields a
  controller valid under the full `E`. Gated to **non-strict** semantics (under
  strict semantics the assumption-driven `W` structure feeds the AbsSynthe
  strict-safety encoder; pruning reshapes it into an unrecognized nested-`G`).
  New fixture `cluster_prune.tlsf` (+ `.compose` golden) shows a safety cluster
  de-contaminated from `G F !r` via the class lever; `cluster_assume.residual`
  regenerated (cluster `y` drops the irrelevant `G a`). 184 tests green,
  clang-tidy clean, coverage 89% on residual.c, valgrind clean.
- [!] **Honest finding: does NOT move the SYNTCOMP needle.** The 300-spec
  `--split` samples are unchanged (safety clusters 43%/22% before==after; residual
  size −0.14%). The corpus liveness clusters are **guarantee-driven** (responses
  `G(req→F grant)`, amba `U`-shaped obligations), not assumption-contaminated, so
  no cluster flips class. The completeness rule correctly **keeps** each cluster's
  fairness (e.g. `G F HREADY` stays on the `READY2` response game in
  `amba_decomposed_tburst4`). Finer clustering is sound + leaner and the right
  foundation, but the genuine lever for the response clusters is a **GR(1)/Büchi
  backend** (see "Factor robot-style GR(1) structure" below) — finer clustering
  enables it by scoping each GR(1) game to only its relevant fairness.

## Bounded GR(1)/Büchi backend (via the existing AbsSynthe safety solver)
Architecture: a *complete* GR(1) solver is easiest as an AbsSynthe extension (its
BDD engine, `CPre`, strategy extraction, and a justice/fairness AIGER frontend —
parsed then ignored at `aig.cpp:83-84` — are all present). But the lighter,
self-contained first step is a **bounded reduction to safety**, solved by the
*existing* AbsSynthe; the complete extension is the follow-on for the
fairness-bearing tail.
- [x] **Bounded-liveness rewrite + routing** (`src/main_tlsfcompose.c`).
  `bound_liveness` rewrites `F x` (AbsSynthe-Boolean `x`) to `x|Xx|..|X^k x` at
  *positive* polarity only, so `G F g` → `G(g|..|X^k g)` and `G(req→F grant)` →
  `G(req→grant|..|X^k grant)` become pure-safety games the existing encoder
  handles. **Soundness asymmetry**: bounding a *guarantee* is sound (stronger
  obligation ⇒ implies the unbounded `F`); bounding an *assumption* is unsound, so
  a negative-polarity `F` (a fairness assumption) is left intact, fails
  `abssynthe_eligible`, and the cluster stays on `ltlsynt`. A bounded miss
  (unrealizable at `k`) **falls back to ltlsynt**, never a false failure. Bound
  `k` via `--bound N` / `$ABSSYNTHE_BOUND` (default 4); harness `--bound`.
  New fixture `bounded_resp.tlsf` (fairness-free response game) + fake `.aag`
  golden + real-AbsSynthe verify test; `cluster_prune` now fully solves without
  ltlsynt. 187 tests green, clang-tidy clean, coverage 77.6%, valgrind clean.
  **Soundness verified** against real AbsSynthe + Spot: the `k`-bounded
  controller satisfies the UNBOUNDED spec (`verify_aiger_abssynthe_real_bounded_resp`,
  `cluster_prune`).
- [x] **Bounded `U`/`W`/`R`/`M`** — `bound_liveness` now also rewrites
  `a U b → ⋁_i(⋀_{j<i}X^j a ∧ X^i b)` at positive polarity, and strengthens
  `a W b`/`a R b`/`a M b` to a bounded until (`⟸ a U b` / `⟸ b U(a∧b)`, sound).
  Routing gate widened to `has_weak_until`/`has_release`. Fixtures
  `bounded_until` + `bounded_wuntil` (fake goldens + real verify). 191 tests
  green, clang-tidy clean, coverage 77.7%, valgrind clean, soundness verified.
  **Measured (full tlsf, fake, `--bound 4`): eligibility 229 → 266 (+37).**
- [!] **Honest finding: fairness, not more operators, is the lever.** The
  remaining tail (2279) is ~2/3 fairness-bearing; the `U`/`W`/`R` extension barely
  moved the "liveness (non-GR)" bucket (1734→1716) because those clusters carry a
  relevant `G F a` *assumption* that can't be bounded soundly. Pure-safety-release
  `W`/`R` (~149) need an exact "released"-latch monitor (smaller prize).
- [x] **Bounded GR(1) (fairness-gated counters)** — `abssynthe_gr1_parts`
  recognizes `(SafetyAssume ∧ G F a) → (SafetyGua ∧ ⋀ Justice)`;
  `build_abssynthe_gr1_game` gives each justice a saturating counter gated on the
  fairness `a` (`gr1_saturate`), so "met within k occurrences of `a`" — sound
  (never bounds the env's absolute timing). Fixtures `gr1_spec` + `gr1_response`
  (fake goldens + real verify against the **unbounded** `G F a → …` spec). 195
  tests green, clang-tidy clean, coverage 77.8%, valgrind clean.
- [!] **PLATEAU: bounded reduction is +0 on the corpus here, ceiling at 266.**
  `F` +98 → 229, `U`/`W`/`R`/`M` +37 → 266, bounded GR(1) **+0** → 266. The clean
  GR(1) shape (single fairness, `F`-responses, no initial conditions) **doesn't
  occur in SYNTCOMP**: real GR(1) is multi-fairness, `U`-shaped (amba
  `!READY U (HREADY ∧ …)`), with initial conditions (`!DECIDE`). Shape-matched
  bounded reduction has hit its ceiling.
- [x] **Complete GR(1) fixpoint (AbsSynthe submodule extension) — done.**
  Solver-side shape limits removed (multi-fairness, multi-justice, no `k`-bound)
  and wired into tlsf-tools end to end with Spot-verified controllers. C++/CUDD,
  spans two repos. The remaining corpus lever is now the *front-end* recognizer
  (see the recognizer-gated note below), not the solver.
  - [x] **GR(1) realizability** (AbsSynthe `native-dev-par`, CI green). The
    Piterman–Pnueli–Sa'ar fixpoint
    `Z=νZ.⋀ⱼμY.⋁ᵢνX.[(Jˢⱼ∧cpre Z)|cpre Y|(¬Jᵉᵢ∧cpre X)]` over `cpre=¬upre(¬·)`
    (`solveGR1`, `algos.cpp`), consuming the justice/fairness AIGER records it
    used to ignore (`BDDAIG::sysJustice`/`envFairness`, `aig.cpp`). Realizable
    iff `init⊆Z`. Four hand-built games incl. the fairness-discriminating pair
    (REAL with the `GF req` assumption, UNREAL without).
  - [x] **GR(1) strategy — single Büchi goal** (AbsSynthe `native-dev-par`, CI
    green). `gr1NondetStrategy` replays the `μY` layers at the converged `Z`
    (with the inner `νX` waiting-sets) and builds the rank-descent move relation;
    the existing `synthAlgo`/`bdd2aig`/`finalizeSynth` emit the controller (no
    new latches needed for one goal). `gr1verify.sh` model-checks it by
    re-solving the closed system (`cpre`→∀env) — rejects a hand-broken
    controller. 39 tests green, coverage 67.9%, valgrind clean.
  - [x] **GR(1) strategy — multiple goals** (Phase 2b-ii, AbsSynthe
    `native-dev-par`, CI green). `AIG::degeneralizeJustice` rewrites a
    generalized-Büchi guarantee into one goal via the standard degeneralization:
    a deterministic mod-`n` justice counter (`⌈log2 n⌉` new latches, reset 0)
    advances when the pursued goal holds; the `n` justice records become the
    single wrap goal `(counter==n-1)∧goal[n-1]`, so `GF wrap ⟺ ⋀ᵥ GF goalᵥ` and
    the single-goal extraction/emission/model-check apply unchanged. `solve()`
    degeneralizes before BDDAIG construction for multi-goal synthesis (the
    counter is plain AIG gates: sel/jcur/mod-`n` incrementer/accept). Fixtures
    `gr1_two_goals` (+unreal) and `gr1_three_goals` (mod-3, wrap 2→0), state
    (latch) goals. 43 tests green, coverage 68.6%, valgrind clean. **Note:**
    justice goals must be state predicates — goals over controllable *inputs*
    couple latch+input under `cpre` and misbehave (Phase 3's monitors emit state
    predicates).
  - [x] **tlsf-tools integration** (Phase 3, `tlsfgraph`). (a) AIGER 1.9
    justice/fairness *output* in `aiger.c` (`aig_add_justice`/`aig_add_fairness`,
    9-number header) and the reader skips those records so a GR(1) strategy reads
    back for merging. (b) `build_abssynthe_unbounded_gr1_game` emits a real
    justice/fairness game: each justice goal via a deterministic pending monitor
    (`pending' = !violated & !grant & (pending|req)`, `req=true` for recurrence)
    so the justice literal `!pending` is a STATE predicate; each fairness `a`
    sampled into a latch. A broken safety assumption clears the monitors, lifting
    the liveness obligation vacuously. (c) `use_gr1` routes through it (replacing
    bounded `build_abssynthe_gr1_game`/`gr1_saturate`); on miss/unreal it defers
    to ltlsynt to avoid a false UNREAL. (d) Multi-fairness recognized
    (`abssynthe_gr1_parts`, `Gr1Parts.fairness[]`). 197 tests green incl.
    `verify_aiger_abssynthe_real_gr1_{spec,response,multifair}` — Spot confirms
    the controllers satisfy the **unbounded** GR(1) specs (multifair has two
    fairness in one cluster). coverage 77.9%, clang-format clean.
  - [!] **Corpus lift is recognizer-gated, not solver-gated.** Old (bounded) vs
    new (complete) on a 150-spec random `tlsf` sample (`--ltlsynt /bin/false`,
    capped): identical 8/150 fully-AbsSynthe-solved, **0 status changes**. The
    complete solver removed the *solver*-side shape limits (multi-fairness, no
    `k`-bound — proven on `gr1_multifair`), but the broad corpus number doesn't
    move because real GR(1) clusters (e.g. `lift_gr1+`, amba) fail the *front-end*
    `abssynthe_gr1_parts` recognizer: their liveness is `U`-shaped
    (`!READY U (HREADY ∧ …)`) / has initial conditions, not the clean `G F a` +
    recurrence/response it matches (both old and new report "liveness ... not
    AbsSynthe-eligible"). And GR(1) clusters usually coexist with other residual
    clusters that still need ltlsynt.
  - [x] **Recognizer extensions** (Phase 4, `tlsfgraph`). Three verified
    capabilities so more real shapes reach the complete solver:
    (a) **initial conditions** — TLSF renders INITIALLY/PRESET as a nested
    `EnvInit -> (SysInit & (assume -> guarantee))`; `abssynthe_gr1_parts` peels
    them into `Gr1Parts.env_init`/`.sys_init`, and the emitter adds a `first`
    (t=0) marker (env-init breach latches `violated`, sys-init breach adds to
    `bad`). (b) **AND-form** — a cluster with no env safety/init renders as
    `AND(sys_init, G(safety), (AND G F a -> AND justice))` (no outer
    implication); accepted via `gr1_collect_consequent`. (c) **pure weak-until**
    `a W b` (Boolean) — a `released` monitor latch. Fixtures `gr1_init`,
    `gr1_preset`, `gr1_weak`, all Spot-verified against the unbounded spec.
  - [!] **Phase 4 lift is ~0; the real blocker is strict GR(1).** The generalized
    recognizer first *over*-accepted Streett clusters (independent `G F i->G F a`
    pairs, or a bare unconditional `G F a` beside a fairness implication) and
    emitted **wrong** controllers (caught: lilydemo17/18 "controller violates
    formula" under Spot). Fixed: `gr1_collect_consequent` accepts at most ONE
    implication plus only unconditional safety/init; everything else falls back
    to ltlsynt (guard `aiger_streett_not_gr1`). After the fix, old-vs-new on a
    300-spec sample is **17/300 = 17/300, 0 sound gains, 0 regressions** — the
    capabilities are correct but the clean shapes they unlock are rare and the
    headline amba/lift family is blocked by **strict semantics**: amba's
    guarantee is `Sys W !(… & G(EnvSafety))` (a weak-until with a `G` inside the
    release, `SEMANTICS Strict`), i.e. the whole guarantee conditioned on the env
    maintaining its assumption.
  - [x] **Strict GR(1)** (Phase 5, `tlsfgraph`) — **lands the amba_gr1 family.**
    `build_spec_formula` emits strict specs as
    `(S_safety W ¬A_safety) ∧ (E → GUARANTEE)`, `E = A_safety ∧ ASSUME`.
    `gr1_collect_consequent` recognizes the strict `S_safety W ¬A_safety` conjunct
    (G-safety operands, so the Phase-4 pure-weak-until handler does not match) and
    buckets `S_safety` as sys safety/init via `gr1_collect_strict_safety`; the
    `¬A_safety` release is redundant because `A_safety` reappears in `E` and drives
    the existing `violated` latch, so `bad = ¬violated ∧ ¬S_safety` is exactly
    `¬(S_safety W ¬A_safety)` — **no new emitter machinery.** `gr1_collect` also
    buckets initial Booleans (env-init on the assume side); the x-depth-0 assume
    gate relaxes to "encodable" and the assumption window skips early lags where an
    X-depth assume reaches before the window start. Three diverse strict fixtures
    (`gr1_strict`, `_sticky`, `_multi`) Spot-verify against the unbounded strict
    spec. **Measured:** `amba_gr_pb_{2..6}` now solve via AbsSynthe alone (5/8
    sampled; previously 0); `pb_{10,11,12}` are recognized+routed but time out at
    30 s on AbsSynthe's BDD (a solver-perf limit, not recognition). amba is too
    big for Spot to model-check directly, but shares the verified encoding path.
    `amba_gr+` is GR(2) (out of scope for a GR(1) solver). 210 tests green,
    coverage 78.2%.
  - [!] **Solve-rate snapshot + two negative levers.** templates+AbsSynthe
    (no ltlsynt) closes **~5–7%** of specs fully self-contained on capped random
    samples (whole-spec metric: every residual cluster must be AbsSynthe-eligible).
    Residual failure mix (500-sample): 344 "liveness not eligible" (~27% of those
    are *unrealizable* specs needing a verdict), 42 weak-until/release **safety**
    (encodable, unrecognized), 21 GR(2), 10 AbsSynthe-BDD timeouts.
    - **Lever 1 — pass AbsSynthe solver flags (`$ABSSYNTHE_FLAGS`, no default):
      measured, does not help.** GR(1) games dispatch to `solveGR1` before
      `-a`/`-c` are read (no-ops); `-t` *slows* the GR(1) fixpoint
      (amba_gr_pb_8 10 s→19 s); on the slow safety tail the bounded game just
      misses faster. The slow tail is intrinsic to AbsSynthe's BDD GR(1) fixpoint
      (abstraction isn't wired into `solveGR1`) — a real AbsSynthe feature, not a
      flag. Knob kept for experimentation.
    - **Lever 2 — `G(p∧q) ≡ G p ∧ G q` distribution: sound rewrite, but
      REVERTED.** It correctly exposes `G F x` buried in `G(safety ∧ F x …)`
      (round_robin), but widens recognition to complex specs (deep-`X` responses,
      mutual-exclusion liveness over *controllable outputs*, the unrealizable
      round_robins) whose *other* parts the emitter encodes inexactly →
      **controllers that violate the spec** (Spot caught 7/7 newly-"solved" as
      unsound, incl. 4 unrealizable specs wrongly "solved"). The lesson: the
      recognizer's per-conjunct acceptance does **not** guarantee an *exact*
      game, so any widening is unsafe without a gate.
  - [x] **Self-verification gate** (`tlsfgraph`) — the safety mechanism the
    recognizer work was missing. `tlsfcompose --verify PROG` (or
    `$TLSFCOMPOSE_VERIFY`) model-checks each AbsSynthe cluster controller against
    the **original** cluster spec (`PROG --aiger F --formula L`, exit 1 =
    violation, via `controller_violates_spec`) and, on a definite violation,
    discards it and falls back to ltlsynt. The cluster strategy already carries
    cluster-named i/o (controllable_ stripped on read-back), so it matches the
    formula APs. **Inconclusive checks keep the controller** (verified / AP
    mismatch / verifier error / Spot OOM-on-big-amba) so the gate never demotes a
    sound solve nor regresses specs Spot can't check; default off ⇒ no behavior
    change. `scripts/verify_aiger_ltl.py` is the reference Spot verifier. Proven:
    re-applying the reverted G-over-∧ distribution and running an unrealizable
    round_robin under `--verify` turns its unsound rc 0 into a correct ltlsynt
    fallback — the gate catches the exact class that hit lever 2 and the Phase-4
    Streett bug. Tests: gate-keeps (`/bin/true`), gate-falls-back (`/bin/false`),
    real-Spot gate on gr1_spec. 213 tests green.
  - [!] **Lever 2 re-land measured behind the gate: not worth it; the gate's
    protection is verifier-bounded.** With the distribution applied and `--verify`
    on, the **sound** corpus lift is ~0: across seeds 5 and 7 *every* newly-solved
    spec is either confirmed-unsound by Spot (amba_decomposed, lilydemo22,
    round_robin_unreal) or a big `amba_decomposed_pb_*` that is structurally
    identical to the confirmed-unsound base but too large for Spot to check. The
    second clause is the key limitation: **the gate "keeps on inconclusive", and
    the distribution's unsound cases are exactly the big specs Spot OOMs on, so
    they would *not* be caught.** The gate only de-risks widenings whose failure
    cases are checker-tractable; the `G`-over-∧ distribution is not one. Left
    reverted.
  - [x] **Weak-until / release safety (`W`/`R`) — guarantee + assume + structural,
    exact and Spot-verified.** `a W b`/`a R b` are pure safety, so they encode
    exactly and the gate is fully effective. The direct safety path
    (`build_abssynthe_game`) collapses `G(a W b)≡G(a|b)` / `G(a R b)≡G(b)` to
    invariants and gives a top-level `a W b` a released-monitor latch. Re-armed
    **responses** are now unified across four shapes via `wr_response_parts` +
    `wr_emit_g_body`: `G(req→[X](a W b))` and `G(req→[X](a R b))` (with/without the
    `X`). The non-X variant is active the same step `req` fires (`active =
    (valid&req)|owe`); the X variant is delayed one step (`active = owe`). `a W b`
    releases on `b` and loses on `!a&!b`; `a R b` releases on `a&b` and loses on
    `!b`. **Initial-state constraints** (bare-Boolean conjuncts) are charged only
    on the first valid step via a `first = valid & !seen_valid` rising-edge marker
    (built lazily — `wr_has_initial`/`wr_structural_has_initial` — so games without
    an initial keep their exact old shape and goldens). A new **structural** game
    `build_abssynthe_wr_game` handles `AND(U…, IMPL(A, G))` with `W`/`R` on any
    side: it reuses the verified `wr_emit_guarantee` walk for all three roles
    (unconditional U→`bad`, assume A→`viol_a` driving `violated`/`released`,
    guarantee G→`bad_cond` gated by `!released`). Routed via `use_abs_wr`
    (`wr_structural_supported`).
    **Corpus measurement (429 realizable specs, AbsSynthe-only, this build):**
    78 solve self-contained via AbsSynthe — 52 direct safety, 11 GR(1),
    **8 W/R-structural** (MusicApp×3, OneCounter(Gui), SPI, TwoCounters×2), 7
    bounded. A **soundness pass with the `--verify` gate over all 78** found zero
    wrong controllers and zero new false-UNREALIZABLE from the `W`/`R` work: the
    only flags were 5 pre-existing GR(1) self-verification fallbacks (round_robin,
    sound) and 2 specs (Gamelogic, lilydemo19) whose residual cluster ltlsynt
    *also* calls UNREALIZABLE (genuine, not a backend bug). Fixtures `wr_resp_nox`,
    `wr_rel_resp`, `wr_assume` Spot-verify. `collector_v1` (nested `G(¬x)` in an
    antecedent) and `zoo5` (a recognized cluster whose game compile still misses)
    remain on ltlsynt — sound fallbacks, future work.
  - [x] **Backend wall-clock caps (robustness).** `run_abssynthe_game` now honours
    `$ABSSYNTHE_TIMEOUT` (seconds, 0/unset = unbounded): a hung BDD solve is
    SIGKILLed and the cluster falls back to ltlsynt instead of hanging the tool
    (test `aiger_abssynthe_timeout_fallback`). The self-verification gate
    (`controller_violates_spec`) caps the verifier at `$TLSFCOMPOSE_VERIFY_TIMEOUT`
    (default 30 s); a Spot blow-up on a big formula is treated as *inconclusive*
    (keep the controller) rather than a hang — this is what lets OneCounterGuiA9
    (AbsSynthe solves it in 0.04 s, Spot can't verify it in time) stay
    self-contained.
  - [ ] **Open follow-ons.** (a) Nested weak-until `G(req→(A W B))` where A/B carry
    inner `W`/`R` (MusicAppFeedback) — needs sub-monitors. (b) `zoo5` is *not* a
    compile miss: the game builds (depth 1) but AbsSynthe calls it UNREALIZABLE
    while ltlsynt finds it realizable, i.e. the encoding **over-constrains** it (the
    safe direction — sound ltlsynt fallback, never a wrong controller). Root cause:
    a guarantee invariant with an `X` over inputs only
    (`G(clicked ↔ (activated ↔ X!activated))`) whose violation is detected one step
    late, so the `!released` gating mis-times relative to the assume violation that
    should excuse it. Fixing the X/release timing risks the verified common case;
    left as fallback. (c) U-shaped responses
    `G(req→X(a U b))` behind the gate — *first* confirm the unsound cases are
    Spot-tractable (else same trap as lever 2). (d) AbsSynthe BDD perf / GR(1)-aware
    abstraction for big amba (`pb_10+`). (e) GR(2)/generalized-Rabin for `amba_gr+`.
    (f) A scalable verifier (BDD/symbolic, not Spot) to lift the gate's
    check-tractability ceiling. (g) Trust the complete solver's UNREALIZABLE verdict
    on exact clusters (~27% of the liveness tail).
  - [x] **Speed benchmark (`scripts/benchgraph.py` → BENCHGRAPH.md).** Automates the
    "fast preprocessor" question over the whole corpus: residual **complexity**
    (ltlsynt-disabled self-contained rate + residual shape) and **speed** (full
    pipeline wall vs standalone `ltlsynt --tlsf=SPEC --aiger`), tracking solve
    STATUS so fast failures don't masquerade as wins. Sentinel-delimited section in
    BENCHGRAPH.md, rerunnable; `--from-data` re-renders without re-running. First
    run (commit de82555, 2545 specs, 20 s cap): on AbsSynthe-contributing specs
    where both engines synthesize the **median is rough parity** (22 ms vs 17 ms)
    but **aggregate ×0.47 (slower)** — a tail of AbsSynthe BDD solves outlasts
    ltlsynt, and the fixed AbsSynthe spawn+CUDD-init cost hurts on specs ltlsynt
    does in ms. Real wins: **18 specs ltlsynt cannot do in 20 s that we solve**
    (GR(1) `amba_gr`, large decomposed safety).
  - [ ] **Completeness gaps (PRIORITY, blocks the "fast preprocessor" claim): 80
    specs we FAIL where ltlsynt succeeds** (selection-ltl-2025 ×41, sweap ×39). The
    ltlsynt fallback is handed a malformed interface — e.g. `amba_decomposed_*_pb_*`
    emits a residual whose formula references `HBUSREQ_7` but `residual_print_signals`
    omits it from `--ins/--outs` (the cluster `root` references an AP not in its
    `seen[]` set), so ltlsynt errors out fast instead of solving. Fix the
    formula/`seen`-set consistency (and audit `sweap`). Until fixed we are *less
    complete* than bare ltlsynt on these families.
  - [ ] **Speed lever: skip/curb AbsSynthe on trivial clusters.** The spawn + CUDD
    init is a fixed ~hundreds-of-ms cost; on specs ltlsynt solves in ms it makes us
    net-slower. Gate AbsSynthe behind a cheap size/fan-out heuristic, or reuse a
    persistent solver, so the abstraction only pays where it wins.

> **Tracker note**: the synthesis-graph tracker tasks (#66–#71) are stale —
> superseded by committed work; this file is the source of truth.


> **Updated 2026-06-07**: strong-next `X[!]`, SR-latch / set-reset grouping,
> toggle-register, fixed-delay response, deterministic-Buchi global recurrence,
> multi-guard reaction, AbsSynthe vendor setup, sponsor metadata, the deferred
> `--aiger` partition fix, and the bounded corpus harness are cleared.
> AbsSynthe backend is in progress: the process/merge path works for non-finite
> `G` safety clusters with Boolean/nested-`X` bodies and safety assumptions, and
> vanilla AbsSynthe gate-renaming output is recovered via `controllable-gate`
> comments.

## Prong B — closed-form templates (do first; cheap, also shrinks the game)
- [x] **Strong-next `X[!]` soundness handling.**
  Under finite (LTLf) semantics `G(α→X[!]o)` is **violated at the last trace
  position** when α holds there (strong-next demands a successor that doesn't
  exist), so a `next o := OR(guards)` controller does **not** soundly discharge
  it. Implemented:
  - `X[!]` is recognized as a guarded-next / delayed-definition candidate
    wherever ordinary `X` is matched.
  - Finite `X[!]` guarded-next and delayed-definition blocks stay `candidate`;
    the closed-form register templates do not certify them as `solved`.
  - `X[!]` under infinite semantics is rejected at parse time, and also after
    `--overwrite-semantics` changes a finite spec to infinite semantics.
  - Regression coverage: finite candidate CSNF goldens plus infinite/override
    expected-failure tests.
- [x] **SR-latch / set-reset register via per-output grouping** — group set
  `G(α→Xo)` + reset `G(β→X¬o)` (+ implicit hold) for one output into one register
  block and certify it. Implemented as `set-reset-register`, claiming mixed
  guarded-next groups before the one-sided `guarded-next-assignment` fallback.
  Controller shape: `X o := set ∨ (o ∧ ¬reset)`. Side condition is the existing
  syntactic set/reset guard exclusivity check; finite `X[!]` groups remain
  candidates. Verified the controller implication with `ltlfilt --implied-by`
  and added solved/declined/finite-strong regression goldens.
- [x] **Extra closed-form templates** (lower priority).
  - [x] T-flip-flop / toggle register `G(t→(X o↔¬o))`: implemented as
    `toggle-register`, with `tog` CSNF records and certificate
    `toggle_register`. Controller shape: `X o := o xor (⋁t)`. Finite `X[!]`
    toggles remain candidates. Verified the controller implication with
    `ltlfilt --implied-by` and added solved/finite-strong regression goldens.
  - [x] Fixed-delay response `G(r→X^k g)`: implemented as
    `fixed-delay-response`, matching expanded nested `X` chains and emitting
    compact `fdresp` CSNF records with certificate `fixed_delay_response`.
    Finite strong-next delay chains and non-free outputs remain candidates.
    Verified the per-record controller implication with `ltlfilt --implied-by`
    and added solved/declined/finite-strong regression goldens. Note for the
    later AIGER backend: preserve pre-expansion bounded operators (`X[k]`,
    `F/G[lo:hi]`) or annotations where useful so the encoder can choose
    delay-line/counter monitors instead of only seeing unrolled formulas.
  - [x] Multi-guard combinational reaction (collect all `G(α_i→(¬)o)` for one
    output into one Boolean controller): existing grouping confirmed and
    covered with a four-constraint regression. The certifier now reuses the
    shared guard-exclusivity helper; controller implication verified with
    `ltlfilt --implied-by`.

## Prong A — safety backend (headline capability)
- [~] **AbsSynthe safety-AIGER backend** — detect pure-safety clusters (only
  `G`/`X`/`X[!]`/bool), compile to safety-AIGER (outputs→`controllable_*` inputs,
  uncontrollable = spec inputs, one latch per `X`-ed signal, single output
  `bad = ⋁¬(G-body)`), call AbsSynthe (`--absynthe PATH` / `$ABSSYNTHE`), merge
  strategy. Reserve `ltlsynt` for liveness clusters. Gate on the binary; add a
  fake-stub coverage test like `test/fake_ltlsynt.sh`. Prior art for LTL→AIGER:
  gaperez64's `acacia_ltl2aig` / `task2aig`. AbsSynthe keys controllable inputs
  on the `controllable` name prefix (`aig.cpp:248`).
  - [x] Vendor setup: AbsSynthe added as `external/AbsSynthe` submodule on
    `native-dev-par`; Meson detects initialized/built state and provides
    `abssynthe-submodule` / `abssynthe-build` run targets.
  - [x] First backend slice: `tlsfcompose --aiger` accepts `--abssynthe`
    (`--absynthe` alias) / `$ABSSYNTHE`, routes eligible non-finite
    `G(boolean)` safety clusters through an AbsSynthe-style `-o strategy.aag`
    process, strips `controllable_` output prefixes before merge, and keeps
    liveness / unsupported temporal-safety clusters on `ltlsynt`. Regression
    uses `test/fake_abssynthe.sh`.
  - [x] Extend the safety monitor encoder beyond `G(boolean)` to non-finite
    `G`/`X`/bool via history latches; regression covers `G(BURST4 -> X(...))`.
    Finite `X[!]` is deliberately not routed to AbsSynthe.
  - [x] Add environment-assumption handling to the safety monitor. Eligible
    implication clusters now compile `A -> G` as safety games guarded by a
    false-initialized `violated` monitor: guarantees are enforced until the
    environment violates the assumptions, and later obligations are released.
  - [x] Recover named controllable functions from vanilla AbsSynthe output.
    The AbsSynthe submodule now emits `controllable-gate <lit> <name>` comments
    when redefining controllable inputs as gates; the local AIGER reader imports
    those comments as named outputs and strips the ordinary `bad` output before
    merging.
  - [x] Smoke-test the path with the real vendored AbsSynthe binary, not only
    `test/fake_abssynthe.sh`. Build `external/AbsSynthe/binary/abssynthe`, run
    the existing safety/next/assumption cases through it, and decide whether any
    real-output quirks need parser or merge hardening. First finding: AbsSynthe
    ignores latch reset literals and initializes all latches to false, so
    monitors must not rely on reset-to-true state. The assumption monitor now
    uses a false-initialized `violated` latch and gates guarantee checks by the
    full assumption window; optional real-backend Meson tests cover both a
    realizable delayed assumption and the unconstrained future-input rejection.
  - [x] Run a bounded corpus pass with the AbsSynthe backend enabled and record
    the solve-rate / residual-size delta against the fake-only development
    coverage. Added `scripts/bounded_synthesis.py` for bounded
    `tlsfcompose --aiger` runs. On a 40-spec deterministic test/cases sample
    (`seed=11`, `timeout=10`, fake `ltlsynt`), fake AbsSynthe reported 36/40
    ok; real AbsSynthe reported 31/40 ok and 5 real unrealizable clusters
    (-12.5pp ok rate), with the remaining 4 errors coming from intentionally
    invalid fixtures.
    Local benchmark rerun (`bench/specs`, real AbsSynthe, `ltlsynt=/bin/false`,
    `timeout=1800`, `mem=3000MB`): templates-only solved/fully-solved 0/6 and
    eliminated 0/1892 constraints; templates+AbsSynthe emitted 1/6 controllers
    (`small_Lights2_f1477cc5_2.tlsf`). The four robot specs and
    `small_ltl2dba22.tlsf` still fail at cluster 0 because the remaining
    cluster contains liveness / weak-until structure that is not handled without
    `ltlsynt`. Re-running with `--split` did not change the synthesis coverage:
    templates found one solved block in the trivial Lights spec, but
    templates+AbsSynthe still emitted only 1/6 controllers.
    Full SYNTCOMP rerun against `../benchmarks/tlsf` compared with
    `BENCHGRAPH.md`: after the global-recurrence template, certified template
    coverage is 502 solved blocks, 202 specs with >=1 solved block, 2 fully
    solved specs, 385/90855 constraints eliminated, and 318/14463 outputs
    owned. The AbsSynthe route adds 131/2545 syntactically eligible whole specs
    with the fake backend, covering 1483 residual clusters. Real AbsSynthe,
    restricted to those eligible specs with `ltlsynt=/bin/false` and
    `timeout=10`, emitted controllers for 123 specs, proved 7 specs
    unrealizable, and timed out on 1; the successful specs account for 1439
    residual clusters. Combined compositional coverage is therefore roughly
    318+1439=1757/4977 units (35.3%) with real controllers, up from 318/4977
    (6.4%) in the template-only composition accounting.
  - [x] Add a direct AIGER-vs-LTL verification harness for solved controllers.
    `scripts/verify_aiger_ltl.py` uses Spot's Python AIGER reader to check
    emptiness of `controller & !spec`. Meson registers a fast template-only
    verification case and, when local Spot Python plus the vendored AbsSynthe
    binary are available, a real-AbsSynthe no-`ltlsynt` assumption-monitor case.
    `BENCHGRAPH.md` now records the current full-corpus no-`ltlsynt` delta:
    template-only composition covers 318/4977 units, templates+real AbsSynthe
    cover 1757/4977 units, and real AbsSynthe plus local templates emit 125 full
    `tlsf` controllers without `ltlsynt`.
  - [x] Preserve bounded temporal operator metadata for compact AIGER encodings.
    Unrolling `X[k]` is fine for templates, but the expanded AST now retains
    `X[k]`, `G[lo:hi]`, and `F[lo:hi]` origin metadata so the safety backend can
    choose delay-line or binary-counter monitors before relying on the
    unrolled shape. `tlsfinfo --bounded-temporal` exposes this for regression
    tests and debugging.

## Coverage recovery TODOs
- [x] **Add a small deterministic-Buchi / persistence template layer.**
  Implemented as `global-recurrence-switch` for `G(phi) <-> G F o`, with
  temporal-free/output-free `phi`, a one-bit local AIGER controller, CSNF
  `dbuchi` records, and AIGER-vs-LTL verification coverage. This solves
  `small_ltl2dba22.tlsf` locally and adds the two `ltl2dba22` SYNTCOMP copies
  to the no-`ltlsynt` full-controller set.
- [~] **Factor robot-style GR(1) structure before backend selection.**
  The robot benchmarks are dominated by safety transition constraints plus
  fairness assumptions (`G F !door*`) and recurrence/persistence guarantees.
  Current clustering keeps these in a single liveness/weak-until formula, so
  AbsSynthe never sees the safety game. Extract the explicit transition system,
  safety invariants, justice assumptions, and justice guarantees into a small
  GR(1)/Buchi game backend instead of sending the whole cluster to `ltlsynt`.
  Strict-safety `S W !A` clusters are now factored into AbsSynthe safety games
  before backend selection; the four local robot specs advance past cluster 0
  and now stop at the remaining GR(1) liveness cluster when `ltlsynt` is
  disabled.
- [x] **Improve composition diagnostics for disabled fallback runs.**
  When `--ltlsynt /bin/false` is used, report whether the failed cluster was
  ineligible because of liveness, weak-until, finite strong-next, unsupported
  temporal shape, or because AbsSynthe returned unrealizable/no strategy.
  Disabled-fallback tests cover GR(1) liveness residuals, and AbsSynthe failures
  now distinguish unrealizable/no-strategy from unsupported fallback routing.

## Deferred short-term TODOs
- [x] **Fix `--aiger` cluster ins/outs partition gap** — every atom in a cluster
  LTL must be classified into `c ins=`/`c outs=`; dropped enum/bus atoms break the
  backend on ~32/40 amba specs ("…should match 'BURST4'").
  Unclassified residual APs are now treated as environment inputs in cluster
  headers and in the merged AIGER interface; regression covers the fake-ltlsynt
  merge path with `BURST4`.
- [x] **Bounded corpus harness** — script the pipeline over a sample with
  `RLIMIT_AS`+`timeout` (mirror `scripts/benchgraph_plots.py`'s
  `_limit`/`--mem-mb`/`--timeout`), reporting solve-rate deltas without OOM kills.
  Implemented as `scripts/bounded_corpus.py`: each spec runs in its own bounded
  `tlsfbenchgraph` child, stdout is a stable TSV with per-process status, stderr
  reports solve rates/residual reduction, and `--baseline` reports percentage
  point deltas against a prior benchgraph/harness TSV.

## Invariants (every change)
clang-format (LLVM) + clang-tidy clean · tests green · coverage ≥75% via
`gcovr` with the compiler's matching `gcov` · valgrind clean · no JSON
(DIMACS-style lines) · self-contained where CI runs (flex/bison/gcc/valgrind
only — no spot/ltlsynt/AbsSynthe). Heavy runs bounded (`ulimit -v` + `timeout`).
