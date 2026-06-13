# Architecture — in-process safety solver on OxiDD

**Status:** phases 1–3 implemented (safety + W/R + strict-safety).
Phases 4 (benchmark) in progress; GR(1) on OxiDD (phase 5) deferred.
**Goal:** replace the AbsSynthe *subprocess* with a local, in-process BDD safety
solver built on [OxiDD](https://oxidd.net/) (a modern Rust decision-diagram
library with a C FFI), to make tlsf-tools a genuinely *fast* synthesis
preprocessor without giving up the safety-game capability.

## 1 · Motivation

`scripts/benchgraph.py` (see `BENCHGRAPH.md`) showed the pipeline is at rough
*median* parity with bare `ltlsynt` but **slower in aggregate (≈×0.47)** on the
specs where AbsSynthe contributes. The cost is **not algorithmic** — it is the
fixed per-cluster overhead of `posix_spawn`-ing AbsSynthe and re-initialising
CUDD for a game that the in-process work built in microseconds. An in-process BDD
library removes exactly that overhead and unlocks three open levers at once:

- **Speed:** no spawn, no per-cluster manager re-init.
- **Parallelism:** a shared manager makes solving the output-disjoint clusters
  concurrently natural (OxiDD is designed for concurrency).
- **Reuse:** a persistent manager + the existing `tlsfwl` Weisfeiler-Lehman
  fingerprints enable caching a solved cluster's controller and reusing it for
  isomorphic clusters across a parametric family.

It also deletes incidental complexity: the `external/AbsSynthe` submodule, the
AIGER round-trip, and the subprocess timeout / zombie-reaping machinery
(`$ABSSYNTHE_TIMEOUT`, `PR_SET_PDEATHSIG`, …).

Non-goal: a liveness/parity solver. That is `ltlsynt`'s job; the preprocessor
forwards the liveness residual. OxiDD here replaces only the **safety** (and
later GR(1)) game solve.

## 2 · What changes, what stays

The decision to keep is the **clean boundary already present** in
`src/main_tlsfcompose.c`:

```
build_abssynthe_game(cov, seen, root)            ─┐
build_abssynthe_strict_safety_game(...)           │  build an `Aig` GAME
build_abssynthe_wr_game(...)                       │  (inputs, controllable_*
build_abssynthe_unbounded_gr1_game(...)          ─┘   inputs, latches, `bad`,
                                                       justice/fairness)
        │
        ▼
run_abssynthe_game(prog, cov, seen, game, unreal) ──► write AIGER → spawn
                                                       AbsSynthe → read strategy
                                                       AIGER → return `Aig`
```

The game **encoders stay unchanged** — the history latches, the `valid` window,
the W/R monitors, the GR(1) pending/fairness latches are all still useful. We
replace only the *solve* step:

```
run_abssynthe_game(...)            →   solve_safety_oxidd(game, &unreal)
  (subprocess, AIGER round-trip)        (in-process: Aig game → BDDs →
                                          cpre fixpoint → strategy Aig)
```

The returned `Aig` strategy flows into the **unchanged** downstream: the
output-coverage check (`abssynthe_strategy_has_outputs`), the self-verification
gate (`controller_violates_spec`), and `aig_merge`. Keeping AbsSynthe wired as a
fallback during the transition is cheap (the routing already picks a backend).

## 3 · OxiDD interface requirements

A first prototype needs these BDD operations from the C FFI (`oxidd-ffi-c`,
header `oxidd.h`). **Verify these exist before committing** — if any are
Rust-only we write a thin shim crate.

| Need | Used for |
|---|---|
| manager create/destroy, fresh BDD variable | one var per primary input + one per latch |
| `ite` / `and` / `or` / `not` / `xor` | compile the AIG cone into BDDs |
| **`exists` (∃) and `forall` (∀)** over a variable set/cube | the controllable predecessor `cpre` |
| **`substitute` / `compose`** (replace vars by functions) | image under the transition; strategy extraction |
| equality / `is_false` / `is_true` | fixpoint convergence, realizability check |
| `pick_cube` / satisfying assignment, or cofactor | Skolem strategy extraction |
| ref-count / GC hooks | manage intermediate BDDs across the fixpoint |
| (optional) dynamic reordering | larger games; our decomposed clusters are small |

OxiDD is concurrency-oriented; confirm whether the C API is single- or
multi-manager and whether quantification takes a cube BDD or a variable list.

## 4 · Component design

New module `src/safety_oxidd.c` (+ `include/tlsf/safety_oxidd.h`), compiled only
when the OxiDD feature is enabled (§6). It needs **read access to the `Aig`
game's internals** (latches and their next-functions, the and-gates, the inputs,
the `bad` output literal). The `Aig` struct is private to `src/aiger.c`, so add a
minimal read-accessor API there (see §4.5).

### 4.1 Variable allocation

For game `g`:
- one BDD variable `x_i` per primary input (uncontrollable **and**
  `controllable_`-prefixed — distinguished by the name prefix, as today);
- one BDD variable `s_j` per latch (current state).

Keep a `lit → BDD` map sized to `g`'s literal space; constants `0/1` map to
`⊥/⊤`, negation toggles the BDD complement.

### 4.2 AIG → BDD

Compile every needed literal by a memoised post-order over the and-gates:
`bdd(and) = bdd(r0) ∧ bdd(r1)`, `bdd(lit^1) = ¬bdd(lit)`. Produce:
- `BAD` — BDD of the `bad` output over (inputs, state);
- for each latch `j`, `NEXT_j` — BDD of its next-function over (inputs, state).

### 4.3 The safety fixpoint

Following AbsSynthe's convention (`cpre = ¬upre(¬·)`, `upre = ∃u ∀c`), with the
environment moving first (Mealy):

```
safe(S)          = ¬BAD(S, u, c)              (a state/move is immediately safe)
img_in(Z)(S,u,c) = Z[ s_j := NEXT_j(S,u,c) ]  (substitute next-state into Z)
cpre(Z)(S)       = ∀u. ∃c. ( ¬∃u∃c BAD … )    -- concretely:
                 = ∀u ∃c [ ¬BAD(S,u,c) ∧ img_in(Z)(S,u,c) ]
W                = νZ. cpre(Z)                 (greatest fixpoint from Z₀ = ⊤)
```

Iterate `Z ← cpre(Z)` until fixpoint (BDD equality). `∃c` quantifies the
controllable input vars, `∀u` the uncontrollable ones; `img_in` is a `substitute`
of the latch vars by their `NEXT_j` BDDs.

**Realizable iff** the initial state (latch reset values — `0` for the history /
`valid` / monitor latches as built by the encoders) satisfies `W`. Evaluate `W`
at the init cube; set `*unreal` accordingly (return no strategy → caller falls
back to `ltlsynt`, exactly as the UNREALIZABLE path does today).

### 4.4 Strategy extraction → `Aig`

The controller is a Mealy machine whose **memory is the game's latches** and whose
**outputs are Skolem functions** of (state, uncontrollable inputs). For the
controllable inputs `c_1..c_m`, extract one BDD function `f_k(S, u)` at a time
(standard sequential/self-substitution Skolemisation within `W`): pick `c_k` so
that the remaining choice can still keep the play in `W`, then substitute `f_k`
for `c_k` before extracting `f_{k+1}`.

Emit the strategy as an `Aig` reusing the existing builders:
- `aig_input` for each uncontrollable input;
- `aig_latch` for each game latch (memory);
- **BDD → AIG**: each BDD node `(v, T, E)` becomes `ite(v,T,E) = (v∧T)∨(¬v∧E)`,
  memoised per node, terminals → `AIG_TRUE/FALSE` — gives an AIG literal for any
  BDD function;
- drive each controllable output `aig_set_output(name, bdd2aig(f_k))` (named to
  match the spec, *not* `controllable_`-prefixed — we own the naming, so the
  `aig_strip_output_prefix` step disappears);
- set each latch's next-function to `bdd2aig(NEXT_j)` with the `c_k` inputs
  already substituted by `f_k`.

This is the same shape AbsSynthe's strategy AIGER had, so `aig_merge` consumes it
unchanged. **Strategy extraction is the main implementation effort and the main
correctness risk** — but the self-verification gate (`controller_violates_spec`)
and the golden / real-verify tests already guard it end-to-end.

### 4.5 New `Aig` read-accessors (in `src/aiger.c`)

```c
uint32_t aig_num_latches(const Aig*);
void     aig_latch_at(const Aig*, uint32_t i, uint32_t *cur_lit, uint32_t *next_lit, uint32_t *reset);
uint32_t aig_num_inputs(const Aig*);
const char *aig_input_name(const Aig*, uint32_t i, uint32_t *lit);
uint32_t aig_num_ands(const Aig*);
void     aig_and_at(const Aig*, uint32_t i, uint32_t *lhs, uint32_t *r0, uint32_t *r1);
uint32_t aig_output_lit(const Aig*, const char *name);   // e.g. "bad"
```

(GR(1) later also needs justice/fairness readers; the writers already exist.)

## 5 · Solve entry point

```c
// include/tlsf/safety_oxidd.h
Aig *solve_safety_oxidd(Aig *game, int *unreal);   // owns/frees `game`, like run_abssynthe_game
```

In `main_tlsfcompose.c`, the `run_abssynthe`/`_strict_safety`/`_wr` wrappers gain
an OxiDD branch (env/flag selected), e.g. `$TLSF_SOLVER=oxidd|abssynthe`, default
`abssynthe` until the OxiDD path passes the full suite, then flip the default.
GR(1) (`run_abssynthe_gr1`) stays on AbsSynthe in phase 1.

## 6 · Build & dependency

- OxiDD stays **optional**, like AbsSynthe: a meson feature
  (`-Doxidd=enabled/disabled/auto`) and an `#ifdef HAVE_OXIDD` guard, so the
  default build and CI (flex/bison/gcc/valgrind only) remain dependency-free.
- Pull OxiDD via its C FFI: either a vendored build (`cargo build -p oxidd-ffi-c`
  producing `liboxidd.{a,so}` + `oxidd.h`) wired through meson like the AbsSynthe
  submodule targets, or a system `dependency('oxidd')`. Prefer a pinned vendored
  build for reproducibility.
- Valgrind: the in-process BDD library must be leak-clean for the CI memory job
  (or excluded from that job if it has benign one-time allocations).

## 7 · Phasing

1. **Confirm the OxiDD C FFI** exposes ∃/∀, substitution, and assignment
   extraction (§3). Spike: solve one hand-built safety game.
2. **`solve_safety_oxidd` for the direct safety path** (`build_abssynthe_game`),
   behind `$TLSF_SOLVER=oxidd`. Pass `aiger_abssynthe_safety` and the real-verify
   safety fixtures.
3. **Strict-safety + W/R** games (same encoders, same solver).
4. **Benchmark**: rerun `scripts/benchgraph.py` with `$TLSF_SOLVER=oxidd`;
   target flipping the aggregate from ≈×0.47 toward ≥×1 (parity-or-faster). This
   is the success metric.
5. **GR(1) on OxiDD** (PPS fixpoint over the justice/fairness BDDs) — only after
   safety is proven; keep AbsSynthe as the GR(1) fallback meanwhile.
6. **Then** layer the dependent levers: persistent manager → parallel clusters →
   WL-fingerprint controller cache.
7. Once OxiDD covers everything AbsSynthe did and wins on the benchmark, retire
   the AbsSynthe submodule (keep a tag/branch for provenance).

## 8 · Testing & validation

- Reuse the existing fakes/goldens: the `aiger_abssynthe_*` golden tests and the
  `verify_aiger_abssynthe_real_*` Spot-verified tests become
  `…_oxidd_*` variants (same specs, OxiDD solver) — a true A/B oracle.
- The **self-verification gate** already model-checks each controller against the
  original cluster LTL and falls back to `ltlsynt` on violation, so an extraction
  bug degrades to a sound fallback rather than a wrong controller.
- Coverage ≥75%, clang-format/tidy, valgrind clean — the standing invariants.

## 9 · Risks & mitigations

| Risk | Mitigation |
|---|---|
| C FFI lacks ∀/∃ or substitution | thin Rust shim crate exposing the needed ops; verify in phase 1 before any C work |
| Strategy extraction bug → wrong controller | the self-verification gate catches it (sound `ltlsynt` fallback); A/B against AbsSynthe goldens |
| BDD blow-up without CUDD-grade reordering | clusters are small post-decomposition; start with a static interleaved order; enable OxiDD reordering if available |
| Build/dependency friction (Rust toolchain) | optional feature, default off; CI stays dependency-free; pinned vendored FFI |
| Losing GR(1) by dropping AbsSynthe early | phase it: safety first, GR(1) stays on AbsSynthe until its OxiDD port lands |

## 10 · Open questions

- Does the OxiDD C API quantify over a **cube BDD** or a **variable array**? (Shapes the `cpre` code.)
- Is there a **single global** manager or **per-game** managers? (Determines the persistent-manager / parallel-cluster design.)
- Reordering: **dynamic**, **manual**, or **none**?
- Strategy extraction: use OxiDD's own assignment/cofactor primitives, or
  implement self-substitution Skolemisation over the C API?
