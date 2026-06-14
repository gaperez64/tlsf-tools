# Architecture — in-process safety solver on OxiDD

**Status:** complete. All phases implemented. AbsSynthe retired; OxiDD is the sole
backend for safety (direct, W/R, strict-safety) and GR(1) (PPS tri-nested fixpoint).
Benchmark rerun pending (corpus not present locally).
**Goal:** replace the AbsSynthe *subprocess* with a local, in-process BDD safety
and GR(1) solver built on [OxiDD](https://oxidd.net/) (a modern Rust decision-diagram
library with a C FFI), to make tlsf-tools a genuinely *fast* synthesis
preprocessor without giving up the safety-game or GR(1) capability.

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
solve_safety_oxidd(game, &unreal)    ──► in-process: Aig game → BDDs →
solve_gr1_oxidd(game, &unreal)            cpre/PPS fixpoint → strategy Aig
```

The game **encoders stay unchanged** — the history latches, the `valid` window,
the W/R monitors, the GR(1) pending/fairness latches are all still useful. Only
the *solve* step changed (AbsSynthe subprocess → OxiDD in-process).

The returned `Aig` strategy flows into the **unchanged** downstream: the
output-coverage check (`abssynthe_strategy_has_outputs`), the self-verification
gate (`controller_violates_spec`), and `aig_merge`.

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

In `main_tlsfcompose.c`, `solve_safety_game` calls `solve_safety_oxidd` directly;
`solve_gr1_game` calls `solve_gr1_oxidd`. No subprocess, no env-var routing.

## 6 · Build & dependency

- OxiDD is **mandatory** (`-Doxidd=enabled`, no auto-detect). Built as
  `external/oxidd` git submodule via `meson compile -C build oxidd-build`; artifacts
  detected at `external/oxidd/target/release/liboxidd_ffi_c.a`.
- No `#ifdef HAVE_OXIDD` guards remain; the solver code is always compiled.
- Valgrind: the in-process BDD library must be leak-clean for the CI memory job
  (or excluded from that job if it has benign one-time allocations).

## 7 · Phasing

1. [x] **Confirm the OxiDD C FFI** exposes ∃/∀, substitution, and assignment extraction.
2. [x] **`solve_safety_oxidd` for the direct safety path** — `src/safety_oxidd.c`.
3. [x] **Strict-safety + W/R** games (same encoders, same solver).
4. [ ] **Benchmark**: rerun `scripts/benchgraph.py`; target aggregate ≥×1.
5. [x] **GR(1) on OxiDD** — `src/gr1_oxidd.c` (PPS tri-nested fixpoint).
6. [x] **AbsSynthe retired** — submodule removed; OxiDD mandatory.
7. [ ] **Dependent levers**: persistent manager → parallel clusters → WL-fingerprint
   controller cache.

## 8 · Testing & validation

- Golden/fake tests: `aiger_oxidd_*` (same specs, OxiDD solver); Spot correctness
  tests: `verify_aiger_oxidd_*` (safety, 16 tests) + `verify_aiger_oxidd_gr1_*`
  (GR(1), 9 tests). AbsSynthe test variants removed.
- The **self-verification gate** already model-checks each controller against the
  original cluster LTL and falls back to `ltlsynt` on violation, so an extraction
  bug degrades to a sound fallback rather than a wrong controller.
- Coverage ≥75%, clang-format/tidy, valgrind clean — the standing invariants.

## 9 · Risks & mitigations

| Risk | Mitigation |
|---|---|
| C FFI lacks ∀/∃ or substitution | thin Rust shim crate exposing the needed ops; verify in phase 1 before any C work |
| Strategy extraction bug → wrong controller | the self-verification gate catches it (sound `ltlsynt` fallback); Spot correctness tests guard end-to-end |
| BDD blow-up without CUDD-grade reordering | clusters are small post-decomposition; static interleaved order; OxiDD reordering can be enabled if needed |
| Build/dependency friction (Rust toolchain) | `scripts/build_oxidd.sh` automates; meson compile target `oxidd-build`; pinned vendored FFI |

## 10 · Open questions

- Does the OxiDD C API quantify over a **cube BDD** or a **variable array**? (Shapes the `cpre` code.)
- Is there a **single global** manager or **per-game** managers? (Determines the persistent-manager / parallel-cluster design.)
- Reordering: **dynamic**, **manual**, or **none**?
- Strategy extraction: use OxiDD's own assignment/cofactor primitives, or
  implement self-substitution Skolemisation over the C API?
