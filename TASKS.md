# TASKS — raise the self-contained solve rate

Working branch: `tlsfgraph` (do **not** merge). Full rationale + measurements in
the approved plan (`.claude/plans/sorted-meandering-thompson.md`).

Strategy (two prongs): route the **safety** residual to **AbsSynthe** (the LTL
residual is ~99% safety; `ltlsynt` is overkill), and add cheap **closed-form
templates** to pre-discharge outputs and shrink the game.

Status legend: `[ ]` pending · `[~]` in progress · `[x]` done · `[!]` blocked/revised

> **Updated 2026-06-07**: strong-next `X[!]`, SR-latch / set-reset grouping,
> toggle-register, AbsSynthe vendor setup, and sponsor metadata are cleared.
> Next local template slice: fixed-delay response `G(r→X^k g)`, or jump to the
> AbsSynthe safety backend.

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
- [~] **Extra closed-form templates** (lower priority).
  - [x] T-flip-flop / toggle register `G(t→(X o↔¬o))`: implemented as
    `toggle-register`, with `tog` CSNF records and certificate
    `toggle_register`. Controller shape: `X o := o xor (⋁t)`. Finite `X[!]`
    toggles remain candidates. Verified the controller implication with
    `ltlfilt --implied-by` and added solved/finite-strong regression goldens.
  - [ ] Fixed-delay response `G(r→X^k g)`.
  - [ ] Multi-guard combinational reaction (collect all `G(α_i→(¬)o)` for one
    output into one Boolean controller).

## Prong A — safety backend (headline capability)
- [ ] **AbsSynthe safety-AIGER backend** — detect pure-safety clusters (only
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

## Deferred short-term TODOs
- [ ] **Fix `--aiger` cluster ins/outs partition gap** — every atom in a cluster
  LTL must be classified into `c ins=`/`c outs=`; dropped enum/bus atoms break the
  backend on ~32/40 amba specs ("…should match 'BURST4'").
  `residual.c` (`collect_aps`/`print_signals`/`cluster_keys`). Needed for both backends.
- [ ] **Bounded corpus harness** — script the pipeline over a sample with
  `RLIMIT_AS`+`timeout` (mirror `scripts/benchgraph_plots.py`'s
  `_limit`/`--mem-mb`/`--timeout`), reporting solve-rate deltas without OOM kills.

## Invariants (every change)
clang-format (LLVM) + clang-tidy clean · tests green · coverage ≥75% · valgrind
clean · no JSON (DIMACS-style lines) · self-contained where CI runs (flex/bison/
gcc/valgrind only — no spot/ltlsynt/AbsSynthe). Heavy runs bounded (`ulimit -v` +
`timeout`).
