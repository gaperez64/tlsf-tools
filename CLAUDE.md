# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build commands

```sh
meson setup build && ninja -C build          # dependency-free build (templates only)
meson setup build-san -Dsanitize=address,undefined && ninja -C build-san  # sanitizers
meson setup build-cov -Db_coverage=true && ninja -C build-cov             # coverage

# OxiDD (the safety + GR(1) BDD solvers, i.e. tlsfcompose/tlsfsolve) is an
# optional feature (-Doxidd=auto): the submodule must be built first
# (requires Rust/cargo + cbindgen), then enable it explicitly:
meson compile -C build oxidd-submodule oxidd-build   # or: scripts/build_oxidd.sh
meson setup build-oxidd -Doxidd=enabled && ninja -C build-oxidd

# Optimized / SIMD build (compile-time ISA via -Dcpu; see include/tlsf/simd.h):
meson setup build-opt -Doxidd=enabled -Dcpu=native --buildtype=release -Db_lto=true
```

Without OxiDD, only the TLSF preprocessing tools build (parse, graph, templates,
residual, WL); `tlsfcompose`/`tlsfsolve` and the BDD solvers need `-Doxidd`.
`-Dcpu` ∈ `baseline|avx2|avx512|neon|native` (default `baseline`).

## Test, lint, format

```sh
meson test -C build                          # dependency-free golden-output suite
meson test -C build -k verify_aiger_oxidd   # OxiDD safety tests (needs build-oxidd)
meson test -C build -k verify_aiger_oxidd_gr1  # OxiDD GR(1) tests (needs build-oxidd)
clang-format -i src/*.c include/tlsf/*.h    # style: LLVM, 2-space indent, 80-col
clang-tidy -p build src/*.c                 # lint
valgrind --leak-check=full build/tlsfcompose --split --aiger spec.tlsf   # leaks
```

## Architecture overview

The pipeline processes TLSF specs through four stages:

1. **Parse → expand** (`flex`/`bison` in `src/parser.l`/`src/parser.y`): raw AST → ground AST. Every tool starts here via `tlsf_parse_file` / `tlsf_parse_string`.

2. **Recognize + templates** (`tlsfcover`/`recognize`, `tlsftemplates`): builds the expanded constraint cover, recognises syntactic template candidates (response, mutex, arbiter, …), promotes to certified controllers. Equivalence-preserving normalization (`tlsfnorm`, `include/tlsf/normalize.h`) can expose more exact shapes first.

3. **Decompose → residual** (`tlsfresidual`, `tlsfcompose`): substitutes certified outputs away, clusters by disjoint output support, classifies each cluster (safety / liveness / GR(1) / template).

4. **Synthesize** (`tlsfcompose --aiger`): routes safety clusters to a BDD safety solver, GR(1) clusters to a GR(1) solver, liveness to `ltlsynt`. Merges the resulting AIGER controllers.

### Key source files

The synthesis orchestrator (`tlsfcompose`) is split across one internal header
and four TUs (see `include/tlsf/compose_internal.h` for the shared types
`Gr1Parts`/`ClusterShape` and the cross-module prototypes):

- `src/main_tlsfcompose.c` — CLI parsing + per-cluster routing in `main`.
- `src/compose_analysis.c` — pure AST/arena gates: eligibility, X-depth, W/R + GR(1) decomposition (`aig_eligible`, `aig_gr1_parts`, `bound_liveness`), cluster-shape classification.
- `src/compose_games.c` — the four `Aig` game builders (`build_aig_game`, `build_aig_strict_safety_game`, `build_aig_wr_game`, `build_aig_gr1_game`).
- `src/compose_solve.c` — `ltlsynt` subprocess fallback, the OxiDD dispatchers (`solve_safety_game` → `solve_safety_oxidd`; `solve_gr1_game` → `solve_gr1_oxidd`), and the self-verification gate (`controller_violates_spec`).
- `src/aiger.c` / `include/tlsf/aiger.h` — `Aig` struct (and-inverter graph): inputs, latches, outputs, `just[]` (system Büchi goals), `fair[]` (env fairness). All game builders emit `Aig`.
- `src/safety_oxidd.c`, `src/gr1_oxidd.c`, `src/oxidd_common.c` — in-process BDD solvers. `solve_safety_oxidd` runs the cpre fixpoint + Skolem extraction; `solve_gr1_oxidd` runs the PPS tri-nested fixpoint with goal-counter latches; `oxidd_common.{c,h}` holds the shared BDD↔AIG helpers (`Memo`, `bdd2aig`, `lit_to_bdd`, `cube_of`, `bdd_eq`).
- `src/templates.c` + `src/templates_certify.c` (`include/tlsf/templates_internal.h`) — CSNF template machinery: `templates.c` keeps the dispatcher / composition / emission; `templates_certify.c` holds the 15 per-template recognizers + certifiers; the private `Block`/`Csnf` model lives in the internal header.
- `include/tlsf/simd.h` — compile-time ISA selection (AVX-512/AVX2/NEON/scalar) for the `apset` word-array reductions, keyed off `-Dcpu`.
- `src/main_tlsfsolve.c` — standalone `tlsfsolve` binary: reads AIGER game → `solve_safety_oxidd` or `solve_gr1_oxidd` → writes strategy AIGER to stdout.

### OxiDD (sole BDD backend)

Vendored as `external/oxidd` git submodule. Build artifacts:
- `external/oxidd/target/release/liboxidd_ffi_c.a`
- `external/oxidd/build/include/oxidd/capi.h`

Meson feature `-Doxidd` (`auto`: use if the artifacts are present; `enabled`:
require them). AbsSynthe is fully retired — OxiDD is the only BDD backend, and
`ltlsynt` is the fallback for liveness clusters and failed/unverified solves.
CI builds the FFI once in the `oxidd` job and shares it as an artifact; the
`build-oxidd` job builds `-Doxidd=enabled -Dcpu=avx2`. The Spot-verified
`verify_aiger_oxidd*` tests auto-gate on Spot (absent in CI; run locally).

**Safety fixpoint:** `W = νZ. ∀u. ∃c. [¬bad ∧ Z[s:=NEXT]]`. Realizable iff `W` is true at the reset cube. Strategy: sequential Skolem (cofactor + substitute per controllable), then BDD→AIG via ite-expansion memoised on BDD handle bytes.

**GR(1) fixpoint (PPS):** `W* = νZ. ⋀_j[μY. νX. cpre((Z∩goal_j) ∪ Y ∪ (X∩not_fair))]`. Strategy: one-hot goal-counter latches (all reset=0; `eff_curr[0]` is TRUE when no curr latch is set), Skolem extraction per level, BDD→AIG.

### GR(1) game format

`build_aig_gr1_game` emits an `Aig` with: inputs (env + controllable), state latches, `bad` output, `just[]` pending-monitor latches (one per system justice goal), `fair[]` latch-sampled env fairness latches. `solve_gr1_oxidd` operates over these via the PPS fixpoint.

### Corpus benchmarking

`scripts/benchgraph.py` runs the full pipeline vs `ltlsynt` over a corpus; results go to `BENCHGRAPH.md`. **Never run two instances in parallel** — each spawns child processes that together can OOM the machine. Use `--resume` after a crash.

## Status & remaining work

Done: in-process OxiDD safety + GR(1) solvers (AbsSynthe retired); OxiDD manager
cap raised to 22 bits; W/R false-UNREAL safety fix (complex depth≥3 bodies now
fall back to ltlsynt); SensorSelector AND(G,IMPL) shape; compile-time SIMD +
OxiDD-in-CI; persistent BDD manager (one alloc per run); Gamelogic false-UNREAL
fix (bare-W/R + G X over-constraint → ltlsynt fallback); output-free guarantee
soundness fix (`--split` now realizability-checks input-only guarantees with all
assumptions instead of dropping them — e.g. `G(o&&a)` correctly UNREALIZABLE);
`spot-syntcomp` Docker image (Spot ltlsynt + preprocessor) + GHCR CD job;
**verdict-trust framework** (under/over/exact certifier classes) + two
false-UNREAL fixes (certifier freedom check + assumption-drop re-validation; 0
false-UNREAL corpus-wide); **W/R-safety marked OVER-approximation** + ltlsynt
re-validation of its REALIZABLE verdict (fixes the box/evasion/follow/square
false-REALs); **E2BIG fix** (ltlsynt/verifier formulas passed via file, not the
command line — re-enables the fallback/verify on large clusters); `tlsfinfo
--expanded-ins/--expanded-outs` (scalar signal CSV).

Benchmark (2026-06-25; 30s base + 60s re-run of the losses, ltlsynt/Spot):
**16.5% self-contained** (419/2545 at 30s), **0 false-UNREAL, 0 false-REAL**,
**net +12** preprocessor head-to-head (21 specs solved that ltlsynt times out on,
9 lost), both-solved aggregate ×1.11. The earlier **31.8%/×35** numbers were a
looser/older setup; at a tight 30s budget the decomposition overhead costs the
timeout race, so the preprocessor's edge is the specs ltlsynt *can't* do, not raw
speed. See `BENCHGRAPH.md` (note: the head-to-head mixes a 30s base with a 60s
re-run of the loss set after the E2BIG fix).

Open (reach — solve more residuals):
- **Liveness backend** (biggest lever): ~2/3 of residuals are pure liveness
  (F/U/GF/Büchi) needing a real game, not a syntactic certificate; ~27% of that
  tail are genuinely unrealizable.
- **Remaining W/R-safety shapes** (gate-protected, exactly encodable): nested
  weak-until `G(req → (A W B))` with inner W/R (sub-monitors; *MusicAppFeedback*);
  U-shaped responses `G(req → X(a U b))`. Extend the gates in
  `compose_analysis.c` + the builders in `compose_games.c`; the self-verification
  gate keeps any wrong encoding sound (falls back to `ltlsynt`).
  **Note:** W/R path currently falls back on UNREALIZABLE as well as OOM (complex
  depth≥3 pattern interaction can produce over-constrained games); exact W/R
  encoding for specs with many nested X operators is an open correctness task.
- **GR(2)/generalized-Rabin** for `amba_gr+`; GR(1)-aware BDD abstraction for big
  amba (`pb_10+`).
- **Trust UNREALIZABLE** on bounded/GR(1)/liveness paths (needs over-constraint
  analysis; currently sound to fall back).

Deferred perf levers (in order): persistent BDD manager (per-session, not
per-cluster) → parallel output-disjoint clusters → WL-fingerprint controller
cache.

Measured dead-ends — **do not redo** (all +0 on the SYNTCOMP needle): finer
per-cluster assumption scoping; bounded-liveness reduction (fairness is the
lever, not more bounded operators); `G`-over-∧ distribution behind the gate
(Spot OOMs on the big unsound specs the gate can't protect); adding recognizer
shapes without a solver (recognizer lift is gated at the GR(1) wall).

## Code conventions

- C23, LLVM clang-format (2-space, 80-col). Tabs in generated files (bison) only.
- No dynamic dispatch — function pointers only for internal callbacks; prefer direct calls.
- `Aig` ownership: every function that takes `Aig *game` owns and frees it.
- Tests: golden-output diffs via `test/check.sh`; Spot correctness via `scripts/verify_aiger_ltl.py`; realizability oracle is Spot equivalence, not byte-identical circuit.
