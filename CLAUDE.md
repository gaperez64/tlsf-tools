# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build commands

```sh
meson setup build && ninja -C build          # default build (no AbsSynthe, no OxiDD)
meson setup build-san -Dsanitize=address,undefined && ninja -C build-san  # sanitizers
meson setup build-cov -Db_coverage=true && ninja -C build-cov             # coverage

# Optional backends (submodule must be initialized first):
meson compile -C build abssynthe-submodule abssynthe-build   # AbsSynthe subprocess solver
meson compile -C build oxidd-submodule oxidd-build           # OxiDD in-process BDD solver
# After oxidd-build, reconfigure so meson picks up the artifacts:
meson setup --reconfigure build-oxidd && ninja -C build-oxidd
```

## Test, lint, format

```sh
meson test -C build                          # dependency-free golden-output suite
meson test -C build -k verify_aiger_oxidd   # OxiDD-specific tests (needs build-oxidd)
meson test -C build -k abssynthe            # AbsSynthe tests (needs abssynthe backend)
clang-format -i src/*.c include/tlsf/*.h    # style: LLVM, 2-space indent, 80-col
clang-tidy -p build src/*.c                 # lint
valgrind --leak-check=full build/tlsfcompose --split --aiger spec.tlsf   # leaks
```

## Architecture overview

The pipeline processes TLSF specs through four stages:

1. **Parse → expand** (`flex`/`bison` in `src/parser.l`/`src/parser.y`): raw AST → ground AST. Every tool starts here via `tlsf_parse_file` / `tlsf_parse_string`.

2. **GSNF + templates** (`tlsfgraph`, `tlsftemplates`): builds a Graph Structural Normal Form, recognises syntactic template candidates (response, mutex, arbiter, …), promotes to certified controllers.

3. **Decompose → residual** (`tlsfresidual`, `tlsfcompose`): substitutes certified outputs away, clusters by disjoint output support, classifies each cluster (safety / liveness / GR(1) / template).

4. **Synthesize** (`tlsfcompose --aiger`): routes safety clusters to a BDD safety solver, GR(1) clusters to a GR(1) solver, liveness to `ltlsynt`. Merges the resulting AIGER controllers.

### Key source files

- `src/main_tlsfcompose.c` — the synthesis orchestrator. Contains the four game builders (`build_abssynthe_game`, `build_abssynthe_strict_safety_game`, `build_abssynthe_wr_game`, `build_abssynthe_unbounded_gr1_game`) and three routing wrappers (`run_abssynthe`, `run_abssynthe_strict_safety`, `run_abssynthe_wr`). `run_abssynthe_gr1` routes GR(1) clusters.
- `src/aiger.c` / `include/tlsf/aiger.h` — `Aig` struct (and-inverter graph): inputs, latches, outputs, `just[]` (system Büchi goals), `fair[]` (env fairness). All game builders emit `Aig`.
- `src/safety_oxidd.c` / `include/tlsf/safety_oxidd.h` — in-process BDD safety solver (OxiDD). `solve_safety_oxidd(game, unreal)` runs the cpre fixpoint and Skolem strategy extraction.
- `src/main_tlsfsolve.c` — standalone `tlsfsolve` binary: reads AIGER game → `solve_safety_oxidd` → writes strategy AIGER to stdout.

### Safety solver dispatch

`solve_safety_game` (in `main_tlsfcompose.c`) selects the backend via `$TLSF_SOLVER`:
- `TLSF_SOLVER=oxidd` → `solve_safety_oxidd` (in-process, no subprocess)
- default → `run_abssynthe_game` (AbsSynthe subprocess)

GR(1) clusters always use AbsSynthe subprocess (`run_abssynthe_gr1`) — OxiDD GR(1) is the next planned phase.

### OxiDD (in-process BDD solver)

Vendored as `external/oxidd` git submodule (v0.11.2). Build artifacts:
- `external/oxidd/target/release/liboxidd_ffi_c.a`
- `external/oxidd/build/include/oxidd/capi.h`

Compile-time guard: `#ifdef HAVE_OXIDD`. Meson feature: `-Doxidd=auto` (auto-detects if artifacts are present).

The safety fixpoint: `W = νZ. ∀u. ∃c. [¬bad ∧ Z[s:=NEXT]]`. Realizable iff `W` is true at the reset cube. Strategy extraction: sequential Skolem (cofactor + substitute per controllable output), then BDD→AIG via ite-expansion memoised on BDD handle bytes.

### GR(1) game format

`build_abssynthe_unbounded_gr1_game` emits an `Aig` with: inputs (env + controllable), state latches, `bad` output, `just[]` pending-monitor latches (one per system justice goal), `fair[]` latch-sampled env fairness latches. The Piterman-Pnueli-Sa'ar (PPS) tri-nested fixpoint operates over these.

### Corpus benchmarking

`scripts/benchgraph.py` runs the full pipeline vs `ltlsynt` over a corpus; results go to `BENCHGRAPH.md`. **Never run two instances in parallel** — each spawns child processes that together can OOM the machine. Use `--resume` after a crash.

## Code conventions

- C23, LLVM clang-format (2-space, 80-col). Tabs in generated files (bison) only.
- No dynamic dispatch — function pointers only for internal callbacks; prefer direct calls.
- `Aig` ownership: every function that takes `Aig *game` owns and frees it.
- Tests: golden-output diffs via `test/check.sh`; Spot correctness via `scripts/verify_aiger_ltl.py`; realizability oracle is Spot equivalence, not byte-identical circuit.
