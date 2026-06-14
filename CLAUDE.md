# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build commands

```sh
meson setup build && ninja -C build          # default build (OxiDD required)
meson setup build-san -Dsanitize=address,undefined && ninja -C build-san  # sanitizers
meson setup build-cov -Db_coverage=true && ninja -C build-cov             # coverage

# OxiDD submodule must be built first (requires Rust/cargo):
meson compile -C build oxidd-submodule oxidd-build
# Then reconfigure so meson picks up the artifacts:
meson setup --reconfigure build-oxidd && ninja -C build-oxidd
```

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

2. **GSNF + templates** (`tlsfgraph`, `tlsftemplates`): builds a Graph Structural Normal Form, recognises syntactic template candidates (response, mutex, arbiter, …), promotes to certified controllers.

3. **Decompose → residual** (`tlsfresidual`, `tlsfcompose`): substitutes certified outputs away, clusters by disjoint output support, classifies each cluster (safety / liveness / GR(1) / template).

4. **Synthesize** (`tlsfcompose --aiger`): routes safety clusters to a BDD safety solver, GR(1) clusters to a GR(1) solver, liveness to `ltlsynt`. Merges the resulting AIGER controllers.

### Key source files

- `src/main_tlsfcompose.c` — the synthesis orchestrator. Contains four game builders (`build_abssynthe_game`, `build_abssynthe_strict_safety_game`, `build_abssynthe_wr_game`, `build_abssynthe_unbounded_gr1_game`) and two routing dispatchers (`solve_safety_game` → `solve_safety_oxidd`; `solve_gr1_game` → `solve_gr1_oxidd`).
- `src/aiger.c` / `include/tlsf/aiger.h` — `Aig` struct (and-inverter graph): inputs, latches, outputs, `just[]` (system Büchi goals), `fair[]` (env fairness). All game builders emit `Aig`.
- `src/safety_oxidd.c` / `include/tlsf/safety_oxidd.h` — in-process BDD safety solver. `solve_safety_oxidd(game, unreal)` runs the cpre fixpoint and Skolem strategy extraction.
- `src/gr1_oxidd.c` / `include/tlsf/gr1_oxidd.h` — in-process BDD GR(1) solver. `solve_gr1_oxidd(game, unreal)` runs the PPS tri-nested fixpoint and strategy extraction with goal-counter latches.
- `src/main_tlsfsolve.c` — standalone `tlsfsolve` binary: reads AIGER game → `solve_safety_oxidd` or `solve_gr1_oxidd` → writes strategy AIGER to stdout.

### OxiDD (sole BDD backend)

Vendored as `external/oxidd` git submodule. Build artifacts:
- `external/oxidd/target/release/liboxidd_ffi_c.a`
- `external/oxidd/build/include/oxidd/capi.h`

Meson feature: `-Doxidd=enabled` (mandatory). No AbsSynthe fallback.

**Safety fixpoint:** `W = νZ. ∀u. ∃c. [¬bad ∧ Z[s:=NEXT]]`. Realizable iff `W` is true at the reset cube. Strategy: sequential Skolem (cofactor + substitute per controllable), then BDD→AIG via ite-expansion memoised on BDD handle bytes.

**GR(1) fixpoint (PPS):** `W* = νZ. ⋀_j[μY. νX. cpre((Z∩goal_j) ∪ Y ∪ (X∩not_fair))]`. Strategy: one-hot goal-counter latches (all reset=0; `eff_curr[0]` is TRUE when no curr latch is set), Skolem extraction per level, BDD→AIG.

### GR(1) game format

`build_abssynthe_unbounded_gr1_game` emits an `Aig` with: inputs (env + controllable), state latches, `bad` output, `just[]` pending-monitor latches (one per system justice goal), `fair[]` latch-sampled env fairness latches. `solve_gr1_oxidd` operates over these via the PPS fixpoint.

### Corpus benchmarking

`scripts/benchgraph.py` runs the full pipeline vs `ltlsynt` over a corpus; results go to `BENCHGRAPH.md`. **Never run two instances in parallel** — each spawns child processes that together can OOM the machine. Use `--resume` after a crash.

## Code conventions

- C23, LLVM clang-format (2-space, 80-col). Tabs in generated files (bison) only.
- No dynamic dispatch — function pointers only for internal callbacks; prefer direct calls.
- `Aig` ownership: every function that takes `Aig *game` owns and frees it.
- Tests: golden-output diffs via `test/check.sh`; Spot correctness via `scripts/verify_aiger_ltl.py`; realizability oracle is Spot equivalence, not byte-identical circuit.
