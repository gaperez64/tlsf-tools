# tlsf-tools

Command-line tools and a shared C library for [TLSF](https://github.com/reactive-systems/syfco)
(Temporal Logic Synthesis Format) specifications. They expand parameters,
definitions (including recursive cases), sets, reductions, structural pattern
guards, buses, bounded temporal operators, `enum` types, and `SIZEOF` into ground
TLSF or equivalent LTL.

| Stable tool | Purpose |
|---|---|
| `tlsf2ltl` | Convert expanded TLSF to LTL. |
| `tlsf2tlsf` | Emit expanded/basic TLSF. |
| `tlsfinfo` | Inspect metadata, signals, and GR level. |
| `tlsfnorm` | Normalize, split, and simplify TLSF. |
| `mealy2moore` | Delay AIGER strategy outputs for Moore-target specs. |

The optional research layer adds decomposition, certified local controllers,
exact OxiDD safety/GR(1) solving, and external residual solving. Build these
executables with `-Dresearch_tools=true`; they are excluded from stable release
archives and the stable preprocessing API.

| Research tool | Purpose |
|---|---|
| `tlsftemplates` | Inspect template certificates and CSNF output. |
| `tlsfbenchgraph` | Report corpus benchmarks and structural shapes. |
| `tlsfresidual` | Emit residual clusters after sound decomposition. |
| `tlsfcompose` | Plan decomposed synthesis and merge AIGER strategies. |
| `tlsfsolve` | Solve [AbsSynthe](https://github.com/gaperez64/AbsSynthe)-style AIGER safety/GR(1) games with OxiDD. |

## Build

Requires C23 and C++20 compilers, [Meson](https://mesonbuild.com/),
[Ninja](https://ninja-build.org/), `flex`, `bison`, Cargo (Rust 1.91+), and
`cbindgen` 0.29.4. Every build includes OxiDD and native GR(1); `research_tools`
controls only optional executables. The library, tests, and CI do not require Spot.

```sh
meson setup build --buildtype=release
ninja -C build

# Research tools
git submodule update --init --recursive
meson setup build-research -Dresearch_tools=true --buildtype=release
ninja -C build-research
```

Use `-Dsanitize=address,undefined` for development sanitizers. JSON support uses
installed yyjson 0.12.0 or the pinned `subprojects/yyjson.wrap` fallback. The
fallback installs yyjson and its pkg-config file with `libtlsf`, so static
consumers can use `pkg-config --static --libs tlsf`.

`-Dcpu=baseline|x86-64-v2|avx2|avx512|neon|native` selects the compiler's target
for auto-vectorization. AP-set kernels use portable C loops with a one-word
union fast path; the compiler chooses vector width. Build metadata retains the
existing tier names (`scalar` is the historical baseline label), which describe
the compiler target rather than runtime dispatch or a guaranteed vector width.
`simd_check` covers every length 0–1000, every word offset modulo 64 bytes,
zero/one/alternating/random data, and unchanged words outside the union range.

On the shared x86-64 AVX2 host, nine serial release (`-O3`) runs of
[`bench/simd.c`](bench/simd.c) gave these median union times (ns/call):

| Compiler / target | Words | Intrinsics | Portable |
| --- | ---: | ---: | ---: |
| GCC 15.3 / baseline | 1000 | 252.97 | 252.93 |
| GCC 15.3 / x86-64-v2 | 1000 | 333.37 | 252.85 |
| GCC 15.3 / AVX2 | 1 | 3.24 | 2.43 |
| GCC 15.3 / AVX2 | 1000 | 171.56 | 131.24 |
| Clang 21.1 / baseline | 1000 | 252.91 | 253.37 |
| Clang 21.1 / AVX2 | 1000 | 217.20 | 156.46 |

The [complete measurements](bench/simd-20261104.json) include small sizes and
popcount. The change favors common one-word sets and longer unions, with some
short Clang cases costing up to about 1.2 ns more; it is not a speed guarantee
for every size. Popcount keeps the builtin reduction, letting the target
compiler choose scalar or vector instructions. The unused AND-popcount kernel
was removed. AVX-512 and AArch64/NEON are compile-only checks here; these numbers
make no performance claim for those targets or for whole applications.

[OxiDD](https://github.com/OxiDD/oxidd) is part of `libtlsf`.
[ltlsynt](https://spot.lre.epita.fr/ltlsynt.html) and
[acacia-bonsai](https://github.com/gaperez64/acacia-bonsai) are optional external
executables for `scripts/solve.sh` and benchmark flows. GR(1) tries general
monitor admission after a default unsupported decline. The
[Lean reference and bounded validation](proofs/README.md#automaton-translation-validation)
cover both policies; runtime formulas without a validated golden rely on the
proved reference and validation sample, not a proof of the C implementation.

## Usage

Tools read `FILE` or stdin, write stdout or `--output FILE`, and accept
`--version` and `--help`. Options use long (`--`) names only.

```sh
# convert
tlsf2ltl  spec.tlsf                       # spec's LTL (ltlxba, minimal parens)
tlsf2ltl  --format ltl|latex spec.tlsf    # plain LTL / LaTeX math
tlsf2ltl  --strong-simplify spec.tlsf     # NNF + push/pull simplification, etc.
tlsf2ltl  --safety | --liveness spec.tlsf # syntactic split of the formula
tlsf2ltl  --fair-environment spec.tlsf     # assume every input toggles forever
tlsf2tlsf --fair-environment spec.tlsf     # add scalar/quantified fairness
tlsf2tlsf --basic spec.tlsf               # fully expanded basic TLSF
tlsf2tlsf --provenance-out origin.json spec.tlsf  # expanded TLSF + source origins
mealy2moore strategy.aag > strategy.moore.aag  # delay Mealy outputs one step

# inspect
tlsfinfo  spec.tlsf                        # all metadata (--semantics, --title, …)
tlsfinfo  --input-signals|--output-signals spec.tlsf    # declared (bus notation)
tlsfinfo  --expanded-ins|--expanded-outs   spec.tlsf    # scalar CSV for ltlsynt --ins/--outs
tlsfinfo  --generalized-reactivity spec.tlsf   # GR(k) level, or "NOT in GR"

# research / diagnostics
tlsftemplates --certify --solve --format csnf spec.tlsf   # certified controllers
tlsfbenchgraph --input-dir specs/ --split --summary       # corpus shape census
tlsfbenchgraph --source-features spec.tlsf                # leakage-free selector row
scripts/automata_study.py --file-list panel.list --output run/ \
  --tlsfnorm build/tlsfnorm --tlsf2ltl build/tlsf2ltl \
  --tlsfinfo build/tlsfinfo --tlsfbenchgraph build/tlsfbenchgraph \
  --automata-generator ../acacia-bonsai/build/src/acacia-automata-study

# normalize / decompose / synthesize
tlsfnorm  --passes split,nnf,boolean spec.tlsf            # re-emit normalized TLSF
tlsfnorm  --pre-passes pre-safe --passes match-safe:1 spec.tlsf  # exact-recognition normalization
tlsfnorm  --passes route-safe:1 spec.tlsf                 # routing normalization
tlsfnorm  --passes sickert-stage2:1 --norm-max-growth 300 spec.tlsf  # experimental, infinite-word-only
tlsfnorm  --norm-stats --passes match-safe:1 spec.tlsf    # per-rule normalization stats
tlsfresidual --split --output-dir out/ spec.tlsf          # one residual.k.ltl per cluster
tlsfresidual --split --lowercase spec.tlsf                # lowercase formulas + interfaces
tlsfcompose --split --output-dir out/ spec.tlsf           # controllers.aag + clusters + exact OxiDD solves
tlsfcompose --split --realizability spec.tlsf             # fast REAL/UNREAL/UNKNOWN oracle
tlsfcompose --merge out/controllers.aag out/cluster.*.aag # recombine external strategies
scripts/solve.sh --solver ltlsynt --output ctrl.aag spec.tlsf  # ltlsynt backend
scripts/solve.sh --backend acacia --solver acacia-bonsai \
        --output ctrl.aag spec.tlsf                            # acacia backend
tlsfsolve game.aag > strategy.aag                         # solve an AIGER safety/GR(1) game
```

`tlsfbenchgraph --source-features` emits a versioned TSV (`--schema-version`).
Only declared interface sizes and source-derived `guard_*` operator/depth
measurements are supported selector inputs. Splitting and normalization options
are rejected; automata, recognizer results, and solver outcomes are excluded.
See [the automata study](AUTOMATA-STUDY.md) for bundles and selector evaluation.

For `tlsfsolve` game formats, exit codes, memory settings, diagnostic builds,
and independent verification, see [the solver guide](docs/tlsfsolve-diagnostics.md).
Native monitor symbols and the `game.aag.symbols` file required for controller
export are documented in [frontend provenance](docs/frontend-provenance.md#monitor-game-symbol-namespace).

## Embeddable API

The installed library exposes decomposition/preprocessing without AIGER structs
or internal AST layouts:

- C header: `#include <tlsf/decompose.h>`
- C++ wrapper: `#include <tlsf/decompose.hpp>`
- opaque AST: `#include <tlsf/ast_api.h>`
- typed C++ visitor: `#include <tlsf/ast_api.hpp>`
- Meson: `dependency('tlsf')`
- pkg-config: `pkg-config --cflags --libs tlsf`

`tlsf_decompose_string()` / `tlsf_decompose_file()` return duplicated strings:
preprocessed LTL, global inputs/outputs, residual clusters
`{ltl, inputs, outputs}`, semantics/target, GR level, a fast pre-check verdict,
and trust tags. Free the C result with `tlsf_decompose_result_free()`. The C++
wrapper returns `std::string` / `std::vector` values and frees the C handle via
RAII.

`TlsfAst` retains the expanded specification, residual plan, cluster roots,
and the same `TlsfDecomposeResult` metadata under one lifetime. Consumers can
walk the opaque 16-kind post-expansion tree manually or use
`tlsf_ast_accept()`'s children-first callback table. The header-only C++ API
provides `tlsf::ast::Ast`, non-owning `Tree` values, and an ANTLR-style
`Visitor<T>` whose methods build any consumer-defined result type.

```cpp
#include <tlsf/decompose.hpp>
#include <tlsf/ast_api.hpp>

tlsf::Options opt;
opt.split = true;
tlsf::Result r = tlsf::decompose(spec_text, opt);
for (const tlsf::Cluster &c : r.clusters) {
  // c.ltl, c.inputs, c.outputs
}

tlsf::ast::Ast ast(spec_text, opt);
MyFormulaBuilder builder;  // derives from tlsf::ast::Visitor<MyFormula>
MyFormula formula = builder.visit(ast.root());
for (tlsf::ast::Tree cluster : ast.clusters()) {
  MyFormula residual = builder.visit(cluster);
}
```

No `Aig`, OxiDD, internal `Node`, cover, CSNF, or arena type crosses this API.
The visitor-based [`ast_api` Spot example](examples/tlsf2spot.cpp) builds each
tree directly as a `spot::formula` and checks it against the string API.
It requires Spot and is built by hand, outside Meson and CI; see the build
command in the file's header.

## Synthesis and solver pipelines

`tlsfcompose` certifies local controllers, solves eligible residuals in process,
and writes external clusters. For file-based controller export:

```sh
mkdir out && tlsfcompose --split --output-dir out/ spec.tlsf
sh out/compose.sh
# Infinite-word Mealy targets: use the exact interface expressions in compose.sh
ltlsynt --ins=… --outs=… -F out/cluster.0.spot
# Or automate solving and merging:
scripts/solve.sh --solver ltlsynt --output ctrl.aag spec.tlsf
```

`controllers.aag` contains the certified part; trusted exact/UNDER routes can
write `cluster.k.aag`, and trusted OVER routes can stop on UNREAL. Remaining
`cluster.k.ltl` files carry `c ins=`/`c outs=` interface comments. Only those
exact metadata lines are comments: `c -> p` is a valid formula.
`tlsfcompose --merge` combines local and external AIGER strategies.

Spot files quote atoms such as `Grant`; anchored interface regexes preserve
case and match whole names. Infinite Moore checks use `cluster.k.mealy` with
delayed environment inputs. The driver defaults to `ltlsynt` for infinite words
and `ltlfsynt` for finite words. Select an executable with `--solver /path/to/solver`
or `TLSFCOMPOSE_SOLVER`; the CLI wins, and an unset/empty variable uses the default.
The value is one executable name or path (spaces allowed), recorded in
`compose.sh`. It must accept `--ins`, `--outs`, `-F`, and `--realizability`, plus
`--semantics=Mealy|Moore` for finite words. Use a wrapper to adapt other interfaces
or add arguments.

`scripts/solve.sh` supports only infinite-word Mealy controller export. Its
`ltlsynt` backend passes `--lowercase` so formulas, interfaces, and AIGER symbols
agree; the `acacia` backend uses the same convention and calls acacia-bonsai with
`-F/-i/-o/-s`.

To use another Spot/Strix-style LTL synthesizer, normalize and export the scalar interface:

```sh
tlsfnorm --passes split,nnf,boolean spec.tlsf > spec.norm.tlsf
lc() { tr 'A-Z' 'a-z'; }  # ltlxba lowercases atoms
ins=$(tlsfinfo --expanded-ins spec.norm.tlsf | lc)
outs=$(tlsfinfo --expanded-outs spec.norm.tlsf | lc)
tlsf2ltl spec.norm.tlsf > spec.norm.ltl
ltlsynt --ins="$ins" --outs="$outs" -F spec.norm.ltl
```

Use `-F` for large formulas that exceed `-f` argument limits. The historical
SyFCo/classic-ltl2ba `ltlxba` dialect lowercases atoms; faithful `ltl` preserves
case, which Spot accepts. `tlsfcompose` and `tlsfresidual` preserve case unless
`--lowercase` is set; all lowercase exports reject collisions. TLSF permits
`'` and `@` in identifiers, but ltl2ba/ltl3ba silently truncate at these characters.
Every `ltlxba` export therefore rejects them; use `--format ltl`.

The research reports provide corpus shapes, normalization comparisons, and
wrapper performance:

```sh
tlsfbenchgraph --input-dir benchmarks/tlsf --split --summary > shapes.tsv
tlsftemplates --certify --solve --format csnf spec.tlsf
scripts/benchgraph.py --corpus benchmarks/tlsf \
  --tlsfcompose build-research/tlsfcompose \
  --solver ../acacia-bonsai/build_best_decomp_mona/src/acacia-bonsai
scripts/collect_route_stats.py --compose build-research/tlsfcompose \
  --timeout 5 --out route_stats.tsv benchmarks/tlsf
```

The first command reports per-spec metrics and aggregate template distributions.
`collect_route_stats.py` runs no solver, writes rows incrementally, and skips
slow specs. [BENCHGRAPH.md](BENCHGRAPH.md) holds wrapper results; `--from-data`
re-renders them.

## Synthesis guarantees

Recognition uses the expanded constraint cover, retaining each formula's role,
side, invariant wrapping, safety/liveness class, and signal support.
`--split` exposes top-level conjunctions by distributing `G`/`X` along the spine.
`tlsfnorm` and `--match-normalize` can expose further exact shapes with
equivalence-preserving rewrites. Synthesis uses no graph similarity or
approximate matching.

Template candidates include response `G(r→F g)`, mutex, recurrence `G F x`,
persistence `F G x`, reaction, definition, guarded-next, and arbiter.
`tlsftemplates` promotes them through candidate → checked → certified → solved
in Certified Strategy Normal Form (CSNF). A solved block needs conservative
side conditions, usually that its target output occurs in no other constraint.
Certified controllers include decoders (`o:=θ`), set/reset/toggle/delay registers,
reaction logic, and response/round-robin/arbiter schedulers. Stateful safety and
GR(1) reactivity remain candidates requiring a solver. CSNF is DIMACS-style line
records (`fgets`/`strtok`), not JSON.

Decoder and delayed-definition values must be temporal-free. Elimination needs
a system-side definition and no environment-side use of its output. Uses must
be in the defining section, covered by PRESET, or be GUARANTEES using ASSERT;
non-strict semantics also permit ASSERT to use GUARANTEES definitions.

`tlsfresidual` substitutes solved combinational outputs and clusters remaining
constraints by shared outputs. With disjoint outputs, infinite-word semantics
allow `E → ⋀ᵢ Gᵢ ≡ ⋀ᵢ (E → Gᵢ)`; output-dependent assumptions collapse the
clusters. Finite games keep one cluster because controllers share the word's
end. Infinite Mealy games, including strict games, prune global environment
entries outside a cluster's transitive signal cone only after a bounded native
lasso search confirms their joint `INITIALLY && G REQUIRE && ASSUMPTIONS` is
satisfiable. Inconsistent or uncertain sets stay; finite and Moore games keep
all global assumptions. The emitted cluster formula is the exact trusted game
(`TRUST_EXACT`); the spec is realizable iff every cluster is. See
[the proof rules and scope](proofs/README.md).

`tlsfcompose --realizability` uses a `TRUST_OVER` pre-check to refute a weakening
(UNREAL only) and a `TRUST_UNDER` pre-check to prove a strengthening (REAL only).
If neither succeeds, it returns `UNKNOWN` with exit 2.

## What `tlsf2ltl` emits

The single LTL formula defined by the TLSF semantics:

```
INITIALLY → ( PRESET ∧ ( (G REQUIRE ∧ ASSUME) → (G ASSERT ∧ GUARANTEE) ) )
```

`REQUIRE`/`ASSERT` are wrapped in `G`; `PRESET` sits *outside* the
assumption→guarantee implication; empty sections drop out. The
shape then follows the (possibly overwritten) `SEMANTICS`/`TARGET`:

- Strict (`Strict,*`): the TLSF v1.1 section 3.2 form
  `INITIALLY → (PRESET ∧ (ASSERT W ¬REQUIRE) ∧
  (G REQUIRE ∧ ASSUME → GUARANTEE))`; `--overwrite-semantics Mealy`
  relaxes it to the standard implication.
- Finite-word (`Finite,*`): emits `ltlxba-fin`: strong-next prints `X[!]`,
  and `W` plus any internally derived strong release are rewritten with
  LTLf-valid identities so spot's `ltlfsynt` accepts them.
- **Mealy/Moore**: from `SEMANTICS`; for infinite words, a `TARGET` mismatch
  is converted (Moore→Mealy delays all environment inputs `i↦X i`, including
  undeclared atoms; Mealy→Moore delays outputs `o↦X o`). Under finite-word
  semantics, target adaptation is unsupported: `SEMANTICS` and `TARGET` must
  agree. The adapting CLIs and decomposition API refuse finite mismatches;
  `tlsf_convert` refuses all finite semantics.

Generated `compose.sh` drivers default to `ltlfsynt --semantics=Mealy|Moore`
for finite residuals. Infinite Moore targets bypass OxiDD and use the standard
input-delay encoding for external realizability checks. `scripts/solve.sh`, which exports
and merges controllers, supports only infinite-word Mealy targets and refuses
finite games and Moore targets.

Output is minimally parenthesised by the spot/ltl2ba precedence
(`! X F G` > `U R W` > `&&` > `||` > `-> <->`). `--parenthesize` fully
parenthesises; `--format` picks the spelling (`ltlxba`/`ltl`/`latex`).
Equivalence-preserving rewrites are exposed as flags
(`--weak-simplify`=`-s0`, `--strong-simplify`=`-s1`, `--nnf`,
`--no-{weak-until,release,strong-release,finally,globally}`,
`--{push,pull}-{globally,finally,next}-{in,out}`);
The rewrites preserve equivalence (`ltlfilt --equivalent-to`).

`--fair-environment` adds `G F i` and `G F !i` assumptions for every Boolean
environment input, requiring each input to visit both values infinitely often.
For input buses, normal `tlsf2tlsf` output keeps two inclusive quantified
assumptions over the declared bounds; `tlsf2tlsf --basic` and `tlsf2ltl`
expand them into one pair per bit. Existing assumptions are preserved, specs
without inputs are unchanged, and the option is rejected under effective
finite-word semantics (including semantics selected by an override). Generated
assumptions participate in the usual Mealy/Moore conversion, rewrites, and
safety/liveness output modes.

> The `--safety`/`--liveness` split is **syntactic**: after NNF, *safety* iff the
> tree has no `F`, `U`, or internally derived strong-release node. A safety
> property written with liveness operators is classified as liveness.

## Development

| Path | Contents |
|---|---|
| `include/tlsf/` | Installed public headers. |
| `src/lib/` | Library, private headers, OxiDD solvers, GR(1) checker. |
| `src/tools/<tool>/` | Executables; `common/` holds shared helpers. |
| `test/unit/`, `test/api/` | Internal tests and installed-header API tests. |
| `test/cli/`, `test/oracle/` | Golden CLI checks and Python oracles/differentials. |
| `test/fixtures/` | Fake solvers, stubs, and `cases/` corpus. |

Each area has a `meson.build`; top-level executable declarations put binaries
at `build/<tool>`.

```sh
meson test -C build
meson setup build-cov -Dresearch_tools=true -Db_coverage=true && meson test -C build-cov
git ls-files '*.[ch]' '*.cc' '*.cpp' '*.hh' '*.hpp' | xargs clang-format -i
clang-tidy -p build src/lib/*.c src/tools/*/*.c
bench/bench.sh [--baseline|--check]
```

CI (`.github/workflows/ci.yml`) checks formatting, GCC/Clang builds, tests,
Valgrind leaks, 75% line coverage, and `bench.sh --check` wall/RSS regressions.
Licensed under [MIT](LICENSE).
