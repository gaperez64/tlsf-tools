# tlsf-tools

Command-line tools and a C library (installed as `libtlsf.a`) for [TLSF](https://github.com/reactive-systems/syfco)
(Temporal Logic Synthesis Format) specifications. They expand parameters,
definitions (including recursive cases), sets, reductions, structural pattern
guards, buses, bounded temporal operators, `enum` types, and `SIZEOF` into ground
TLSF or equivalent LTL.

TLSF v1.1 conformance: expansion uses lexical scope for definitions, function
arguments and big operators (§§4.1–4.2, 4.6–4.7). Free identifiers, conflicting
binding categories, non-bus indexing and enum labels outside bus comparisons
are rejected (§§4.3–4.6), including in unused definitions and unselected guards.
We deliberately read §4.6's “fresh” function arguments lexically, compatibly
with the SYNTCOMP corpus: an argument may shadow any global name within its
function body, taking its category from the actual argument. Big-operator and
pattern binders still reject clashes with declared names. Enum comparisons
require equal bus and valuation widths (§4.4), checked against the actual bus
after domain filtering and argument resolution. Exact global alias chains are
also checked in unused definitions and unselected guards. Function types are
instantiated per call, including recursion (§4.6), with the boolean/signal
embedding into LTL (§4.3) and a bounded inference/expansion recursion guard.
Bus aliases resolve for indexing, `SIZEOF` and set identity; evaluated indices
must lie within the resolved declaration bounds (§4.5). To preserve distinct
signals in flattened output (§4.5), a signal declaration named `<bus>_<i>` is
rejected if that bit belongs to another declared bus; this check uses complete
names and resolved widths, including overrides. Flattened names have no
fixed-size buffer limit.
Formula-valued set elements retain closed high-level syntax, with identity
determined by their desugared core formulas (§4.8); weak and strong next remain
distinct. These rules change behavior relative to earlier releases, including
set cardinality and membership. Finite semantics and strong indexed next remain
supported extensions.

Expression precedence and associativity follow TLSF v1.1 Table 1 (p.118),
including all alternative operator names. Multiplication binds tighter than
right-associative division/modulo; implication and equivalence share one
right-associative level. `W` binds tighter than `U`, then `R`; `W`/`U` associate
right and `R` associates left. Pattern matching and guards bind loosest, so
`n == 0 || n == 2 : o` tests the whole disjunction. Numeric reductions have
level 1, set reductions level 5 and boolean reductions level 11.
TLSF §4.6 gives consecutive function cases no separator (`(ec)+`). The single
parser in `src/lib/tlsf.y` uses longest match: a guard or value continues as far
as the Table 1 expression grammar allows. Binary minus continues the value,
and `identifier (` continues as a call, even across whitespace or comments.
Thus `n == 0 : 0 -n < 0 : 1` groups as `(n == 0 : (0 - n < 0)) : 1`
(Table 1 row 19 associates `:` left). Similarly, `o (n)` becomes `o(n)`;
normal type checking then applies. To force separate cases, write
`n == 0 : (0) (-n < 0) : 1`. Reduction heads such as `&&[` start a new case
when they cannot continue the preceding expression. `otherwise` also starts
a new case. Prefix operators still compose across levels, for example
`MIN CUP[k IN {1,2}] {k}`. These choices deliberately change earlier releases' readings.
If delimiter/binder lookahead still leaves two complete readings with the same
outer boundaries, parsing fails with `ambiguous function case boundary or
expression`, for example `SUM[0 < i < 2 < j < 4] i` with two candidate binders.
Parentheses around the intended bound resolve that ambiguity; no parse is guessed.
Range bounds must be numerical expressions (§4.7); guards belong only to
function cases (§4.6). Guarded bounds such as `SUM[true : 0 <= i < 2] i`
are rejected. Plain range binders and bounded `F[l:u]`/`G[l:u]` remain supported.
There are no deliberate Table 1 precedence deviations. Existing extensions
`X[n]`, strong next (`X[!]`, `X[!n]`, `X[n!]`) and bounded `F`/`G` (including
strong bounds) retain level 11; unary minus retains level 1. `GEQ` remains an
alias of `>=`. `M` remains an ordinary TLSF identifier; infix `M` is rejected.
Existing keyword reuse also accepts infix `SUM` at level 4, `PROD` at level 2,
`FORALL` at level 12 and `EXISTS` at level 13; indexed `PLUS`/`MUL` use level 1.
The LTL output printer retains the separate ASCII LTL precedence documented
below; use `--parenthesize` when inspecting the exact temporal tree.

| Stable tool | Purpose |
|---|---|
| `tlsf2ltl` | Convert expanded TLSF to LTL. |
| `tlsf2tlsf` | Emit expanded/basic TLSF. |
| `tlsfinfo` | Inspect metadata, signals, and GR level. |
| `tlsfnorm` | Normalize, split, and simplify TLSF. |
| `mealy2moore` | Delay AIGER strategy outputs for Moore-target specs. |

The optional research layer adds decomposition, certified local controllers,
exact OxiDD safety/GR(1) solving, and residual export. Build these
executables with `-Dresearch_tools=true`; they are excluded from stable release
archives and the stable preprocessing API.

| Research tool | Purpose |
|---|---|
| `tlsftemplates` | Inspect template certificates and CSNF output. |
| `tlsfbenchgraph` | Report corpus benchmarks and structural shapes. |
| `tlsfresidual` | Emit residual clusters after sound decomposition. |
| `tlsfcompose` | Plan decomposed synthesis and merge AIGER strategies. |
| [`tlsfsym`](src/tools/tlsfsym/README.md) | Census of declared-index symmetries. |
| `tlsfcertcheck` | Independent native GR(1) certificate and policy checking. |
| `tlsfsolve` | Solve [AbsSynthe](https://github.com/gaperez64/AbsSynthe)-style AIGER safety/GR(1) games with OxiDD. |

## Build

Requires C23 and C++20 compilers, [Meson](https://mesonbuild.com/),
[Ninja](https://ninja-build.org/), `flex`, `bison`, Cargo (Rust 1.91+), and
`cbindgen` 0.29.4. Every build includes OxiDD and native GR(1); `research_tools`
controls only optional executables. The library, tests, CI and offline tools use only in-house checks.

Initialize OxiDD before configuring either source build:

```sh
git submodule update --init --recursive
meson setup build --buildtype=release
ninja -C build -j 2

# Research tools
meson setup build-research -Dresearch_tools=true --buildtype=release
ninja -C build-research -j 2
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
Unresolved residuals return UNKNOWN unless the user explicitly selects a command.
GR(1) tries general
monitor admission after a default unsupported decline. The
[Lean reference and bounded validation](proofs/README.md#automaton-translation-validation)
cover both policies; runtime formulas without a validated golden rely on the
proved reference and validation sample, not a proof of the C implementation.

## Usage

The preprocessing tools (`tlsf2ltl`, `tlsf2tlsf`, `tlsfinfo`, `tlsfnorm`)
read `FILE` or stdin, write stdout or `--output FILE`, and accept `--version`
and `--help` with long option names. `mealy2moore` and the research solver
`tlsfsolve` write strategies to stdout; redirect it as shown below. Both accept
`-h` for help and `--version`. `tlsfsolve` also accepts `-v` for diagnostic
verbosity in debug builds.

Install the tools or add the selected build directories to `PATH`:

```sh
export PATH="$PWD/build:$PWD/build-research:$PATH"
```

Research examples require `-Dresearch_tools=true`. Supply your own `spec.tlsf`,
strategies, corpus directories and `panel.list`. The automata generator requires
an Acacia build configured with `-Dbuild_research_tools=true`.

```sh
# convert
tlsf2ltl  spec.tlsf                       # spec's LTL (ltlxba, minimal parens)
tlsf2ltl  --format ltl spec.tlsf          # plain LTL
tlsf2ltl  --format latex spec.tlsf        # LaTeX math
tlsf2ltl  --strong-simplify spec.tlsf     # NNF + push/pull simplification, etc.
tlsf2ltl  --safety spec.tlsf              # syntactic safety fragment
tlsf2ltl  --liveness spec.tlsf            # syntactic liveness fragment
tlsf2ltl  --fair-environment spec.tlsf     # assume every input toggles forever
tlsf2tlsf --fair-environment spec.tlsf     # add scalar/quantified fairness
tlsf2tlsf --basic spec.tlsf               # fully expanded basic TLSF
tlsf2tlsf --provenance-out origin.json spec.tlsf  # expanded TLSF + source origins
mealy2moore strategy.aag > strategy.moore.aag  # delay Mealy outputs one step

# inspect
tlsfinfo  spec.tlsf                        # all metadata (--semantics, --title, …)
tlsfinfo  --input-signals spec.tlsf        # declared inputs (bus notation)
tlsfinfo  --output-signals spec.tlsf       # declared outputs (bus notation)
tlsfinfo  --expanded-ins spec.tlsf         # scalar input CSV
tlsfinfo  --expanded-outs spec.tlsf        # scalar output CSV
tlsfinfo  --generalized-reactivity spec.tlsf   # GR(k) level, or "NOT in GR"

# research / diagnostics
tlsftemplates --certify --solve --format csnf spec.tlsf   # certified controllers
tlsfbenchgraph --input-dir specs/ --split --summary       # corpus shape census
tlsfbenchgraph --source-features spec.tlsf                # leakage-free selector row
scripts/automata_study.py --file-list panel.list --output run/ \
  --tlsfnorm build-research/tlsfnorm --tlsf2ltl build-research/tlsf2ltl \
  --tlsfinfo build-research/tlsfinfo --tlsfbenchgraph build-research/tlsfbenchgraph \
  --automata-generator /path/to/acacia-research-build/src/acacia-automata-study

# normalize / decompose / synthesize
tlsfnorm  --passes split,nnf,boolean spec.tlsf            # re-emit normalized TLSF
tlsfnorm  --pre-passes pre-safe --passes match-safe:1 spec.tlsf  # exact-recognition normalization
tlsfnorm  --passes route-safe:1 spec.tlsf                 # routing normalization
tlsfnorm  --passes sickert-stage2:1 --norm-max-growth 300 spec.tlsf  # experimental, infinite-word-only
tlsfnorm  --norm-stats --passes match-safe:1 spec.tlsf    # per-pass normalization stats
tlsfresidual --split --output-dir out/ spec.tlsf          # one residual.k.ltl per cluster
tlsfresidual --split --lowercase spec.tlsf                # lowercase formulas + interfaces
tlsfcompose --split --output-dir out/ spec.tlsf           # controllers.aag + clusters + exact OxiDD solves
tlsfcompose --split --realizability spec.tlsf             # fast REAL/UNREAL/UNKNOWN oracle
# After supplying every residual controller:
tlsfcompose --merge out/controllers.aag out/cluster.*.aag # recombine strategies
scripts/solve.sh --output ctrl.aag spec.tlsf  # native controllers; UNKNOWN if unresolved
scripts/solve.sh --backend acacia --solver acacia-bonsai \
        --output ctrl.aag spec.tlsf                            # acacia backend
tlsfsolve game.aag > strategy.aag                         # solve an AIGER safety/GR(1) game
```

`tlsfnorm --norm-soundness verify` is an alias for the default `assert`:
both check schedule metadata for phase legality and finite-word safety. They
do not run a semantic equivalence checker; `off` skips that metadata gate.

Normalization diagnostics count pass invocations, including no-ops, rejected
candidates and list-level splits. Each accepted invocation that changes a tree
counts once, even for compound passes or splits producing several conjuncts.
Formula totals count visits (the CLI visits each formula once per scheduled
pass); split output node counts sum the resulting conjuncts. Pass node sums
include attempted candidates, while aggregate output nodes count retained
results. `time_ns` sums measured rewrite time, including rejected attempts,
excluding statistics collection. Passing a null stats pointer disables these
measurements. TSV diagnostics now use pass names and `passes_changed_total`,
and separate `rejected_growth` from `rejected_nodes`; these are intentional
diagnostic schema/count changes. Formula, interface and artifact output is
unchanged.

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
- pkg-config: `pkg-config --cflags --static --libs tlsf` (includes the static
  library's private link dependencies)

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

Embedding fragment: supply `spec_text`, `MyFormula` and `MyFormulaBuilder`
in your application.

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
## Synthesis and solver pipelines

`tlsfcompose` certifies local controllers, solves eligible residuals in process,
and writes remaining clusters. For file-based controller export:

```sh
mkdir -p out && tlsfcompose --split --output-dir out/ spec.tlsf
sh out/compose.sh
scripts/solve.sh --output ctrl.aag spec.tlsf
```

`controllers.aag` contains the certified part; trusted exact/UNDER routes can
write `cluster.k.aag`, and trusted OVER routes can stop on UNREAL. Remaining
`cluster.k.ltl` files carry `c ins=`/`c outs=` interface comments. Only those
exact metadata lines are comments: `c -> p` is a valid formula.
`tlsfcompose --merge` combines compatible AIGER strategies.

Generated drivers return UNKNOWN for unresolved residuals by default. An
explicit `--solver /path/to/command` or `TLSFCOMPOSE_SOLVER` selects a single
executable (CLI takes precedence). It must implement `--ins`, `--outs`, `-F`,
`--realizability`, and finite `--semantics=Mealy|Moore`; use a wrapper to adapt
another protocol. Quoted `.formula` files and anchored interface expressions
preserve AP identity. Infinite Moore verdict exports use `.mealy` with delayed
inputs. No external synthesizer is discovered or selected automatically.

`scripts/solve.sh` exports and merges infinite Mealy controllers. Native
presolving is used first; unresolved clusters return UNKNOWN unless an explicit
command is selected. It refuses finite and Moore controller export. Its command
backend and optional acacia adapter lowercase formulas/interfaces and reject
collisions. Faithful `--format ltl` exports preserve case and identifiers such
as `Grant`, `@` and names containing apostrophes; classic `ltlxba` exports
reject identifiers they cannot represent.

The research reports provide corpus shapes, normalization comparisons, and
wrapper performance:

```sh
tlsfbenchgraph --input-dir benchmarks/tlsf --split --summary > shapes.tsv
tlsftemplates --certify --solve --format csnf spec.tlsf
scripts/benchgraph.py --corpus benchmarks/tlsf \
  --tlsfcompose build-research/tlsfcompose \
  --solver /path/to/acacia-build/src/acacia-bonsai
scripts/collect_route_stats.py --compose build-research/tlsfcompose \
  --timeout 5 --out route_stats.tsv benchmarks/tlsf
```

The first command reports per-spec metrics and aggregate template distributions.
`collect_route_stats.py` does not invoke an external residual synthesizer;
route collection can run native Boolean prechecks. It writes rows incrementally
and skips slow specs. [BENCHGRAPH.md](BENCHGRAPH.md) holds wrapper results; `--from-data`
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
  LTLf-valid identities.
- **Mealy/Moore**: from `SEMANTICS`; for infinite words, a `TARGET` mismatch
  is converted (Moore→Mealy delays all environment inputs `i↦X i`;
  Mealy→Moore delays outputs `o↦X o`). Under finite-word semantics, target
  adaptation is unsupported: `SEMANTICS` and `TARGET` must
  agree. The adapting CLIs and decomposition API refuse finite mismatches;
  `tlsf_convert` refuses all finite semantics.

Generated drivers return UNKNOWN for unsupported native residual games.
Finite and Moore controller export remains unsupported by `scripts/solve.sh`.

Output is minimally parenthesised by the classic ASCII LTL precedence
(`! X F G` > `U R W` > `&&` > `||` > `-> <->`). `--parenthesize` fully
parenthesises; `--format` picks the spelling (`ltlxba`/`ltl`/`latex`).
Equivalence-preserving rewrites are exposed as flags
(`--weak-simplify` and `--strong-simplify` correspond to SyFCo's `-s0` and `-s1`).
Other flags are `--nnf`, `--no-weak-until`, `--no-release`,
`--no-strong-release`, `--no-finally`, `--no-globally`, `--push-globally-in`,
`--push-finally-in`, `--push-next-in`, `--pull-globally-out`,
`--pull-finally-out`, and `--pull-next-out`.
The rewrites have native regression checks and a Lean reference; independent
direct-semantics sampling checks the committed normalized objectives.

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

Development tests may build dependencies. Use clang-format 22.1.8 (as in CI);
the clang-tidy command below checks C sources.

```sh
meson test -C build
meson setup build-cov -Dresearch_tools=true -Db_coverage=true && meson test -C build-cov
git ls-files -z -- '*.[ch]' '*.cc' '*.cpp' '*.hh' '*.hpp' | xargs -0 clang-format -i
clang-tidy -p build src/lib/*.c src/tools/*/*.c
bench/bench.sh             # report timings for the current build
bench/bench.sh --baseline  # write replacement baseline data
bench/bench.sh --check     # fail on wall-time/RSS regressions
```

CI (`.github/workflows/ci.yml`) checks formatting, GCC/Clang builds, tests,
Valgrind leaks, 75% line coverage, and `bench.sh --check` wall/RSS regressions.
Licensed under [MIT](LICENSE).

Offline golden verification and membership regeneration use the independent
direct-semantics evaluator, seeded in-house formulas, native OxiDD/certificates,
and kernel-checked Lean translation validation. Historical verdicts that cannot
be independently renewed remain frozen, with their original provenance. See
[the golden guide](test/fixtures/golden/README.md) for serial commands and scope.

Source changes require behaviour checks and current proof correspondence
references. Per-PR source-hash ledgers are no longer required. When golden
output changes, regenerate `test/fixtures/golden/MANIFEST.sha256` in the same PR
and explain why the output changed, following the golden guide.
