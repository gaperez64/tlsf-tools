# tlsf-tools

Small, fast, Unix-style command-line tools for working with
[TLSF](https://github.com/reactive-systems/syfco) (Temporal Logic Synthesis
Format) specifications, sharing a common C library.

The normal release build uses OxiDD (<https://github.com/OxiDD/oxidd>) as the
in-process BDD backend for safety and GR(1) games. 
[ltlsynt](https://spot.lre.epita.fr/ltlsynt.html) is mentioned below, but it is
not a library dependency of this project; it is an optional executable used by
`scripts/solve.sh` and by the Docker wrapper image.

The tools fully expand parameterised TLSF (parameters, definitions including
recursive case definitions, bus unrolling, bounded `&&[..]`/`||[..]`, indexed
`X[n]` and bounded `G[i:j]`/`F[i:j]`, `enum` types, `SIZEOF`) and emit a ground
TLSF spec or equivalent LTL. The synthesis layer adds structure-aware
decomposition, certified local controllers, exact OxiDD-backed safety/GR(1)
routes, and an external residual-solving wrapper for `ltlsynt`.

## Status

### Stable tools

| Tool | Purpose |
|---|---|
| `tlsf2ltl` | Convert expanded TLSF to LTL. |
| `tlsf2tlsf` | Emit expanded/basic TLSF. |
| `tlsfinfo` | Inspect metadata, signals, and GR level. |
| `tlsfnorm` | Normalize/split/simplify TLSF before synthesis. |
| `tlsfresidual` | Emit residual clusters after sound decomposition. |
| `tlsfcompose` | Build a decomposed synthesis plan; merge AIGER strategy files. |
| `tlsfsolve` | Solve [AbsSynthe](https://github.com/gaperez64/AbsSynthe)-style AIGER safety/GR(1) games with OxiDD. |

### Research and diagnostic tools

Built with `-Dresearch_tools=true`; included in release archives for
reproducibility, but not part of the stable preprocessing API.

| Tool | Purpose |
|---|---|
| `tlsftemplates` | Inspect template certificates and CSNF output. |
| `tlsfbenchgraph` | Generate corpus-level benchmark/shape reports. |

The preprocessor uses equivalence-preserving normalization followed by exact
syntactic recognizers and conservative certification. It does not use graph
similarity or approximate matching in the synthesis path.

```
TLSF file ──parse──► raw AST ──expand──► ground AST ──► tlsf2tlsf  (basic TLSF)
                  (flex+bison)  (params→defs→buses→quantifiers)  └──► tlsf2ltl  (LTL)
ground AST ──► tlsfnorm      (normalized TLSF)
           ├──► tlsfresidual (residual clusters)
           └──► tlsfcompose  (residual clusters + controllers.aag → plan)
```

## Building

Requires a C23 compiler, [meson](https://mesonbuild.com/),
[ninja](https://ninja-build.org/), `flex`, `bison`, Rust/cargo, and
`cbindgen` for release-quality OxiDD-enabled builds.

Release-quality build:

```sh
git submodule update --init --recursive
scripts/build_oxidd.sh
meson setup build -Doxidd=enabled --buildtype=release
ninja -C build
```

Reduced developer/frontend-only build:

```sh
meson setup build-min -Doxidd=disabled
ninja -C build-min
```

Research/diagnostic tools:

```sh
git submodule update --init --recursive
scripts/build_oxidd.sh
meson setup build-research -Doxidd=enabled -Dresearch_tools=true --buildtype=release
ninja -C build-research
```

Sanitizers are available for development builds with
`-Dsanitize=address,undefined`.

## Usage

Each tool reads a `FILE` argument or stdin, writes to stdout or `--output FILE`,
and accepts `--version`/`--help`. Options are long (`--`) only.

```sh
# convert
tlsf2ltl  spec.tlsf                       # spec's LTL (ltlxba, minimal parens)
tlsf2ltl  --format ltl|latex spec.tlsf    # plain LTL / LaTeX math
tlsf2ltl  --strong-simplify spec.tlsf     # NNF + push/pull simplification, etc.
tlsf2ltl  --safety | --liveness spec.tlsf # syntactic split of the formula
tlsf2tlsf --basic spec.tlsf               # fully expanded basic TLSF

# inspect
tlsfinfo  spec.tlsf                        # all metadata (--semantics, --title, …)
tlsfinfo  --input-signals|--output-signals spec.tlsf    # declared (bus notation)
tlsfinfo  --expanded-ins|--expanded-outs   spec.tlsf    # scalar CSV for ltlsynt --ins/--outs
tlsfinfo  --generalized-reactivity spec.tlsf   # GR(k) level, or "NOT in GR"

# structure / templates
tlsftemplates --certify --solve --format csnf spec.tlsf   # certified controllers
tlsfbenchgraph --input-dir specs/ --split --summary       # corpus shape census

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
scripts/solve.sh --solver ltlsynt --output ctrl.aag spec.tlsf  # external-solver flow
tlsfsolve game.aag > strategy.aag                         # solve an AIGER safety/GR(1) game
```

`tlsfsolve` reads an [AbsSynthe](https://github.com/gaperez64/AbsSynthe)-style AIGER game: uncontrollable inputs are
ordinary inputs, controllable inputs are prefixed `controllable_`, safety games
use a `bad` output, and GR(1) games may use AIGER 1.9 `justice`/`fairness`
records. It emits a strategy AAG on stdout or exits nonzero with `UNREALIZABLE`.

## Embeddable API

The installed library exposes decomposition/preprocessing without AIGER structs
or internal AST types:

- C header: `#include <tlsf/decompose.h>`
- C++ wrapper: `#include <tlsf/decompose.hpp>`
- Meson: `dependency('tlsf')`
- pkg-config: `pkg-config --cflags --libs tlsf`

`tlsf_decompose_string()` / `tlsf_decompose_file()` return duplicated strings:
preprocessed LTL, global inputs/outputs, residual clusters
`{ltl, inputs, outputs}`, semantics/target, GR level, a fast pre-check verdict,
and trust tags. Free the C result with `tlsf_decompose_result_free()`. The C++
wrapper returns `std::string` / `std::vector` values and frees the C handle via
RAII.

```cpp
#include <tlsf/decompose.hpp>

tlsf::Options opt;
opt.split = true;
tlsf::Result r = tlsf::decompose(spec_text, opt);
for (const tlsf::Cluster &c : r.clusters) {
  // c.ltl, c.inputs, c.outputs
}
```

No `Aig`, OxiDD, AST, cover, CSNF, or arena type crosses this API. AIGER
strategies cross process boundaries as files and are recombined with
`tlsfcompose --merge`.

## Example pipelines

### 1 · Preprocess a spec, then synthesize the residual

Decompose first: certify the combinational controllers and hand only the
*residual* to a backend. Each `cluster.k.ltl` carries its own interface in
header comments (`c ins=…`, `c outs=…`), and disjoint-output clusters are
independent — several small `ltlsynt`/`strix` calls instead of one giant one.

```sh
mkdir out && tlsfcompose --split --output-dir out/ spec.tlsf
sh out/compose.sh                                  # ltlsynt per cluster -> verdict
# or drive a backend yourself, per cluster (strip the 'c ' header lines to a
# file and read it with -F; a large cluster overflows ltlsynt's --formula= arg):
grep -v '^c ' out/cluster.0.ltl > out/cluster.0.f
ltlsynt --ins=… --outs=… -F out/cluster.0.f
```

`--output-dir` also writes `controllers.aag`, a mergeable AIGER strategy for
the certified part. Trusted OxiDD-eligible residual outcomes are handled in
process with one persistent BDD session: exact routes and strengthened/UNDER
routes can emit `cluster.k.aag`, while weakened/OVER routes can stop early on
trusted UNREAL. The remaining clusters stay as `cluster.k.ltl`.
`scripts/solve.sh` automates the full flow:

```sh
scripts/solve.sh --solver ltlsynt --output ctrl.aag spec.tlsf
```

For the `ltlsynt` backend the script passes `--lowercase` so the emitted
cluster formulas, `c ins=`, `c outs=`, and AIGER symbols agree. The `acacia`
backend block is explicit in the script and is the intended swap-in point for
an acacia-bonsai invocation. Pre-solved and external strategies are recombined
with `tlsfcompose --merge`.

### 2 · One merged controller circuit (AIGER)

The supported controller flow is file-based: decompose, solve every emitted
cluster with the backend of your choice, then merge those AIGER strategies with
the certified part.

```sh
scripts/solve.sh --solver ltlsynt --output ctrl.aag spec.tlsf
# verify it against the spec (Spot):
python3 scripts/verify_aiger_ltl.py --aiger ctrl.aag \
        --tlsf2ltl build/tlsf2ltl --tlsf spec.tlsf
```

### 3 · Normalize, then feed any LTL synthesizer

`tlsfnorm` re-emits clean TLSF (split conjunctions, NNF, boolean simplify);
`tlsf2ltl` gives the formula and `tlsfinfo --expanded-ins/--expanded-outs` the
scalar interface, so any spot/Strix-style tool can take over. The `ltlxba`
dialect lowercases atoms (spot/ltl2ba read uppercase letters as operators), so
lowercase the interface to match; the faithful `ltl` dialect keeps the original
case. `tlsfcompose` and `tlsfresidual` keep original case by default and apply
lowercasing to formulas and interfaces only with `--lowercase`.

```sh
tlsfnorm --passes split,nnf,boolean spec.tlsf > spec.norm.tlsf
lc() { tr 'A-Z' 'a-z'; }                                  # ltlxba lowercases atoms
ins=$(tlsfinfo  --expanded-ins  spec.norm.tlsf | lc)      # scalar CSV, buses unrolled
outs=$(tlsfinfo --expanded-outs spec.norm.tlsf | lc)
tlsf2ltl spec.norm.tlsf > spec.norm.ltl                   # read via -F (a big
ltlsynt --ins="$ins" --outs="$outs" -F spec.norm.ltl      # formula overflows -f)
```

### 4 · Census a benchmark set by type / template

Census the structural shapes across a corpus.

```sh
# per-spec shape/template metrics + an aggregate distribution (mutex/response/…)
tlsfbenchgraph --input-dir benchmarks/tlsf --split --summary > shapes.tsv

# look at one spec's certified templates (response / mutex / arbiter / …)
tlsftemplates --certify --solve --format csnf spec.tlsf
```

### 5 · Measure route shape and wrapper performance

How much does decomposition change the residual shape, and how does the wrapper
pipeline compare with `acacia-bonsai` alone? `scripts/benchgraph.py` writes the
[`BENCHGRAPH.md`](BENCHGRAPH.md) head-to-head section (solved counts, net gain,
and a survival plot). `scripts/collect_route_stats.py` records route diagnostics
without running a solver.

```sh
# full corpus speed + complexity (rerunnable; --from-data re-renders the report)
scripts/benchgraph.py --corpus benchmarks/tlsf \
        --tlsfcompose build-oxidd/tlsfcompose \
        --solver ../acacia-bonsai/build_best_decomp_mona/src/acacia-bonsai

# route-only corpus census; writes rows incrementally and skips slow specs
scripts/collect_route_stats.py --compose build-oxidd/tlsfcompose \
        --timeout 5 --out route_stats.tsv benchmarks/tlsf
```

## How the synthesis layer works

The preprocessor works on TLSF *structure* — the expanded constraint cover,
before flattening to one LTL formula: each section formula keeps its role, side,
invariant wrapping, syntactic safety/liveness class, and signal support. Over it,
exact syntactic **template candidates** are recognized (response `G(r→F g)`,
mutex, recurrence `G F x`, persistence `F G x`, reaction, definition,
guarded-next, arbiter, …). `--split` first decomposes each constraint into its
top-level `&&` conjuncts (distributing `G`/`X` along the spine,
equivalence-preserving), which is what makes most templates visible. Optional
equivalence-preserving normalization (`tlsfnorm` or `--match-normalize`) can
expose more of these exact shapes before
recognition without changing the spec's meaning.

`tlsftemplates` promotes candidates to a **Certified Strategy Normal Form
(CSNF)** along the ladder *candidate → checked → certified → solved*: a block is
`solved` only behind a sound, conservative side condition (usually *free-output*:
the target output occurs in no other constraint). Certified families cover the
combinational/finite slice — decoders (`o:=θ`), set/reset/toggle/delay registers,
reaction logic, and liveness schedulers (response/round-robin/arbiter). Stateful
safety games and GR(1)-style reactivity need a real solver, not a syntactic
certificate, and stay `candidate`.

`tlsfresidual` then substitutes the solved combinational outputs away and emits
the residual over a *smaller* alphabet, **clustering** it by shared output
(`E → ⋀ᵢ Gᵢ ≡ ⋀ᵢ (E → Gᵢ)` when output sets are disjoint) into independent,
parallelisable sub-problems. Reached assumptions are kept regardless of
safety/liveness class; pruning drops only assumptions over disjoint signals, so
the residual decomposition is labelled **TRUST_EXACT**. The emitted cluster
formula is the formula solved and trusted.

`tlsfcompose` turns that into a runnable plan: `controllers.aag` carries the
certified part; trusted OxiDD residual controllers may also appear as
`cluster.k.aag`; each `cluster.k.ltl` carries an exact residual formula plus
`c ins=`/`c outs=` comments; and `--merge` recombines AIGER strategy files. The
spec is **realizable iff every cluster is**, so the certified controllers ⊕ one
trusted controller per cluster realise the whole spec. The machine format
(`csnf`) is DIMACS-style line records (`fgets`/`strtok`, no JSON).

`tlsfcompose --realizability` is a fast verdict-only oracle. The always-on
UNREAL pre-check is **TRUST_OVER**: it refutes a weakening, so UNREAL is trusted
and REAL is never claimed. The REAL pre-check is **TRUST_UNDER**: it proves a
strengthening, so REAL is trusted and UNREAL is never claimed. If neither fires,
the command exits `2` with `UNKNOWN`.

Corpus shape distributions and the templates+OxiDD solve-rate / speed numbers
live in [`BENCHGRAPH.md`](BENCHGRAPH.md); exact recognizers plus conservative
certification are the proof — there is no approximate matching in the synthesis
path.

## What `tlsf2ltl` emits

The single LTL formula defined by the TLSF semantics:

```
INITIALLY → ( PRESET ∧ ( (G REQUIRE ∧ ASSUME) → (G ASSERT ∧ GUARANTEE) ) )
```

`REQUIRE`/`ASSERT` are wrapped in `G`; `PRESET` sits *outside* the
assumption→guarantee implication; empty sections drop out. The
shape then follows the (possibly overwritten) `SEMANTICS`/`TARGET`:

- **Strict** (`Strict,*`) — the safety weak-until form
  `((PRESET ∧ G ASSERT) W ¬(INITIALLY ∧ G REQUIRE)) ∧ (E → GUARANTEE)`;
  `--overwrite-semantics Mealy` relaxes it to plain `E → S`.
- **Finite-word** (`Finite,*`) — emits `ltlxba-fin`: strong-next prints `X[!]`,
  and `W`/`M` are rewritten with LTLf-valid identities so spot's `ltlfsynt`
  accepts it.
- **Mealy/Moore** — from `SEMANTICS`; a `TARGET` mismatch is converted
  (Moore→Mealy delays outputs `o↦X o`, Mealy→Moore delays inputs `i↦X i`).

Output is minimally parenthesised by the spot/ltl2ba precedence
(`! X F G` > `U R W M` > `&&` > `||` > `-> <->`); `--parenthesize` fully
parenthesises. `--format` picks the spelling (`ltlxba`/`ltl`/`latex`).
Equivalence-preserving rewrites are exposed as flags
(`--weak-simplify`=`-s0`, `--strong-simplify`=`-s1`, `--nnf`,
`--no-{weak-until,release,finally,globally}`, `--{push,pull}-{globally,finally,next}-{in,out}`);
every result is `ltlfilt --equivalent-to` the input.

> The `--safety`/`--liveness` split is **syntactic**: after NNF, *safety* iff the
> tree has no `F`/`U`/`M` node. A safety property written with liveness operators
> is classified as liveness.

## Tests, formatting, benchmarking

```sh
meson test -C build                                  # fast golden-output suite
meson setup build-cov -Doxidd=disabled -Db_coverage=true && meson test -C build-cov
clang-format -i src/*.c include/tlsf/*.h             # style (LLVM, 2-space, 80col)
clang-tidy -p build src/*.c                          # lint
bench/bench.sh [--baseline|--check]                  # wall/RSS perf-regression guard
```

CI (`.github/workflows/ci.yml`) checks formatting, builds with gcc and clang,
runs the suite + a valgrind no-leak check, gates line coverage at 75 %, and runs
the `bench.sh --check` regression guard.

## License

[MIT](LICENSE).
