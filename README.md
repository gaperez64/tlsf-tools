# tlsf-tools

Command-line tools and a C library (`libtlsf.a`) for expanding TLSF
specifications into ground TLSF or LTL.

| Stable tool | Purpose |
|---|---|
| `tlsf2ltl` | Convert expanded TLSF to LTL. |
| `tlsf2tlsf` | Emit expanded/basic TLSF. |
| `tlsfinfo` | Inspect metadata, signals, and GR level. |
| `tlsfnorm` | Normalize, split, and simplify TLSF. |
| `tlsfobf` | Rename identifiers and permute order, with a self-check. |
| `mealy2moore` | Delay AIGER strategy outputs for Moore-target specs. |

Build the optional research tools with `-Dresearch_tools=true`. They are
excluded from stable release archives and the stable preprocessing API.

| Research tool | Purpose |
|---|---|
| `tlsftemplates` | Inspect template certificates and CSNF output. |
| `tlsfbenchgraph` | Report corpus metrics and structural shapes. |
| `tlsfresidual` | Emit residual clusters after decomposition. |
| `tlsfcompose` | Plan decomposed synthesis and merge AIGER strategies. |
| [`tlsfsym`](src/tools/tlsfsym/README.md) | Find verified declared-index permutations. |
| `tlsfcertcheck` | Check native GR(1) certificates and policies. |
| `tlsfsolve` | Solve AbsSynthe-style AIGER safety/GR(1) games with OxiDD. |

## Build

Requires C23 and C++20 compilers, [Meson](https://mesonbuild.com/),
[Ninja](https://ninja-build.org/), `flex`, `bison`, Cargo (Rust 1.91+), and
`cbindgen` 0.29.4. Every build includes OxiDD and native GR(1).

```sh
git submodule update --init --recursive
meson setup build --buildtype=release
ninja -C build -j 2

# Research tools
meson setup build-research -Dresearch_tools=true --buildtype=release
ninja -C build-research -j 2
```

`tests`, `tools`, and `examples` default to `true`. For a library-only build,
pass `-Dtests=false -Dtools=false -Dexamples=false`. Tests require tools;
`fuzz=true` requires tests. Disabling tools also skips research executables.
A Meson parent can use:

```meson
tlsf_native = subproject('tlsf-tools', default_options: [
  'tests=false', 'tools=false', 'examples=false', 'research_tools=false',
])
tlsf_deps = [tlsf_native.get_variable('tlsf_dep')]
```

Use `-Dsanitize=address,undefined` for sanitizers.
`-Dcpu=baseline|x86-64-v2|avx2|avx512|neon|native` selects the compiler target;
AP-set kernels use portable C loops. JSON uses installed yyjson 0.12.0 or the
pinned wrap fallback, which installs yyjson and its pkg-config file.

## Usage

Preprocessing tools read `FILE` or stdin, write stdout or `--output FILE`, and
accept `--help` and `--version`. `mealy2moore` and `tlsfsolve` write strategies
to stdout and accept `-h` for help. Add the builds to `PATH`:

```sh
export PATH="$PWD/build:$PWD/build-research:$PATH"
tlsf2ltl  --format ltl spec.tlsf          # plain LTL
tlsf2ltl  --strong-simplify spec.tlsf     # NNF + push/pull simplification, etc.
tlsf2tlsf --basic spec.tlsf               # fully expanded basic TLSF
tlsf2tlsf --provenance-out origin.json spec.tlsf  # expanded TLSF + source origins
tlsfinfo  --expanded-ins spec.tlsf         # scalar input CSV
tlsfinfo  --expanded-outs spec.tlsf        # scalar output CSV
tlsfobf --mode rename --seed 7 --map map.tsv spec.tlsf  # neutral names + TSV map
tlsfnorm  --passes split,nnf,boolean spec.tlsf            # re-emit normalized TLSF
mealy2moore strategy.aag > strategy.moore.aag  # delay Mealy outputs one step
```

`tlsfobf` modes are `rename`, `reorder`, and `all` (default). Output is
repeatable for the same input, seed and mode. Every parameter needs a value:
before writing, the tool expands both specs and checks their interfaces and
section formulas up to renaming and AND/OR associativity/commutativity.
`--map` includes expanded signal names for renaming controllers back.

`tlsfnorm --norm-stats` reports pass invocations, changes, rejected growth and
node limits. `--norm-soundness verify` and default `assert` check schedule
metadata and finite-word safety; they do not check semantic equivalence.
Sickert passes are experimental and infinite-word only.

`--fair-environment` adds `G F i` and `G F !i` assumptions for each input bit.
It preserves existing assumptions and rejects finite-word semantics.
`--safety`/`--liveness` classify syntax after NNF: safety has no F, U, or
internally derived strong-release node.

## TLSF semantics

The reference is TLSF v1.1 by Jacobs, Klein and Schirmer
([arXiv:1604.02284](https://arxiv.org/abs/1604.02284)), including Table 1
precedence. The following interpretations and extensions affect input files:

- Function arguments may shadow globals under a lexical reading of §4.6's
  "fresh" arguments, compatible with the SYNTCOMP corpus. Loop and pattern
  binders still reject declared-name clashes.
- Finite semantics, indexed next `X[n]`, strong next (`X[!]`, `X[!n]`,
  `X[n!]`), and bounded F/G (including strong bounds) are supported extensions.
  Temporal extensions have precedence level 11; unary minus has level 1.
- `GEQ` aliases `>=`. Infix `SUM`, `PROD`, `FORALL`, and `EXISTS` use levels
  4, 2, 12, and 13; indexed `PLUS`/`MUL` use level 1. `M` is an ordinary
  TLSF identifier; infix `M` is rejected.
- Consecutive function cases use longest match. Binary minus and
  `identifier (` continue an expression across whitespace/comments. Write
  `n == 0 : (0) (-n < 0) : 1` to separate those cases. Ambiguous binder
  boundaries require parentheses. Range bounds must be numeric, not guards.
- A declaration named `<bus>_<i>` is rejected if another bus flattens to that
  signal. Formula-set identity uses desugared core formulas (§4.8), keeping
  weak and strong next distinct.

`tlsf2ltl` assembles the ordinary objective:

```text
INITIALLY → ( PRESET ∧ ( (G REQUIRE ∧ ASSUME) → (G ASSERT ∧ GUARANTEE) ) )
```

Strict semantics use the §3.2 objective with `ASSERT W ¬REQUIRE`.
Target adaptation applies for infinite words: Moore→Mealy delays inputs and
Mealy→Moore delays outputs. Under finite-word semantics, target adaptation is
unsupported: `SEMANTICS` and `TARGET` must agree. The adapting CLIs and
decomposition API reject mismatches; `tlsf_convert` refuses all finite semantics.

Output defaults to `ltlxba`, with precedence
`! X F G` > `U R W` > `&&` > `||` > `-> <->`. Use `--parenthesize` for the
full tree or `--format ltl|latex` for other spellings. Plain LTL preserves
identifier case, `@`, and apostrophes; `ltlxba` rejects unrepresentable names.
Finite output uses `ltlxba-fin` and prints strong next as `X[!]`.

## Library API

Use `#include <tlsf/decompose.h>` or its C++ wrapper `tlsf/decompose.hpp`.
`tlsf_decompose_string()` / `tlsf_decompose_file()` return LTL, signal lists,
residual clusters, semantics/target, GR level, pre-check verdict and trust tags.
Free C results with `tlsf_decompose_result_free()`; C++ results own their values.
`tlsf/ast_api.h` and `tlsf/ast_api.hpp` expose opaque expanded trees and a typed
C++ visitor. See [public headers](include/tlsf) and [examples](examples).
Link with `dependency('tlsf')` or `pkg-config --cflags --static --libs tlsf`.

## Research synthesis

```sh
tlsftemplates --certify --solve --format csnf spec.tlsf
tlsfresidual --split --output-dir out/ spec.tlsf
tlsfcompose --split --output-dir out/ spec.tlsf
tlsfcompose --split --realizability spec.tlsf
scripts/solve.sh --output ctrl.aag spec.tlsf
scripts/solve.sh --backend acacia --solver acacia-bonsai \
        --output ctrl.aag spec.tlsf
tlsfsolve game.aag > strategy.aag
```

CSNF (Certified Strategy Normal Form) is a DIMACS-style line format.
Candidate blocks are recognized shapes; certified blocks have passed side
conditions; solved blocks also have a controller or decoder.

`tlsfcompose` writes certified `controllers.aag`, locally solved
`cluster.k.aag`, and remaining `cluster.k.ltl` with `c ins=`/`c outs=` metadata.
After supplying residual controllers, merge with
`tlsfcompose --merge out/controllers.aag out/cluster.*.aag`.
Generated drivers return UNKNOWN for unresolved clusters unless `--solver`
or `TLSFCOMPOSE_SOLVER` selects an executable. Its protocol requires `--ins`,
`--outs`, `-F`, `--realizability`, and finite `--semantics=Mealy|Moore`.
`scripts/solve.sh` exports infinite Mealy controllers; it rejects finite/Moore
controller export. Command backends lowercase names and reject collisions.

Exact decomposition requires guarded definition elimination and disjoint
system outputs. Finite games and output-dependent environments keep one
cluster. Infinite Mealy games prune disjoint input-only assumptions only after
a positive joint lasso witness. `TRUST_EXACT` gives realizability equivalence;
`TRUST_OVER` supports UNREAL only, `TRUST_UNDER` REAL only. An inconclusive
`--realizability` result is UNKNOWN, exit 2. The [proof index](proofs/README.md)
maps claims to Lean theorems and states the remaining trust boundary.

See the [solver guide](docs/tlsfsolve-diagnostics.md),
[frontend provenance](docs/frontend-provenance.md),
[system region certificates](docs/gr1-region-method.md), and
[environment certificates](docs/gr1-environment-certificate.md).
The lift APIs' `decline_detail` buffers retain bounded discovery diagnostics;
`TlsfGr1LiftError.message` is a shorter summary. See
[gr1_lift.h](include/tlsf/gr1_lift.h).

For corpus workflows, see [benchmark usage](BENCHGRAPH.md) and the
[automata study](AUTOMATA-STUDY.md). `tlsfbenchgraph --source-features` emits
versioned TSV of declared interface sizes and source `guard_*` measurements;
it rejects splitting/normalization options.

## Development

```sh
meson test -C build
meson setup build-cov -Dresearch_tools=true -Db_coverage=true && meson test -C build-cov
git ls-files -z -- '*.[ch]' '*.cc' '*.cpp' '*.hh' '*.hpp' | xargs -0 clang-format -i
clang-tidy -p build src/lib/*.c src/tools/*/*.c
bench/bench.sh --check
```

Use clang-format 22.1.8. CI checks GCC/Clang builds, tests, leaks, 75% line
coverage and wall-time/RSS regressions. See the [fuzz guide](test/fuzz/README.md)
and [golden-fixture guide](test/fixtures/golden/README.md) for additional checks.
Licensed under [MIT](LICENSE).
