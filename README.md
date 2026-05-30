# tlsf-tools

Two small, fast, Unix-style command-line tools for working with
[TLSF](https://github.com/reactive-systems/syfco) (Temporal Logic Synthesis
Format) specifications, sharing a common C library.

| Tool | Input | Output |
|---|---|---|
| `tlsf2ltl`  | TLSF 1.1/1.2 spec | LTL formula in `ltlxba` syntax (for [spot](https://spot.lre.epita.fr/), `ltl2ba`, `ltl3ba`, …) |
| `tlsf2tlsf` | TLSF 1.1/1.2 spec | Expanded *basic* TLSF (no `GLOBAL` section, flat formula lists) |
| `tlsfinfo`  | TLSF 1.1/1.2 spec | Metadata (title, description, semantics, target, tags, parameters, signals) |

These cover the two transformations most commonly needed in a reactive
synthesis toolchain, and are intended as a lightweight, dependency-free
alternative to the relevant parts of
[`syfco`](https://github.com/reactive-systems/syfco): given a parameterised
TLSF specification, fully expand it (parameters → definitions → bus unrolling
→ patterns) and emit either a ground TLSF spec or the equivalent LTL formula.

## Pipeline

```
TLSF file
   │  parse            (flex + bison)
   ▼
raw AST (may contain definition calls, bus indices, patterns, quantifiers, …)
   │  expand           (params → defs → buses → patterns)
   ▼
ground AST
   ├── tlsf2tlsf ───► basic TLSF
   │
   │  to NNF, then classify each guarantee/assertion as SAFETY or LIVENESS
   ▼
   └── tlsf2ltl  ───► ltlxba LTL   (--safety / --liveness / default: all)
```

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the full design and the AST node
taxonomy.

## Building

Requires a C23 compiler, [meson](https://mesonbuild.com/),
[ninja](https://ninja-build.org/), `flex`, and `bison`.

```sh
meson setup build
ninja -C build
# binaries: build/tlsf2ltl  build/tlsf2tlsf
```

With sanitizers:

```sh
meson setup build-san -Dsanitize=address,undefined
ninja -C build-san
```

## Usage

All three tools read a `FILE` argument or, if none is given, stdin; they write
to stdout or to `--output FILE`; and they accept `--version` and `--help`.
Options use long (`--`) names only.

```sh
tlsf2tlsf spec.tlsf                 # expanded basic TLSF on stdout
tlsf2tlsf --basic spec.tlsf         # fully expand to the basic fragment
cat spec.tlsf | tlsf2ltl            # read from stdin
tlsf2ltl  spec.tlsf                 # the spec's LTL formula (ltlxba), minimal parens
tlsf2ltl --parenthesize spec.tlsf   # fully parenthesised LTL
tlsf2ltl --safety / --liveness spec.tlsf      # only the safety / liveness part
tlsf2ltl --overwrite-semantics Mealy spec.tlsf  # also --overwrite-target
tlsf2ltl --output out.ltl spec.tlsf

tlsfinfo spec.tlsf                  # all metadata
tlsfinfo --semantics spec.tlsf      # one field (--title --description --target
                                    #   --tags --parameters --input-signals
                                    #   --output-signals --info)
tlsfinfo --generalized-reactivity spec.tlsf   # the GR(k) level, or "NOT in GR"
tlsfinfo --check spec.tlsf          # "valid" if the spec parses, else error
```

`tlsf2ltl` emits the single LTL formula defined by the TLSF semantics:

```
(INITIALLY ∧ G REQUIRE ∧ ASSUME)  →  (PRESET ∧ G ASSERT ∧ GUARANTEE)
```

(REQUIRE/ASSERT are invariants, wrapped in `G`; empty sections drop out and a
trivial antecedent collapses to just the consequent). The rest is taken from
the (possibly overwritten) `SEMANTICS`/`TARGET`:

- **Strict** (`Strict,*`): emits the safety weak-until form `((PRESET ∧ G
  ASSERT) W ¬(INITIALLY ∧ G REQUIRE)) ∧ (E → GUARANTEE)`. To relax it to the
  plain `E → S`, overwrite the semantics: `--overwrite-semantics Mealy`.
- **Finite-word** (`Finite,*`): renders strong-next as `X[!]`.
- **Mealy/Moore**: read from `SEMANTICS`; when it disagrees with `TARGET` the
  formula is converted to the target (Moore→Mealy delays outputs `o ↦ X o`,
  Mealy→Moore delays inputs `i ↦ X i`).

`--overwrite-semantics VALUE` and `--overwrite-target VALUE` (on both
`tlsf2ltl` and `tlsf2tlsf`) replace the spec's `SEMANTICS`/`TARGET` from the
CLI.

By default `tlsf2ltl` prints with the minimal parentheses implied by the
operator precedence shared by spot/ltl2ba and the TLSF papers (tightest
first): unary `! X F G` > `U R W M` > `&&` > `||` > `-> <->`. Pass
`--parenthesize` to fully parenthesise every subformula instead.

> **Note:** the `--safety` / `--liveness` split is **purely syntactic**, not a
> semantic safety/liveness decomposition. After conversion to negation normal
> form, a formula is treated as *safety* iff its syntax tree contains no `F`,
> `U`, or `M` node (and *liveness* otherwise). NNF is applied first so that,
> e.g., `!(G p)` becomes `F !p` and is correctly classified as liveness. A
> formula that is semantically a safety property but written with liveness
> operators will be classified as liveness.

## Checking output against `syfco`

`tlsf2tlsf` aims to produce the same expanded TLSF as `syfco`'s basic-TLSF
output. The LTL emitted by `tlsf2ltl` is **not** byte-for-byte identical to
`syfco`/`ltl2ba` output (it is fully parenthesised), but it is semantically
equivalent. Equivalence can be checked with `ltlfilt` from the
[spot](https://spot.lre.epita.fr/) toolset:

```sh
ltlfilt --equivalent-to="$(syfco -f ltlxba spec.tlsf)" \
        -f "$(tlsf2ltl spec.tlsf)" && echo equivalent
```

Test specifications can be drawn from the
[SYNTCOMP benchmarks](https://github.com/SYNTCOMP/benchmarks) (`tlsf` and
`tlsf-fin` directories).

## Tests

A self-contained golden-output regression suite lives under `test/cases/` (a
representative spread of SYNTCOMP specs with their expected tool output). It
needs no external tools, so it runs anywhere:

```sh
meson test -C build        # ~0.2s, ~50 cases
```

Coverage (needs `gcovr`):

```sh
meson setup build-cov -Db_coverage=true
meson test -C build-cov
gcovr --root . --filter 'src/' --print-summary
```

GitHub Actions (`.github/workflows/ci.yml`) checks `clang-format`, builds with
both gcc and clang, runs the full suite (it is fast), runs a valgrind no-leak
check on each binary, and reports line coverage.

## Formatting & linting

Code style is [`.clang-format`](.clang-format) (LLVM, 2-space, 80 columns),
enforced in CI. Static analysis is [`.clang-tidy`](.clang-tidy); run it
manually before pushing:

```sh
clang-format -i src/*.c include/tlsf/*.h     # apply formatting
clang-tidy -p build src/*.c                  # lint
```

## Limitations

Relative to `syfco`, not yet implemented: TLSF named patterns, the `X[n]`
n-fold next operator, and output formats other than `ltlxba` and basic TLSF
(e.g. `smv`, `slugs`, `promela`). Of the SYNTCOMP `tlsf` benchmarks, 547/569
convert (the rest use those constructs); all 1717 `tlsf-fin` benchmarks
convert.

## Benchmarking

`bench/bench.sh` measures wall-clock time (median of N runs) and peak resident
memory over the specs in `bench/specs/`:

```sh
bench/bench.sh                 # comparison table: ours vs syfco
bench/bench.sh --baseline      # record our numbers in bench/baseline.tsv
bench/bench.sh --check         # fail on a regression vs the recorded baseline
```

`--check` runs only our tool (no syfco needed) and flags a regression when the
median time exceeds the baseline by `TIME_TOL` or peak RSS by `MEM_TOL`; CI runs
it as a guard. For reference, on a ~100 KB spec `tlsf2ltl` is around 20× faster
and uses roughly 7× less memory than `syfco -f ltlxba`.

## License

[MIT](LICENSE).
