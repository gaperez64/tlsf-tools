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

```sh
tlsf2tlsf spec.tlsf              # expanded basic TLSF on stdout
tlsf2ltl  spec.tlsf              # the spec's LTL formula (ltlxba), minimal parens
tlsf2ltl --parenthesize spec.tlsf  # fully parenthesised LTL
tlsf2ltl --safety   spec.tlsf    # only the safety part
tlsf2ltl --liveness spec.tlsf    # only the liveness part

tlsfinfo spec.tlsf               # all metadata
tlsfinfo -s spec.tlsf            # just the semantics  (-t -d -g -a -p -ins -outs -i)
```

`tlsf2ltl` emits the single LTL formula defined by the TLSF semantics. For the
standard (non-strict) semantics:

```
(INITIALLY ∧ G REQUIRE ∧ ASSUME)  →  (PRESET ∧ G ASSERT ∧ GUARANTEE)
```

(REQUIRE/ASSERT are invariants, wrapped in `G`; empty sections drop out and a
trivial antecedent collapses to just the consequent). All of the following are
taken from the spec's `SEMANTICS` field — there are no flags for them:

- **Strict** (`Strict,*`): emits `((PRESET ∧ G ASSERT) W ¬(INITIALLY ∧ G
  REQUIRE)) ∧ (E → GUARANTEE)`.
- **Finite-word** (`Finite,*`): renders strong-next as `X[!]`.
- **Mealy/Moore**: read from `SEMANTICS`; when it disagrees with `TARGET` the
  formula is converted to the target (Moore→Mealy delays outputs `o ↦ X o`,
  Mealy→Moore delays inputs `i ↦ X i`).

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
meson test -C build
```

GitHub Actions (`.github/workflows/ci.yml`) builds with both gcc and clang,
runs the suite, and runs a valgrind no-leak check on each binary.

## License

[MIT](LICENSE).
