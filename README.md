# tlsf-tools

Small, fast, Unix-style command-line tools for working with
[TLSF](https://github.com/reactive-systems/syfco) (Temporal Logic Synthesis
Format) specifications, sharing a common C library.

| Tool | Input | Output |
|---|---|---|
| `tlsf2ltl`  | TLSF 1.1/1.2 spec | LTL formula — `ltlxba` (default, for [spot](https://spot.lre.epita.fr/), `ltl2ba`, `ltl3ba`), `ltl`, or `latex`; with optional simplification/rewrites |
| `tlsf2tlsf` | TLSF 1.1/1.2 spec | Expanded *basic* TLSF (no `GLOBAL` section, flat formula lists) |
| `tlsfinfo`  | TLSF 1.1/1.2 spec | Metadata (title, description, semantics, target, tags, parameters, signals) |
| `tlsfgraph` | TLSF 1.1/1.2 spec | Synthesis graph (GSNF) + template candidates + WL features — `text`/`gsnf`/`dot`/`tsv` |
| `tlsfwl`    | TLSF 1.1/1.2 specs | Weisfeiler-Lehman features / similarity matrix for clustering & retrieval |
| `tlsftemplates` | TLSF 1.1/1.2 spec | Certify template-solvable blocks → CSNF (decoders, schedulers, certificates) |

These are a lightweight, dependency-free alternative to the relevant parts of
[`syfco`](https://github.com/reactive-systems/syfco): given a parameterised
TLSF specification, fully expand it (parameters, definitions — including
recursive case-definitions — bus unrolling, bounded `&&[..]`/`||[..]`
operators, indexed `X[n]` and bounded `G[i:j]`/`F[i:j]`, `enum` types, and
`SIZEOF`) and emit either a ground TLSF spec or the equivalent LTL formula.

## Pipeline

```
TLSF file
   │  parse            (flex + bison)
   ▼
raw AST (definition calls, bus indices, bounded quantifiers, case guards, …)
   │  expand           (params → defs → buses → quantifiers)
   ▼
ground AST
   ├── tlsf2tlsf ───► basic TLSF
   │
   │  build the single spec formula → optional transforms (simplify, NNF,
   │  push/pull, operator replacement) → print in the chosen dialect
   ▼
   └── tlsf2ltl  ───► LTL  (ltlxba / ltl / latex;  --safety / --liveness / all)
```


## Building

Requires a C23 compiler, [meson](https://mesonbuild.com/),
[ninja](https://ninja-build.org/), `flex`, and `bison`.

```sh
meson setup build
ninja -C build
# binaries: build/{tlsf2ltl,tlsf2tlsf,tlsfinfo,tlsfgraph,tlsfwl,tlsftemplates}
```

With sanitizers:

```sh
meson setup build-san -Dsanitize=address,undefined
ninja -C build-san
```

## Usage

The tools read a `FILE` argument (`tlsfwl` takes several) or, if none is given,
stdin; they write to stdout or to `--output FILE`; and they accept `--version`
and `--help`. Options use long (`--`) names only.

```sh
tlsf2tlsf spec.tlsf                 # expanded basic TLSF on stdout
tlsf2tlsf --basic spec.tlsf         # fully expand to the basic fragment
cat spec.tlsf | tlsf2ltl            # read from stdin
tlsf2ltl  spec.tlsf                 # the spec's LTL formula (ltlxba), minimal parens
tlsf2ltl --parenthesize spec.tlsf   # fully parenthesised LTL
tlsf2ltl --format ltl spec.tlsf     # pure-LTL ASCII (like syfco -f ltl)
tlsf2ltl --format latex spec.tlsf   # LaTeX math output
tlsf2ltl --strong-simplify spec.tlsf            # simplify (syfco -s1)
tlsf2ltl --safety / --liveness spec.tlsf      # only the safety / liveness part
tlsf2ltl --overwrite-semantics Mealy spec.tlsf  # also --overwrite-target
tlsf2ltl --output out.ltl spec.tlsf

tlsfinfo spec.tlsf                  # all metadata
tlsfinfo --semantics spec.tlsf      # one field (--title --description --target
                                    #   --tags --parameters --input-signals
                                    #   --output-signals --info)
tlsfinfo --generalized-reactivity spec.tlsf   # the GR(k) level, or "NOT in GR"
tlsfinfo --check spec.tlsf          # "valid" if the spec parses, else error

tlsfgraph spec.tlsf                 # text summary of the synthesis graph
tlsfgraph --templates spec.tlsf     # + template candidates (response/mutex/…)
tlsfgraph --format gsnf spec.tlsf   # machine-readable GSNF (line format)
tlsfgraph --format dot spec.tlsf    # Graphviz DOT
tlsfgraph --wl 3 spec.tlsf          # + Weisfeiler-Lehman features (depth 3)

tlsfwl --matrix a.tlsf b.tlsf c.tlsf   # all-pairs WL similarity matrix
tlsfwl --nearest 3 *.tlsf              # top-3 nearest spec per spec

tlsftemplates spec.tlsf                # candidate template blocks
tlsftemplates --certify --solve --format csnf spec.tlsf   # certified CSNF
```

`tlsf2ltl` emits the single LTL formula defined by the TLSF semantics:

```
INITIALLY → ( PRESET ∧ ( (G REQUIRE ∧ ASSUME) → (G ASSERT ∧ GUARANTEE) ) )
```

(REQUIRE/ASSERT are invariants, wrapped in `G`; empty sections drop out.
`INITIALLY` is the outer guard and `PRESET` sits *outside* the
assumption→guarantee implication — matching `syfco`, so the system's initial
obligations hold even when the environment violates an assumption.) The rest
is taken from the (possibly overwritten) `SEMANTICS`/`TARGET`:

- **Strict** (`Strict,*`): emits the safety weak-until form `((PRESET ∧ G
  ASSERT) W ¬(INITIALLY ∧ G REQUIRE)) ∧ (E → GUARANTEE)`. To relax it to the
  plain `E → S`, overwrite the semantics: `--overwrite-semantics Mealy`.
- **Finite-word** (`Finite,*`): emits `ltlxba-fin` automatically — strong-next
  prints as `X[!]` (weak next stays `X`), and the weak-until / strong-release
  operators (which `ltl2ba-fin` lacks) are rewritten with the LTLf-valid
  identities `a W b = (a U b) ∨ G a` and `a M b = b U (a ∧ b)`, so the output is
  accepted by finite-word tools such as spot's `ltlfsynt`.
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

### Output dialects (`--format`)

`tlsf2ltl --format VALUE` selects the operator spelling (precedence and
parenthesisation are identical across all three):

- `ltlxba` *(default)* — ltl2ba / spot ASCII.
- `ltl` — pure-LTL ASCII matching `syfco -f ltl` (keeps `W`/`R`/`M`).
- `latex` — LaTeX math (`\land`, `\lor`, `\rightarrow`, `\mathsf{G}`,
  `\mathbin{\mathsf{U}}`, …; atoms wrapped in `\mathit{…}`). Drop the output
  into a `$…$` (or `\[ … \]`) math context. syfco has no LaTeX output.

### Formula transformations

These are equivalence-preserving rewrites of the emitted formula, off by
default, mirroring the corresponding `syfco` flags:

- `--weak-simplify` (`-s0`) — constant folding and redundancy removal.
- `--strong-simplify` (`-s1`) — `-s0` + NNF + `--no-weak-until --no-release
  --pull-globally-out --pull-finally-out --pull-next-out`.
- `--nnf` — negation normal form.
- `--no-weak-until` / `--no-release` / `--no-finally` / `--no-globally` —
  replace that operator by its definition (`a W b ⇒ (a U b) ∨ G a`, etc.);
  `--no-derived` = `--no-weak-until --no-finally --no-globally`.
- `--push-globally-in` / `--push-finally-in` / `--push-next-in` and the
  inverse `--pull-globally-out` / `--pull-finally-out` / `--pull-next-out` —
  distribute / factor a modality over `&&` / `||`.

Every transform preserves meaning, so the result is `ltlfilt --equivalent-to`
the untransformed formula (and to `syfco -s1` where the spec is in syfco's
fragment).

> **Note:** the `--safety` / `--liveness` split is **purely syntactic**, not a
> semantic safety/liveness decomposition. After conversion to negation normal
> form, a formula is treated as *safety* iff its syntax tree contains no `F`,
> `U`, or `M` node (and *liveness* otherwise). NNF is applied first so that,
> e.g., `!(G p)` becomes `F !p` and is correctly classified as liveness. A
> formula that is semantically a safety property but written with liveness
> operators will be classified as liveness.

## Synthesis graph (`tlsfgraph`)

`tlsfgraph` works on TLSF *structure* — the expanded constraint cover, before
flattening to one LTL formula — and exposes synthesis-relevant structure as a
**Graph Structural Normal Form (GSNF)**. Each section formula becomes a
constraint that keeps its role (INITIALLY/PRESET/REQUIRE/ASSERT/ASSUME/
GUARANTEE), assumption/guarantee side, invariant wrapping, syntactic
safety/liveness class, and input/output support; syntactic *template
candidates* are recognized over those constraints:

- `response` `G(r -> F g)`, `mutex` `G(!(a && b) …)`, `pure-recurrence` `G F x`,
  `persistence` `F G x`, `guarded-next-assignment` `G(α -> X o)`,
  `definition` `G(o <-> θ)`; and a multi-constraint `arbiter_candidate` block
  (responses + a grant mutex).

```sh
tlsfgraph --templates spec.tlsf            # text summary + candidate counts
tlsfgraph --format gsnf --templates spec.tlsf > spec.gsnf
tlsfgraph --format dot spec.tlsf | dot -Tsvg > spec.svg
tlsfgraph --guarantees --liveness --format tsv spec.tlsf   # filtered table
```

The machine-readable `gsnf` format is **DIMACS-style**: `c` comment lines, a
`p gsnf …` header, then one tagged record per line (`i`/`o` signals,
`n` constraints, `k` candidates, `f` formulas, `e` edges, `t` template blocks).
It is trivial to parse with `fgets`/`strtok` — no JSON.

Output is **candidate-only**: `tlsfgraph` never rewrites, removes, certifies,
or solves anything — a recognized candidate is a starting point for analysis,
not a proof.

### Weisfeiler-Lehman features (`--wl`, `tlsfwl`)

`tlsfgraph --wl N` appends a WL color-refinement histogram (a structural
fingerprint of the synthesis graph) as `v <count> <key>` lines;
`--wl-labels basic|synthesis|template` chooses the labelling. `tlsfwl` compares
specs by these features:

```sh
tlsfwl --matrix --wl 3 specs/*.tlsf        # all-pairs cosine similarity
tlsfwl --compare ref.tlsf cand/*.tlsf      # each candidate vs a reference
tlsfwl --nearest 5 --kernel jaccard *.tlsf # top-5 nearest spec per spec
```

WL is a *similarity heuristic, never a proof* — it suggests; templates verify.

### Templates & CSNF (`tlsftemplates`)

`tlsftemplates` moves recognized candidates to a **Certified Strategy Normal
Form (CSNF)**, honouring the soundness ladder *candidate → checked → certified
→ solved*: a block is `solved` only after a sound (conservative, syntactic)
side condition passes and a controller/decoder + certificate is produced.

```sh
tlsftemplates spec.tlsf                          # list candidate blocks
tlsftemplates --certify --solve --format csnf spec.tlsf > spec.csnf
```

Four templates are certified this milestone:

- **definition** `G(o<->θ)` → decoder `o := θ` (iff `o` is a Mealy output not
  occurring in `θ`); cert `definition_decoder`.
- **round-robin** (`GF o_i` ×k + grant mutex) → one-hot finite cycle (iff the
  `o_i` occur in no other constraint); cert `round_robin_scheduler`.
- **guarded-next-assignment** `G(α->X o)` / `G(β->X¬o)` → `o' := ⋁α` (iff the
  force-true/false guards are provably exclusive); cert
  `guarded_assignment_consistency`.
- **mutex** `G atMostOne(…)` → *certified* safety invariant (`mutex_safety`),
  not solved on its own.

Anything not provably sound stays `candidate`; nothing is removed (residual
export is the next milestone). CSNF is the same DIMACS-style line format as
GSNF (`b`/`bc`/`dec`/`nsf`/`cyc`/`cert`/`cl`/`do`/`r` records).

`tlsfgraph`/`tlsfwl`/`tlsftemplates` are the implemented slice of a larger
proposed analysis/normalization/synthesis layer. Later milestones (residual
export, controller composition, normalization passes) are not yet implemented
and the corresponding flags (`--norm-depth`, `--from-gsnf`,
`--side-conditions sat|bdd`, …) report a clear "not implemented" error;
`--graph formula|quotient` is likewise reserved.

## Checking output against `syfco`

`tlsf2tlsf` aims to produce the same expanded TLSF as `syfco`'s basic-TLSF
output. The LTL emitted by `tlsf2ltl` is **not** byte-for-byte identical to
`syfco`/`ltl2ba` output (parenthesisation and the section-combining structure
differ), but it is semantically equivalent. Equivalence can be checked with
`ltlfilt` from the [spot](https://spot.lre.epita.fr/) toolset:

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
meson test -C build        # ~0.2s, ~100 cases
```

Coverage (needs `gcovr`):

```sh
meson setup build-cov -Db_coverage=true
meson test -C build-cov
gcovr --root . --filter 'src/' --print-summary
```

GitHub Actions (`.github/workflows/ci.yml`) checks `clang-format`, builds with
both gcc and clang, runs the full suite (it is fast), runs a valgrind no-leak
check on each binary, gates line coverage at 75%, and runs a
performance-regression guard (`bench/bench.sh --check`).

## Formatting & linting

Code style is [`.clang-format`](.clang-format) (LLVM, 2-space, 80 columns),
enforced in CI. Static analysis is [`.clang-tidy`](.clang-tidy); run it
manually before pushing:

```sh
clang-format -i src/*.c include/tlsf/*.h     # apply formatting
clang-tidy -p build src/*.c                  # lint
```

## Limitations

Relative to `syfco`, not yet implemented: the structured synthesis output
formats (`smv`, `slugs`/`slugsin`, `promela`, `wring`, …), partition (`.part`)
files, and config files (`-r`/`-w`). `tlsf2ltl` does emit the `ltlxba`, `ltl`
and `latex` LTL dialects and the `-s0`/`-s1`/push/pull/operator-replacement
transformations; `tlsf2tlsf` emits basic/full TLSF.

The full TLSF surface is parsed, including `enum` type definitions (a typed
signal `mode S;` becomes a bus of the enum's bit width, `S == LABEL` expands to
the positional bit match, and each enum-typed signal carries the implicit
"always a valid value" invariant) and the temporal-operator letter `M` reused
as an identifier. All **2545** SYNTCOMP `tlsf` and **2487** `tlsf-fin`
benchmarks convert.

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
