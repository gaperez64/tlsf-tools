# tlsf-tools

Small, fast, Unix-style command-line tools for working with
[TLSF](https://github.com/reactive-systems/syfco) (Temporal Logic Synthesis
Format) specifications, sharing a common C library.

| Tool | Input | Output |
|---|---|---|
| `tlsf2ltl`  | TLSF 1.1/1.2 spec | LTL formula — `ltlxba` (default, for [spot](https://spot.lre.epita.fr/), `ltl2ba`, `ltl3ba`), `ltl`, or `latex`; optional simplification/rewrites |
| `tlsf2tlsf` | TLSF 1.1/1.2 spec | Expanded *basic* TLSF (no `GLOBAL` section, flat formula lists) |
| `tlsfinfo`  | TLSF 1.1/1.2 spec | Metadata (title, semantics/target, signals, GR level, bounded-temporal origins) |
| `tlsfgraph` | TLSF 1.1/1.2 spec | Synthesis graph (GSNF) + template candidates + WL features — `text`/`gsnf`/`dot`/`tsv` |
| `tlsfwl`    | TLSF 1.1/1.2 specs | Weisfeiler-Lehman features / similarity matrix for clustering & retrieval |
| `tlsftemplates` | TLSF 1.1/1.2 spec | Certify template-solvable blocks → CSNF (decoders, schedulers, certificates) |
| `tlsfbenchgraph` | TLSF corpus (dir/list/files) | Per-spec form/template-shape metrics (TSV) + aggregate summary |
| `tlsfnorm`  | TLSF 1.1/1.2 spec | Local normalization (split / nnf / boolean passes), re-emitted as TLSF |
| `tlsfresidual` | TLSF 1.1/1.2 spec | Residual LTL after a *sound* template decomposition (for `ltlsynt`/`strix`, or safety/GR(1) clusters for OxiDD) |
| `tlsfcompose` | TLSF 1.1/1.2 spec | Decomposed-synthesis plan or merged AIGER: certified controllers + residual clusters + OxiDD (safety+GR(1)) and `ltlsynt` backends |

They are a lightweight, dependency-free alternative to the relevant parts of
[`syfco`](https://github.com/reactive-systems/syfco): given a parameterised TLSF
spec, fully expand it (parameters, definitions including recursive case
definitions, bus unrolling, bounded `&&[..]`/`||[..]`, indexed `X[n]` and
bounded `G[i:j]`/`F[i:j]`, `enum` types, `SIZEOF`) and emit a ground TLSF spec or
the equivalent LTL — plus a structure-aware analysis/decomposition/synthesis
layer (`tlsfgraph`…`tlsfcompose`) that `syfco` does not have.

```
TLSF file ──parse──► raw AST ──expand──► ground AST ──► tlsf2tlsf  (basic TLSF)
                  (flex+bison)  (params→defs→buses→quantifiers)  └──► tlsf2ltl  (LTL)
ground AST ──► tlsfgraph/tlsftemplates (structure, candidates, certified controllers)
           └──► tlsfresidual/tlsfcompose (residual clusters + backends → plan / AIGER)
```

## Building

Requires a C23 compiler, [meson](https://mesonbuild.com/),
[ninja](https://ninja-build.org/), `flex`, and `bison`.

```sh
meson setup build && ninja -C build
# build/{tlsf2ltl,tlsf2tlsf,tlsfinfo,tlsfgraph,tlsfwl,tlsftemplates,
#        tlsfbenchgraph,tlsfnorm,tlsfresidual,tlsfcompose}
meson setup build-san -Dsanitize=address,undefined   # sanitizers (optional)
```

Optional OxiDD backend (in-process safety + GR(1) BDD solver; requires Rust/cargo + cbindgen):

```sh
meson compile -C build oxidd-submodule oxidd-build   # or: scripts/build_oxidd.sh
meson setup build-oxidd -Doxidd=enabled && ninja -C build-oxidd
```

## Usage

Each tool reads a `FILE` argument (`tlsfwl` takes several) or stdin, writes to
stdout or `--output FILE`, and accepts `--version`/`--help`. Options are long
(`--`) only.

```sh
# convert
tlsf2ltl  spec.tlsf                       # spec's LTL (ltlxba, minimal parens)
tlsf2ltl  --format ltl|latex spec.tlsf    # syfco-style LTL / LaTeX math
tlsf2ltl  --strong-simplify spec.tlsf     # syfco -s1 (NNF + push/pull, etc.)
tlsf2ltl  --safety | --liveness spec.tlsf # syntactic split of the formula
tlsf2tlsf --basic spec.tlsf               # fully expanded basic TLSF

# inspect
tlsfinfo  spec.tlsf                        # all metadata (--semantics, --title, …)
tlsfinfo  --input-signals|--output-signals spec.tlsf
tlsfinfo  --generalized-reactivity spec.tlsf   # GR(k) level, or "NOT in GR"

# structure / templates / similarity
tlsfgraph --split --templates spec.tlsf    # synthesis graph + candidate census
tlsfgraph --format dot spec.tlsf | dot -Tsvg > spec.svg
tlsftemplates --certify --solve --format csnf spec.tlsf   # certified controllers
tlsfwl    --nearest 5 --wl 3 *.tlsf        # k-NN by structural fingerprint
tlsfbenchgraph --input-dir specs/ --split --summary       # corpus shape census

# normalize / decompose / synthesize
tlsfnorm  --passes split,nnf,boolean spec.tlsf            # re-emit normalized TLSF
tlsfresidual --split --output-dir out/ spec.tlsf          # one residual.k.ltl per cluster
tlsfcompose --split --output-dir out/ spec.tlsf           # controllers + clusters + compose.sh
tlsfcompose --split --aiger spec.tlsf                     # one merged AIGER controller (OxiDD + ltlsynt)
```

## Example pipelines

### 1 · Preprocess a spec, then synthesize the residual

Decompose first: certify the combinational controllers and hand only the
*residual* to a backend. Each `cluster.k.ltl` carries its own interface in
header comments (`c ins=…`, `c outs=…`), and disjoint-output clusters are
independent — several small `ltlsynt`/`strix` calls instead of one giant one.

```sh
mkdir out && tlsfcompose --split --output-dir out/ spec.tlsf
sh out/compose.sh                                  # ltlsynt per cluster -> verdict
# or drive a backend yourself, per cluster (strip the 'c ' header lines):
ltlsynt --ins=… --outs=… --formula="$(grep -v '^c ' out/cluster.0.ltl)"
```

### 2 · One merged controller circuit (AIGER)

`--aiger` closes the loop: certified controllers become and-inverter gates,
eligible safety clusters go to OxiDD (in-process BDD safety + GR(1) solver),
everything else to `ltlsynt`, and the output-disjoint strategies are merged into
one `aag` over the full interface.

```sh
tlsfcompose --split --aiger spec.tlsf > ctrl.aag          # OxiDD build required
# verify it against the spec (Spot):
python3 scripts/verify_aiger_ltl.py --compose build-oxidd/tlsfcompose \
        --tlsf2ltl build/tlsf2ltl --tlsf spec.tlsf
```

### 3 · Normalize, then feed any LTL synthesizer

`tlsfnorm` re-emits clean TLSF (split conjunctions, NNF, boolean simplify);
`tlsf2ltl` gives the formula and `tlsfinfo` the interface, so any spot/Strix-style
tool can take over. The `ltlxba` dialect lowercases atoms (spot/ltl2ba read
uppercase letters as operators — as `syfco -f ltlxba` does), so lowercase the
interface to match; the faithful `ltl` dialect keeps the original case.

```sh
tlsfnorm --passes split,nnf,boolean spec.tlsf > spec.norm.tlsf
lc() { tr 'A-Z' 'a-z' | tr -d ' '; }
ins=$(tlsfinfo  --input-signals  spec.norm.tlsf | lc)
outs=$(tlsfinfo --output-signals spec.norm.tlsf | lc)
ltlsynt --ins="$ins" --outs="$outs" -f "$(tlsf2ltl spec.norm.tlsf)"   # ltlxba
```

### 4 · Cluster a benchmark set by type / template

Census the structural shapes across a corpus, then group specs by similarity.

```sh
# per-spec shape/template metrics + an aggregate distribution (mutex/response/…)
tlsfbenchgraph --input-dir benchmarks/tlsf --split --summary > shapes.tsv

# group by structural similarity (Weisfeiler-Lehman fingerprints of the graph)
tlsfwl --matrix  --wl 3 benchmarks/tlsf/*.tlsf > sim.matrix   # all-pairs cosine
tlsfwl --nearest 5 --wl 3 benchmarks/tlsf/*.tlsf              # k-NN per spec
tlsfwl --compare ref.tlsf cand/*.tlsf                         # rank vs a reference

# look at one spec's recognized templates (response / mutex / arbiter / …)
tlsfgraph --split --templates spec.tlsf
```

### 5 · Measure the self-contained / fast-preprocessor slice

How much do templates+OxiDD solve *without* `ltlsynt`, and is the pipeline
faster than `ltlsynt` alone? `scripts/benchgraph.py` answers both over a corpus
and writes the [`BENCHGRAPH.md`](BENCHGRAPH.md) "Preprocessor speed & complexity"
section.

```sh
# self-contained slice only: forbid the ltlsynt fallback
tlsfcompose --split --aiger --ltlsynt /bin/false spec.tlsf

# full corpus speed + complexity (rerunnable; --from-data re-renders the report)
scripts/benchgraph.py --corpus benchmarks/tlsf \
        --tlsfcompose build-oxidd/tlsfcompose --ltlsynt ltlsynt
```

## How the synthesis layer works

`tlsfgraph` works on TLSF *structure* — the expanded constraint cover, before
flattening to one LTL formula — as a **Graph Structural Normal Form (GSNF)**:
each section formula keeps its role, side, invariant wrapping, syntactic
safety/liveness class, and signal support. Over it, syntactic **template
candidates** are recognized (response `G(r→F g)`, mutex, recurrence `G F x`,
persistence `F G x`, reaction, definition, guarded-next, arbiter, …). Output is
*candidate-only* — nothing is rewritten or proved. `--split` first decomposes
each constraint into its top-level `&&` conjuncts (distributing `G`/`X` along the
spine, equivalence-preserving), which is what makes most templates visible.

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
parallelisable sub-problems. `tlsfcompose` turns that into a runnable plan or a
single merged AIGER, routing safety and GR(1) clusters to OxiDD (in-process BDD
solver) and pure liveness to `ltlsynt`. The spec is **realizable iff every
cluster is**, so the certified controllers ⊕ one controller per cluster realise
the whole spec. The machine formats (`gsnf`/`csnf`) are DIMACS-style line records
(`fgets`/`strtok`, no JSON).

Corpus shape distributions and the templates+OxiDD solve-rate / speed numbers
live in [`BENCHGRAPH.md`](BENCHGRAPH.md); WL similarity is a heuristic, templates
are the proof.

## What `tlsf2ltl` emits

The single LTL formula defined by the TLSF semantics:

```
INITIALLY → ( PRESET ∧ ( (G REQUIRE ∧ ASSUME) → (G ASSERT ∧ GUARANTEE) ) )
```

`REQUIRE`/`ASSERT` are wrapped in `G`; `PRESET` sits *outside* the
assumption→guarantee implication (matching `syfco`); empty sections drop out. The
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
Equivalence-preserving rewrites mirror `syfco`'s flags
(`--weak-simplify`=`-s0`, `--strong-simplify`=`-s1`, `--nnf`,
`--no-{weak-until,release,finally,globally}`, `--{push,pull}-{globally,finally,next}-{in,out}`);
every result is `ltlfilt --equivalent-to` the input. Check against syfco with
`ltlfilt --equivalent-to="$(syfco -f ltlxba spec.tlsf)" -f "$(tlsf2ltl spec.tlsf)"`.

> The `--safety`/`--liveness` split is **syntactic**: after NNF, *safety* iff the
> tree has no `F`/`U`/`M` node. A safety property written with liveness operators
> is classified as liveness.

## Tests, formatting, benchmarking

```sh
meson test -C build                                  # fast golden-output suite
meson setup build-cov -Db_coverage=true && meson test -C build-cov   # + coverage
clang-format -i src/*.c include/tlsf/*.h             # style (LLVM, 2-space, 80col)
clang-tidy -p build src/*.c                          # lint
bench/bench.sh [--baseline|--check]                  # wall/RSS vs syfco / guard
```

CI (`.github/workflows/ci.yml`) checks formatting, builds with gcc and clang,
runs the suite + a valgrind no-leak check, gates line coverage at 75 %, and runs
the `bench.sh --check` regression guard. On a ~100 KB spec `tlsf2ltl` is ~20×
faster and uses ~7× less memory than `syfco -f ltlxba`.

## Limitations

Relative to `syfco`, not implemented: structured synthesis outputs
(`smv`/`slugs`/`promela`/…), partition (`.part`) and config (`-r`/`-w`) files.
Reserved flags (`--from-gsnf`, `--from-csnf`, `--side-conditions sat|bdd`, …)
report a clear "not implemented" error.

## Future work

The preprocessor's job is to hand `ltlsynt` a *smaller, cheaper* problem and to
carve off what symbolic BDD methods do better — **not** to solve general
liveness in-process. A full liveness game backend is an LTL→automata translation
(determinize to parity/Rabin, then solve), i.e. reimplementing Spot; that work
stays delegated to `ltlsynt`. The realistic, automata-free levers are:

1. **Symbolic GR(2) / generalized-Rabin.** The OxiDD GR(1) fixpoint already
   solves the `⋀ G F aᵢ → ⋀ G F gⱼ` fragment without any determinization. Extend
   it to generalized-Rabin acceptance to reach the `amba_gr+` family — still a
   BDD fixpoint, no automata.
2. **Tighter decomposition → smaller residual.** More sound combinational/
   template eliminations and finer output-disjoint clustering shrink each
   cluster handed to `ltlsynt` without changing its job. This is exactly what the
   *residual-reduction* metric in [`BENCHGRAPH.md`](BENCHGRAPH.md) scores.
3. **Widen the BDD-fast fragment.** Symbolic GR(1) already beats automata
   construction on the specs `ltlsynt` times out on (large `amba_gr`); keep
   pushing more safety / GR(k)-shaped residuals onto the in-process solver so
   only genuinely automata-shaped liveness is forwarded.

See [roadmap](docs/ROADMAP-gr1-persistence.md) too.

## License

[MIT](LICENSE).
