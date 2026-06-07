# tlsf-tools

Small, fast, Unix-style command-line tools for working with
[TLSF](https://github.com/reactive-systems/syfco) (Temporal Logic Synthesis
Format) specifications, sharing a common C library.

| Tool | Input | Output |
|---|---|---|
| `tlsf2ltl`  | TLSF 1.1/1.2 spec | LTL formula — `ltlxba` (default, for [spot](https://spot.lre.epita.fr/), `ltl2ba`, `ltl3ba`), `ltl`, or `latex`; with optional simplification/rewrites |
| `tlsf2tlsf` | TLSF 1.1/1.2 spec | Expanded *basic* TLSF (no `GLOBAL` section, flat formula lists) |
| `tlsfinfo`  | TLSF 1.1/1.2 spec | Metadata (title, description, semantics, target, tags, parameters, signals, GR level, bounded temporal origins) |
| `tlsfgraph` | TLSF 1.1/1.2 spec | Synthesis graph (GSNF) + template candidates + WL features — `text`/`gsnf`/`dot`/`tsv` |
| `tlsfwl`    | TLSF 1.1/1.2 specs | Weisfeiler-Lehman features / similarity matrix for clustering & retrieval |
| `tlsftemplates` | TLSF 1.1/1.2 spec | Certify template-solvable blocks → CSNF (decoders, schedulers, certificates) |
| `tlsfbenchgraph` | TLSF corpus (dir/list/files) | Per-spec form/template-shape metrics (TSV) + aggregate summary |
| `tlsfnorm`  | TLSF 1.1/1.2 spec | Local normalization (split / nnf / boolean passes), re-emitted as TLSF |
| `tlsfresidual` | TLSF 1.1/1.2 spec | The residual LTL after a *sound* template decomposition (for `ltlsynt`/`strix`, or safety clusters for AbsSynthe) |
| `tlsfcompose` | TLSF 1.1/1.2 spec | Decomposed-synthesis plan or merged AIGER: certified controllers + residual clusters + optional AbsSynthe/`ltlsynt` backends |

These are a lightweight, dependency-free alternative to the relevant parts of
[`syfco`](https://github.com/reactive-systems/syfco): given a parameterised
TLSF specification, fully expand it (parameters, definitions — including
recursive case-definitions — bus unrolling, bounded `&&[..]`/`||[..]`
operators, indexed `X[n]` and bounded `G[i:j]`/`F[i:j]`, `enum` types, and
`SIZEOF`) and emit either a ground TLSF spec or the equivalent LTL formula.

## Recommended preprocessing pipeline

For synthesis, prefer decomposing the TLSF structure before handing residual LTL
to `ltlsynt`, `strix`, or another backend. The useful path is:

```sh
# 1. Optional inspection: expose the expanded basic spec.
tlsf2tlsf --basic spec.tlsf > spec.basic.tlsf

# 2. Split top-level conjunctions, certify local controllers, and inspect the
#    sound composition verdict.
tlsftemplates --split --check --format csnf spec.tlsf

# 3. Emit independent residual clusters after exact template substitution.
tlsfresidual --split --output-dir residuals spec.tlsf

# 4. Feed each residual.<k>.ltl to the backend named by its header comments
#    (`c ins=...`, `c outs=...`).
ltlsynt --ins='...' --outs='...' -F residuals/residual.0.ltl
```

For a generated driver instead of manual backend calls:

```sh
tlsfcompose --split --output-dir out spec.tlsf
sh out/compose.sh
```

For one merged controller circuit, use `tlsfcompose --aiger`. With AbsSynthe
available, eligible non-finite safety residuals are handled before falling back
to `ltlsynt`; `--ltlsynt /bin/false` is a useful way to measure the
self-contained slice.

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
# build/{tlsf2ltl,tlsf2tlsf,tlsfinfo,tlsfgraph,tlsfwl,tlsftemplates,tlsfbenchgraph,tlsfnorm,tlsfresidual,tlsfcompose}
```

With sanitizers:

```sh
meson setup build-san -Dsanitize=address,undefined
ninja -C build-san
```

Optional safety backend:

```sh
meson compile -C build abssynthe-submodule
meson compile -C build abssynthe-build
```

When `external/AbsSynthe/binary/abssynthe` exists, Meson enables the optional
real-AbsSynthe regression tests and `tlsfcompose --aiger --abssynthe PATH` can
synthesize eligible non-finite safety residual clusters without `ltlsynt`.

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
tlsfinfo --bounded-temporal spec.tlsf          # expanded X[k]/G[i:j]/F[i:j] origins
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

tlsfbenchgraph --input-dir specs/ --summary   # per-spec metrics TSV + totals

tlsfnorm --passes split spec.tlsf      # split conjunctive constraints, re-emit
tlsfgraph --split --templates spec.tlsf   # analyse with decomposition on
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
  `persistence` `F G x`, `reachability` `F g`, `guarded-next-assignment`
  `G(α -> X o)`, `reaction` `G(α -> o)`, `definition` `G(o <-> θ)`,
  `delayed-definition` `G(X o <-> θ)`; and a multi-constraint `arbiter_candidate`
  block (responses + a grant mutex).

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

The certified template library spans the Manna–Pnueli safety–progress hierarchy
(the classes [spot](https://spot.lre.epita.fr/hierarchy.html) draws), targeting
shapes with a known controller or where the side condition makes synthesis
syntactic. Most are gated by a **free-output** condition — the target output
occurs in no constraint outside the block, so a local controller can't violate
anything else.

*Safety:*

- **definition** `G(o<->θ)` → decoder `o := θ` (Mealy, `θ` combinational and
  `o`-free, `o` free outside the block); cert `definition_decoder`.
- **delayed-definition** `G(X o<->θ)` → register `o' := θ` (causal `θ`, `o`
  free); cert `delayed_definition_register`.
- **guarded-next-assignment** one-sided `G(α->X o)` or `G(β->X¬o)` groups →
  `o' := ⋁α`; cert `guarded_assignment_consistency`.
- **set-reset-register** mixed `G(α->X o)` + `G(β->X¬o)` groups → stateful
  register `o' := set ∨ (o ∧ ¬reset)` (set/reset guards provably exclusive);
  cert `set_reset_register`.
- **toggle-register** `G(t -> (X o <-> ¬o))` groups → stateful register
  `o' := o xor (⋁t)`; cert `toggle_register`.
- **fixed-delay-response** `G(α -> X^k o)`, `k >= 2` groups → delay-line
  register for `o`; cert `fixed_delay_response`.
- **reaction** `G(α_i->o)` / `G(β_i->¬o)` groups → combinational `o := ⋁α_i`
  (Mealy, positive/negative guard pairs exclusive; substituted into the
  residual); cert `reaction_consistency`.
- **mutex** `G atMostOne(…)` → *certified* safety invariant (`mutex_safety`),
  not solved on its own.
- **safety-invariant** `G(B)`, `B` temporal-free — the general stateless case:
  a memoryless Skolem `o := ¬B[o:=⊥]` (single- and multi-output) when its
  outputs are free and `∀inputs∃outputs.B` (a bounded propositional check); cert
  `safety_invariant`. (Real specs are mostly *stateful* safety, so this is a
  small slice — genuine safety-game solving is the open lever.)

*Guarantee / Persistence (free liveness output → constant `o := true`):*

- **reachability** `F o` → cert `reachability_oneshot`.
- **persistence** `F G o` → cert `persistence_latch`.

*Recurrence:*

- **global-recurrence-switch** `G(φ) <-> G F o`, where `φ` is temporal-free and
  output-free (infinite semantics only) → one-bit deterministic-Buchi
  controller; cert `global_recurrence_switch`.
- **response** `G(r -> F g)` (independent, `g` free) → grant controller; cert
  `response_controller`.
- **round-robin** (`GF o_i` ×k + grant mutex) → one-hot finite cycle (the `o_i`
  free outside the block); cert `round_robin_scheduler`.
- **arbiter** (≥2 responses + grant mutex, requests are inputs, grants free) →
  fair round-robin scheduler over the grants; cert `fair_arbiter`.

Reactivity / GR(1) (boolean combinations of recurrence and persistence) is out
of scope — it needs a real game solver, not a syntactic certificate. Anything
not provably sound stays `candidate`; nothing is removed (residual export is the
next milestone). CSNF is the same DIMACS-style line format as GSNF
(`b`/`bc`/`dec`/`nsf`/`srset`/`srreset`/`tog`/`fdresp`/`dbuchi`/`cyc`/`arb`/`one`/`hold`/`resp`/`asg`/`reg`/`cert`/`cl`/`do`/`r`
records).

### Constraint decomposition (`--split`, `tlsfnorm`)

Most specs write several obligations as one conjunctive clause (e.g. `GUARANTEE
{ G(r0->Fg0) && G(r1->Fg1) && G!(g0&&g1); }` is *one* constraint), which
whole-formula matching can't see. The `--split` option (on `tlsfgraph`,
`tlsftemplates`, `tlsfwl`, `tlsfbenchgraph`) decomposes each constraint into its
top-level `&&` conjuncts — distributing `G`/`X` over `&&` along the spine only,
so it is equivalence-preserving and leaves `F`/`U`/… intact. `tlsfnorm` exposes
the same transform as a spec-rewriter:

```sh
tlsfnorm --passes split spec.tlsf      # re-emit with conjunctions split out
tlsfnorm --passes nnf,boolean spec.tlsf
```

`tlsfnorm` applies `split` / `nnf` / `boolean` (= `-s0`) passes per section and
re-emits TLSF; `--format trace` reports the per-pass formula-count changes.
Decomposition is what makes the corpus shape statistics meaningful — see
[`BENCHGRAPH.md`](BENCHGRAPH.md) (e.g. `tlsf-fin` mutex 0 → 230 specs once
split). The remaining `tlsfnorm` passes (`macro`/`response`/`expose-*`) are
reserved and error clearly.

### Residual & composition soundness (`tlsfresidual`, `--check`)

Certification is **per-block and local**; the controllers are **composable**.
`csnf_compose` produces a sound whole-spec decomposition by two means:

- **Substitution** — a combinational output (`o:=θ`, `o:=true`, `o:=⋁guards`) is
  *eliminated from the residual* by rewriting `o` to its value. An output merely
  *read* elsewhere costs nothing; a constraint that forces `o` the other way
  becomes an unrealizable residual (surfaced, not mis-certified).
- **Fair servers** — responses on a shared grant `g` are merged into one
  interleavable server instead of the monopolizing `g:=true`, so requests to one
  resource compose rather than collide. Liveness-owned outputs (servers,
  registers) keep a conservative free-output rule.

```sh
tlsftemplates --check spec.tlsf      # CSNF + a whole-spec composition verdict
tlsfresidual spec.tlsf               # reduced leftover, clustered by output
tlsfresidual --output-dir out/ spec.tlsf   # one residual.<k>.ltl per cluster
tlsfresidual --single spec.tlsf      # the whole residual as one formula
```

`tlsfresidual` substitutes away the solved combinational outputs and emits the
residual over a *smaller* alphabet. It then **clusters** the residual into
independent sub-problems by **shared output** — `E → ⋀ᵢ Gᵢ ≡ ⋀ᵢ (E → Gᵢ)` when
the output sets are disjoint — so a synthesizer makes several small,
parallelisable calls instead of one giant one. The default stream lists
`c clusters N` then, per cluster, `c cluster k outs=… ins=…` and its formula;
`--output-dir` writes one `residual.k.ltl` per cluster, each ready for its own
call: `ltlsynt --ins=… --outs=… -F out/residual.k.ltl`. Pure-input assumptions
are replicated into every cluster's antecedent (sound); the accepted controllers
plus a controller per cluster realise the whole spec.

**Honest caveat (see [`BENCHGRAPH.md`](BENCHGRAPH.md)):** composability is the
*soundness* fix, not a template-coverage fix. Template-only composition now
fully solves 2 SYNTCOMP `tlsf` specs and eliminates only ~0.4–0.6 % of
constraints. With the AbsSynthe safety backend enabled, however,
`tlsfcompose --aiger --ltlsynt /bin/false` currently emits full controllers for
125 / 2545 `tlsf` specs and classifies 7 more as unrealizable. The remaining
gap is dominated by liveness / weak-until / GR(1)-style residuals.

### Decomposed synthesis (`tlsfcompose`)

`tlsfcompose` turns the decomposition into a runnable synthesis plan. In its
default text/output-dir mode it stays self-contained and does not spawn
processes: it emits the certified **combinational controllers** as exact
assignments (`o := θ`), the rest of the spec as independent **residual
clusters** (one LTL job each), and — with `--output-dir` — a generated
**`compose.sh`** that runs `ltlsynt` per cluster:

```sh
tlsfcompose spec.tlsf                      # plan on stdout (controllers + clusters)
tlsfcompose --output-dir out/ spec.tlsf    # controllers.txt, cluster.<k>.ltl, compose.sh
sh out/compose.sh                          # runs ltlsynt per cluster -> overall verdict
tlsfcompose --aiger spec.tlsf > ctrl.aag   # one merged controller circuit
tlsfcompose --aiger --abssynthe external/AbsSynthe/binary/abssynthe \
            --ltlsynt /bin/false spec.tlsf > ctrl.aag
```

`--aiger` closes the loop into a single controller. It encodes certified
controllers directly as and-inverter gates, routes eligible non-finite safety
clusters (`G`/`X`/Boolean, including safety assumptions) to AbsSynthe when
`--abssynthe PATH` or `$ABSSYNTHE` is set, routes anything else to `ltlsynt`,
and **merges** the output-disjoint strategies into one AIGER (`aag`) over the
spec's full interface (`UNREALIZABLE` if any exact residual cluster is
unrealizable). Use `--ltlsynt /bin/false` to assert that no fallback call is
allowed.

The spec is **realizable iff every cluster is** (the combinational controllers
are exact), so the per-cluster `ltlsynt` results compose into a verdict and a
full strategy = the emitted controllers ⊕ one controller per cluster. AbsSynthe
now covers the self-contained safety-game slice; liveness templates
(fair server/arbiter) and GR(1)-style residuals still require a liveness backend
rather than hand-encoded circuits. The `--from-gsnf`/`--from-csnf` line reader
is still reserved.

Generated AIGER controllers can be checked against the original spec with Spot's
Python bindings:

```sh
python3 scripts/verify_aiger_ltl.py --compose build/tlsfcompose \
  --tlsf2ltl build/tlsf2ltl --tlsf spec.tlsf
```

### Corpus statistics (`tlsfbenchgraph`)

`tlsfbenchgraph` runs the whole pipeline over a corpus and emits one TSV row of
form/template-shape metrics per spec (inputs/outputs, syntactic safety/liveness,
per-shape candidate counts, certified/solved blocks, dependent outputs, residual
constraints, largest output component, raw/normalised formula size, and —with
`--wl N`— the WL stabilisation depth), plus an aggregate `--summary`.

```sh
tlsfbenchgraph --input-dir benchmarks/tlsf --summary > tlsf.metrics.tsv
```

Aggregate statistics, plots and insights over the whole SYNTCOMP corpus are in
[`BENCHGRAPH.md`](BENCHGRAPH.md) (regenerated by `scripts/benchgraph_plots.py`).

Over the SYNTCOMP corpus (all specs parse; ~5 s for the 2545 `tlsf` set) the
shape distribution is, e.g.: the real-time `tlsf` set is recurrence-dominated
(`GF` in ~876 specs) with response pervasive once constraints are split (431
specs), while the finite-word `tlsf-fin` set has **no** recurrence/persistence
and is instead **arbitration- and guarded-next-shaped** — mutex (230 specs),
response (141), and guarded-next (292), much of it invisible without `--split`.
Current no-`ltlsynt` AIGER synthesis on the `tlsf` corpus solves 125 specs with
templates+AbsSynthe; template-only full-spec solving is 2.

`tlsfgraph`/`tlsfwl`/`tlsftemplates`/`tlsfbenchgraph`/`tlsfresidual`/
`tlsfcompose` are the implemented slice of a larger
analysis/normalization/synthesis layer. Remaining reserved flags such as
`--norm-depth`, `--from-gsnf`, `--from-csnf`, `--side-conditions sat|bdd`,
`tlsfbenchgraph --jobs/--timeout`, and `--graph formula|quotient` report a clear
"not implemented" error.

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
meson test -C build        # fast regression suite
```

Coverage (uses `gcovr` with the default compiler's matching `gcov`):

```sh
meson setup build-cov -Db_coverage=true
meson test -C build-cov
gcovr --root . --filter 'src/' --exclude '.*tlsf_(lex|parse).*' --print-summary
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
