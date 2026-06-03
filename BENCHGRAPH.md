# SYNTCOMP form / template-shape statistics

Aggregate structural statistics of the [SYNTCOMP](https://github.com/SYNTCOMP/benchmarks)
benchmark corpus, computed with `tlsfbenchgraph`. Two sets:

- **`tlsf`** — real-time / infinite-word benchmarks (2545 specs).
- **`tlsf-fin`** — finite-word (LTLf) benchmarks (2487 specs).

Every spec in both sets parses, expands and is analysed (0 failures). Numbers
come from the synthesis-graph layer (`tlsfgraph` cover + recognizers,
`tlsftemplates` certification, `tlsfwl` WL refinement). They are *syntactic* —
a constraint is counted under a shape only if it matches that shape's exact
pattern, so per-shape counts are **lower bounds**.

**Primary tables use `--split`** (constraint decomposition): each section
formula is split into its top-level `&&` conjuncts (distributing `G`/`X` over
`&&` along the spine — equivalence-preserving), so structure conjoined into one
clause is visible to the recognizers. A dedicated section below quantifies the
effect of decomposition (it is large).

Regenerate everything (plots + the tables below):

```sh
ninja -C build
python3 scripts/benchgraph_plots.py \
    --benchgraph build/tlsfbenchgraph --out docs/benchgraph --wl 6 \
    /path/to/benchmarks/tlsf:tlsf \
    /path/to/benchmarks/tlsf-fin:tlsf-fin
```

(The script needs `matplotlib`; it runs `tlsfbenchgraph` itself — once per
corpus *with* and *without* `--split` — writes the PNGs under
`docs/benchgraph/`, and prints these markdown tables. TSVs go to a temp dir and
are discarded.)

---

## Corpus overview (decomposed)

| corpus | specs | parsed | constraints (med/mean/max) | inputs (med) | outputs (med) |
|---|--:|--:|---|--:|--:|
| `tlsf` | 2545 | 2545 | 13 / 35.7 / 5154 | 8 | 3 |
| `tlsf-fin` | 2487 | 2487 | 7 / 13.8 / 162 | 12 | 10 |

![Constraint-count distribution](docs/benchgraph/constraints_hist.png)

`tlsf` has a small-but-long-tailed size profile; `tlsf-fin` specs are written as
one or a few large conjunctive formulas (see the decomposition blow-up below).

## Template-shape prevalence (decomposed)

| corpus | response | mutex | recurrence | persistence | guarded_next | definition |
|---|--:|--:|--:|--:|--:|--:|
| `tlsf` | 431 (2551) | 12 (14) | 876 (1882) | 46 (54) | 48 (129) | 92 (331) |
| `tlsf-fin` | 141 (544) | 230 (655) | 0 (0) | 0 (0) | 43 (86) | 43 (43) |

_Cells: number of specs exhibiting the shape, and (total candidate count)._

![Template-shape prevalence](docs/benchgraph/shape_prevalence.png)

- **`tlsf` is recurrence-dominated** — a `GF` recurrence in **876 / 2545 (≈34 %)**
  specs — but once conjunctions are split, **response** is the second most
  common shape (431 specs), and **definition** (92) and **guarded-next** (48)
  are non-trivial.
- **`tlsf-fin` still has no recurrence/persistence** (`GF`/`FG` are meaningless
  on finite traces) but, after decomposition, it is clearly **arbitration-
  shaped**: **mutex in 230 specs and response in 141** — both completely
  invisible without splitting (see next section).

## Safety / liveness and template-solvable coverage (decomposed)

| corpus | solved blocks | certified | specs ≥1 solved | specs fully solved | constraints eliminated | outputs owned |
|---|--:|--:|--:|--:|--:|--:|
| `tlsf` | 443 | 14 | 147 | 0 | 0.4 % (326/90855) | 2.2 % (316/14463) |
| `tlsf-fin` | 305 | 426 | 89 | 0 | 0.6 % (219/34352) | 0.2 % (219/132149) |

_"constraints eliminated" / "outputs owned" are the **residual reduction**:
constraints discharged and outputs determined by a sound composable controller
(`tlsfresidual` / `tlsftemplates --check`)._

![Residual reduction](docs/benchgraph/coverage.png)

The certified template library spans the Manna–Pnueli safety–progress hierarchy
([spot's classes](https://spot.lre.epita.fr/hierarchy.html)): **safety**
(definition / delayed-definition / guarded-next / reaction / mutex),
**guarantee** (`F o`), **persistence** (`FG o`) and **recurrence** (response /
round-robin / arbiter). The controllers are now **composable**: combinational
decoders (`o:=θ`, `o:=true`, `o:=⋁guards`) are *eliminated from the residual by
substitution*, and responses on a shared grant are merged into one **fair
server** rather than the monopolizing `o:=true`.

## Composable certification & residual reduction (`tlsfresidual`)

Each block is certified *locally*; "specs with ≥1 solved block" (147 / 89) is a
floor, not a solved-spec count. The real measure is how much of the problem a
**sound whole-spec decomposition** removes before handing off to a synthesizer:

| corpus | fully solved | constraints eliminated | outputs owned | specs with a residual conflict |
|---|--:|--:|--:|--:|
| `tlsf` | **0** | 0.4 % | 2.2 % | 48 |
| `tlsf-fin` | **0** | 0.6 % | 0.2 % | 43 |

Two honest findings:

1. **Composability was the soundness fix, not a coverage fix.** Substitution
   eliminates every combinational decoder *exactly* (an output merely *read*
   elsewhere is rewritten, not ejected), and fair-server merging turns
   same-resource requests into one block instead of a self-collision. This
   removed the M6a ejection pathology — `tlsf` composition conflicts dropped
   **113 → 48**, and those that remain are *genuine* (decoder cycles, real value
   clashes such as `G(o<->a) ∧ G!o`, which surface as an unrealizable residual).
2. **But the headline barely moves: ~0.4–0.6 % of constraints are eliminated and
   no spec is fully solved.** Real specs are dominated by plain safety
   constraints no template matches, plus `ASSUME` assumptions that always belong
   to the residual. Templates discharge the few cleanly decoupled obligations
   (mostly definitions); the bulk (~99 %) is the residual.

So the answer to "what raises the statistics" is: **composition was necessary
but not sufficient** — the ceiling is now template-library *breadth* and genuine
safety/liveness solving, not the controllers' composability. `tlsfresidual`
hands the (still large) residual to `ltlsynt`/`strix`; broadening the library or
solving safety sub-games is the lever for the next milestone.

## Effect of constraint decomposition (`--split`)

| corpus | constraints (total) | response | mutex | recurrence | persistence | guarded_next | definition |
|---|--:|--:|--:|--:|--:|--:|--:|
| `tlsf` | 33513 → 90855 | 44→431 | 4→12 | 796→876 | 46→46 | 30→48 | 16→92 |
| `tlsf-fin` | 3051 → 34352 | 0→141 | 0→230 | 0→0 | 0→0 | 43→43 | 43→43 |

_(specs exhibiting the shape: raw → decomposed)_

![Decomposition effect](docs/benchgraph/split_effect.png)

This is the headline: most specs write several obligations as **one conjunctive
clause**, so whole-formula matching badly under-counts structure. Splitting
(equivalence-preserving) multiplies the visible constraints (tlsf ≈2.7×,
tlsf-fin ≈11×) and uncovers shapes that were entirely hidden —
**`tlsf-fin` mutex 0 → 230, response 0 → 141**; **`tlsf` response 44 → 431**.
Counts that don't reference `&&`-conjoined siblings (recurrence, persistence)
are essentially unchanged, as expected.

## Weisfeiler-Lehman stabilisation depth (decomposed)

| corpus | WL stabilisation depth (med/mean/max) |
|---|---|
| `tlsf` | 3 / 2.7 / 6 |
| `tlsf-fin` | 3 / 3.0 / 6 |

![WL stabilisation depth](docs/benchgraph/wl_stab.png)

Even decomposed, the graphs are **shallow**: WL refinement reaches a fixed point
in a median of 3 rounds (≤6 anywhere), so low-depth fingerprints suffice for
clustering/retrieval.

## Normalisation (formula size under `--strong-simplify`)

![Formula size under strong-simplify](docs/benchgraph/reduction.png)

`--strong-simplify` is a *normal form*, not a minimiser (it eliminates `W`/`R`
and applies NNF): on `tlsf` it tends to grow formulas (median ×1.14), on
`tlsf-fin` it is roughly neutral (median ×0.99).

---

## Key takeaways

1. **Most obligations are conjoined into one clause.** Whole-formula matching
   under-counts; decomposition multiplies visible constraints (≈2.7× / ≈11×)
   and is what makes the shape statistics meaningful.
2. **`tlsf` is recurrence-dominated** (~34 % of specs) with responses pervasive
   once split (431 specs).
3. **`tlsf-fin` is arbitration-shaped, hidden in single formulas** — mutex
   (230) and response (141) only appear after `--split`; no recurrence at all.
4. **Decomposition ~3.7×'s template-solvable `tlsf` coverage** (31 → 114 specs);
   the expanded library (free-liveness, reaction, delayed-def, fair arbiter)
   *solves* `tlsf-fin` arbitration (129 → 297 blocks, 43 → 81 specs).
5. **Composable certification is sound but coverage-bound.** Substitution
   eliminates combinational decoders exactly and fair servers merge shared
   requests, removing the old ejection pathology (`tlsf` conflicts 113 → 48).
   Yet **no spec is fully solved** and only **~0.4–0.6 % of constraints** are
   eliminated — real specs are dominated by non-template safety constraints and
   `ASSUME` assumptions. Composition was the soundness fix; **template breadth /
   sub-game solving** is the lever for coverage. The residual goes to a real
   synthesizer (`tlsfresidual`).
6. **Structure is shallow** (WL depth ≤6) and **`--strong-simplify` can grow**
   formulas (it normalises, it does not shrink).

## Caveats

- Recognizers are *syntactic*; per-shape numbers are lower bounds even after
  decomposition.
- `--split` distributes `G`/`X` over `&&` only along the spine (never inside
  `F`/`U`/…), so it is equivalence-preserving and does not perturb
  recurrence/persistence counts.
- Combinational outputs (definition/reaction/reachability/persistence) are
  **eliminated by substitution** (`o:=value` rewritten into the residual), so an
  output merely *read* elsewhere costs nothing; a constraint that genuinely
  *forces* `o` the other way becomes an unrealizable residual (surfaced, not
  mis-certified).
- Liveness-owned outputs (fair servers, registers) have no closed form, so they
  keep a conservative **free-output** rule: they reduce the residual only when
  the output is otherwise unreferenced. This is where coverage is left on the
  table — a shared grant read by other constraints stays in the residual.
