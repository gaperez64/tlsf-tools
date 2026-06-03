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

| corpus | safety | liveness | solved blocks | certified | specs with a solved block | norm/raw size (med/mean) |
|---|--:|--:|--:|--:|--:|--:|
| `tlsf` | 64305 | 26550 | 291 | 14 | 114 | 1.14 / 1.41 |
| `tlsf-fin` | 26408 | 7944 | 297 | 426 | 81 | 0.99 / 0.91 |

_safety/liveness are **per-constraint** totals (syntactic classification)._

![Template-solvable coverage](docs/benchgraph/coverage.png)

The certified template library now spans the Manna–Pnueli safety–progress
hierarchy ([spot's classes](https://spot.lre.epita.fr/hierarchy.html)): **safety**
(definition / delayed-definition / guarded-next / reaction / mutex),
**guarantee** (`F o`), **persistence** (`FG o`) and **recurrence** (response /
round-robin / arbiter). All but the decoders are gated by a conservative
**free-output** side condition (the target output occurs in no constraint
outside the block), which keeps the constant/scheduler controllers sound.

Decomposition roughly **3.7×'s** the template-solvable `tlsf` specs (31 → 114
have a SOLVED block). On `tlsf-fin` the revealed arbitration now *solves*
(arbiter + response) instead of only certifying mutexes: solved blocks
**129 → 297** (43 → 81 specs), and the absorbed mutexes drop standalone
`mutex_safety` certificates from **655 → 426**.

The `tlsf` solved count is *lower* than a previous run (458) by design:
definition decoders are now required to be **causal** (`θ` has no `X`). A
`G(o <-> X a)` would ask `o` to predict a future input, so it is not a sound
combinational decoder — ≈168 such non-causal "decoders" are now correctly
declined. Every remaining certificate is sound.

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
5. **Structure is shallow** (WL depth ≤6) and **`--strong-simplify` can grow**
   formulas (it normalises, it does not shrink).

## Caveats

- Recognizers are *syntactic*; per-shape numbers are lower bounds even after
  decomposition.
- `--split` distributes `G`/`X` over `&&` only along the spine (never inside
  `F`/`U`/…), so it is equivalence-preserving and does not perturb
  recurrence/persistence counts.
- Side conditions are *sound but conservative*: the free-output check declines
  solvable blocks whose output is merely *read* elsewhere, so solved counts are
  a floor.
- Definition decoders intentionally do **not** require a free output (a decoder
  fixes `o` to its defined value, so reads are fine); a separate constraint that
  *forces* `o` to a different value would still make the pair unrealizable —
  detecting that needs the residual/side-condition solving of a later milestone.
