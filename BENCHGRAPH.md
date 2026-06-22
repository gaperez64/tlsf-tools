# SYNTCOMP selection form / template-shape statistics

> Generated benchmark snapshot. This file records measurements; it is not a
> roadmap. Regenerate it with the benchmark scripts before relying on the
> numbers.

Aggregate structural statistics for the local SYNTCOMP selection directories,
computed with `tlsfbenchgraph` from `build-release-local`:

- **`tlsf`** — `tlsf-selection-2026` (1586 specs).
- **`tlsf-fin`** — `tlsf-fin-selection-2026` (748 specs).

Every selected spec parses, expands, and is analysed. The structural numbers are
syntactic lower bounds: a constraint is counted under a shape only when it
matches that exact recognizer pattern.

Primary structural tables use `--split`, which decomposes top-level conjunctions
so conjoined obligations are visible to the recognizers.

Regenerate structural plots and tables:

```sh
python3 scripts/benchgraph_plots.py \
    --benchgraph build-release-local/tlsfbenchgraph \
    --out docs/benchgraph \
    tlsf-selection-2026:tlsf \
    tlsf-fin-selection-2026:tlsf-fin
```

Regenerate the preprocessor speed/complexity section:

```sh
scripts/benchgraph.py \
    --corpus tlsf-selection-2026 \
    --tlsfcompose build-release-local/tlsfcompose \
    --ltlsynt ltlsynt \
    --baseline-mode tlsf-tools \
    --out BENCHGRAPH.md \
    --data benchgraph_data.tsv \
    --timeout 15 --mem-gb 6
```

---

## Corpus overview (decomposed)

| corpus | specs | parsed | constraints (med/mean/max) | inputs (med) | outputs (med) |
|---|--:|--:|---|--:|--:|
| `tlsf` | 1586 | 1586 | 15 / 40.4 / 5154 | 7 | 3 |
| `tlsf-fin` | 748 | 748 | 13 / 19.0 / 162 | 13 | 35 |

![Constraint-count distribution](docs/benchgraph/constraints_hist.png)

## Template-shape prevalence (decomposed)

| corpus | response | mutex | recurrence | persistence | global_recurrence | guarded_next | definition |
|---|--:|--:|--:|--:|--:|--:|--:|
| `tlsf` | 383 (2419) | 5 (6) | 556 (1090) | 19 (19) | 2 (2) | 36 (106) | 55 (250) |
| `tlsf-fin` | 26 (96) | 46 (104) | 0 (0) | 0 (0) | 0 (0) | 77 (132) | 22 (22) |

_(cells: # specs with the shape, and total candidate count)_

![Template-shape prevalence](docs/benchgraph/shape_prevalence.png)

## Template-solvable coverage (decomposed)

| corpus | solved blocks | certified | specs ≥1 solved | specs fully solved | constraints eliminated | outputs owned |
|---|--:|--:|--:|--:|--:|--:|
| `tlsf` | 231 | 6 | 106 | 1 | 0.2% (126/64136) | 0.9% (88/9377) |
| `tlsf-fin` | 154 | 62 | 45 | 0 | 0.8% (110/14243) | 0.2% (110/61672) |

`constraints eliminated` and `outputs owned` are residual-reduction metrics:
constraints discharged and outputs determined by certified composable blocks.

![Residual reduction](docs/benchgraph/coverage.png)

## Residual complexity (monolith -> residual)

Residual complexity after all template work — per-spec residual = the games the synthesis backends still face (every accepted SOLVED block removed):

![Residual independent games by synthesis class](docs/benchgraph/residual_class.png)

![Hardest game dimensionality: monolith vs residual](docs/benchgraph/residual_gamesize.png)

| corpus | fully solved | specs factoring ≥2 clusters | residual clusters (safety→OxiDD / liveness→ltlsynt) | hardest game outs monolith→residual (mean) | residual size / monolith |
|---|--:|--:|--:|--:|--:|
| `tlsf` | 1 (0%) | 371 (23%) | 1622 (50%) / 1612 (50%) | 5.0→4.9 | 69.4% (3463866/4988001) |
| `tlsf-fin` | 0 (0%) | 241 (32%) | 272 (18%) / 1257 (82%) | 80.8→80.7 | 100.1% (10763580/10750952) |

_(Per-spec class: most specs still carry a liveness cluster, but clustering isolates it — the safety clusters are OxiDD-eligible games; only the liveness clusters need `ltlsynt`. Synthesis cost is ~exponential in a game's outputs, so the hardest-game column is the headline dimensionality number.)_

## Effect of constraint decomposition (`--split`)

Effect of `--split` (specs with the shape: raw → decomposed):

| corpus | constraints (total) | response | mutex | recurrence | persistence | global_recurrence | guarded_next | definition |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| `tlsf` | 14686→64136 | 23→383 | 2→5 | 484→556 | 19→19 | 2→2 | 23→36 | 15→55 |
| `tlsf-fin` | 1036→14243 | 0→26 | 0→46 | 0→0 | 0→0 | 0→0 | 22→77 | 22→22 |

![Decomposition effect](docs/benchgraph/split_effect.png)

## Normalization obstacles before matching

Structural indicators (from `tlsfbenchgraph`, summed over the raw constraint
formulas) of where a Sickert-style normalization would have to fire: `u_under_w`
(`U` under `W`), `limit_under_temporal` (a `GF`/`FG` limit node under a temporal
node), `w_under_gf` (`W` inside a `GF`), and `u_under_fg` (`U` inside an `FG`).
These quantify the obstacle tail that the bounded Sickert passes target; a corpus
with near-zero counts will not benefit from those passes.

## Effect of exact recognition normalization

`scripts/norm_sweep.py` runs the structural/certification pipeline once per
normalization schedule (via `tlsfbenchgraph --pre-normalize` /
`--match-normalize`) and reports, per schedule, the deltas vs the `off`
baseline: extra template candidates, certified/solved blocks, eliminated
constraints, and owned outputs, plus formula growth and a soundness-eligibility
flag (a schedule is **not** eligible if it introduces any new parse failure vs
`off` — e.g. an infinite-word-only pass on a `Finite` spec). Only eligible rows
should be ranked; prefer the smallest eligible schedule on the Pareto frontier
(e.g. `match-safe:1` over `match-safe:2` when the second iteration adds nothing).

```sh
scripts/norm_sweep.py --corpus benchmarks/tlsf \
    --tlsfbenchgraph build-research/tlsfbenchgraph \
    --schedules off match-safe:1 match-safe:2 pre-safe:1+match-safe:1 \
    --out docs/benchgraph/norm_sweep.tsv --markdown docs/benchgraph/norm_sweep.md
```

## Normalisation (formula size under `--strong-simplify`)

![Formula size under strong-simplify](docs/benchgraph/reduction.png)

## Key takeaways

1. The selected `tlsf` corpus remains recurrence-heavy after decomposition: 556
   specs expose recurrence candidates, and 383 expose response candidates.
2. The selected `tlsf-fin` corpus is dominated by guarded-next and mutex-shaped
   structure after decomposition, with no recurrence or persistence candidates.
3. Template-certified blocks solve part of the problem but rarely the whole spec:
   106 selected `tlsf` specs and 45 selected `tlsf-fin` specs have at least one
   solved block, while full structural solve counts are 1 and 0 respectively.
4. Residual clustering is the main decomposition lever: 371 selected `tlsf`
   specs and 241 selected `tlsf-fin` specs factor into two or more residual
   games, with safety clusters isolated for OxiDD.
5. The refreshed preprocessor benchmark below is based on the selected `tlsf`
   corpus and records the per-spec data in `benchgraph_data.tsv`.

## Caveats

- Recognizers are syntactic; shape counts are lower bounds.
- `--split` only distributes over equivalence-preserving top-level conjunctions.
- The speed section compares only OxiDD-contributing specs; baseline `ERROR`
  rows are reported but excluded from both-solved speedup statistics.

<!-- BENCHGRAPH:PREPROCESSOR START (generated by scripts/benchgraph.py) -->
## Preprocessor speed & complexity vs ltlsynt (`scripts/benchgraph.py`)
Is templates+OxiDD a FAST preprocessor? Two metrics: residual **complexity**
(what's left after templates+OxiDD) and **speed** (our full pipeline vs a standalone
`ltlsynt` baseline for the whole spec). Goal: carve off safety with OxiDD, forward
only the hard liveness residual to ltlsynt, and never be slower or less complete.
Regenerate: `scripts/benchgraph.py --corpus DIR --tlsfcompose … --ltlsynt …`
(or `--from-data benchgraph.tsv` to re-render this section without re-running).

### Run: 2026-06-21 15:42 UTC · commit `38c04fd`
- Corpus: `tlsf-selection-2026` (1586 specs)
- Caps: timeout 15s/run, 6 GB RAM/run (systemd cgroup hard cap), sequential
- Baseline: `tlsf2tlsf --basic` + `tlsf2ltl --format ltl` + `ltlsynt -F … --ins … --outs … --aiger`
- Ours: `tlsfcompose --split --aiger --ltlsynt …`
- Per-spec data: `benchgraph_data.tsv`

### Complexity
- **Self-contained (templates+OxiDD, no ltlsynt): 489/1586 = 30.8%** (404 use OxiDD).
- **OxiDD reach (≥1 cluster): 407/1586 = 25.7%**.
- Residual shape (specs not self-contained), hardest cluster:

  | residual class | specs |
  |---|---|
  | liveness (F/U/GF/Buchi) | 944 |
  | GR(2+) generalized reactivity | 60 |
  | W/R safety not yet handled | 50 |
  | (none / unrealizable verdict) | 43 |

### Residual reduction (complexity)
- Specs with ≥1 synthesis cluster: 1461; 2746 clusters total (1692 peeled by OxiDD, 1054 forwarded to ltlsynt).
- **Formula mass OxiDD carves off the residual before ltlsynt: aggregate 32.0%** (residual 1297605/1909224 nodes), median per spec **0.0%**.
- OxiDD peels the **entire** synthesis residual (nothing left for ltlsynt): 407/1461 specs.
- Residual clusters still forwarded to ltlsynt (count → specs): 0→407, 1→1054.

### Speed (OxiDD-contributing specs)
- Timed: 407 specs. Both produced a controller: 89.
- Status breakdown on timed specs: ours SOLVED 215, UNREAL 143, TIMEOUT 49, FAILED 0; baseline SOLVED 89, UNREAL 4, TIMEOUT 1, ERROR 313.
- Baseline ERROR rows are excluded from speedup statistics; they are cases where standalone `ltlsynt` did not produce a verdict for the expanded formula/signals.
- **Both-solved speedup `base/ours`: median ×0.60, geomean ×0.43** (faster: 16, slower: 73).
- Absolute wall on both-solved: **median ours 57 ms vs base 34 ms** (near parity); mean ours 418 ms vs base 140 ms.
- Total wall on both-solved: ours 37.2s vs base 12.5s (**×0.34** aggregate).
- Ours solves where **base times out** (≥15s): 1 clear win.

### Completeness vs ltlsynt
- **ltlsynt produced a controller but we did not: 0** — the honest deficit (we are *less complete* on these). Breakdown: 0 we wrongly call **UNREALIZABLE**, 0 backend **FAILED**, 0 **timed out**.

### Verdict
On the **median** OxiDD-contributing spec where both engines synthesize, tlsf-tools is at **rough parity** (57 ms vs 34 ms). In **aggregate we are ×0.34 slower** than ltlsynt. The genuine value is the **1 spec ltlsynt cannot synthesize in 15s that we do**. The completeness blocker is **0 specs ltlsynt solves that we don't** — now dominated by **0 false-UNREALs** from output-free assumption clusters, not parse bugs.
<!-- BENCHGRAPH:PREPROCESSOR END -->
