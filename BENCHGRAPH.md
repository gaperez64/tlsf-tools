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
    --out docs/benchgraph --wl 6 \
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

## Weisfeiler-Lehman stabilisation depth (decomposed)

| corpus | WL stabilisation depth (med/mean/max) |
|---|---|
| `tlsf` | 2 / 2.6 / 6 |
| `tlsf-fin` | 3 / 3.0 / 6 |

![WL stabilisation depth](docs/benchgraph/wl_stab.png)

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
## ltlsynt vs preprocessor + ltlsynt (`scripts/benchgraph.py`)
Head-to-head synthesis: standalone **ltlsynt** vs the **preprocessor** (templates + OxiDD + `--split` decomposition) that carves off safety/GR(1) in-process and forwards the residual to ltlsynt. Each (engine, spec) pair gets the same timeout. Regenerate with `scripts/benchgraph.py` (or `--from-data benchgraph.tsv` to re-render).

### Run: 2026-06-24 21:58 UTC · commit `52a7980`
- Corpus `../benchmarks/tlsf` (2545 specs); timeout **30s**, 6 GB/run (systemd cgroup hard cap), sequential.
- ltlsynt: `ltlsynt --tlsf=SPEC --aiger` (syfco translation, full synthesis)
- preprocessor + ltlsynt: `tlsfcompose --split --aiger --ltlsynt …`
- Self-contained without ltlsynt (templates+OxiDD): **419/2545 = 16.5%**.

### Solved within timeout
| engine | solved | only this engine |
|---|--:|--:|
| ltlsynt | 1970/2545 | 59 |
| preprocessor + ltlsynt | 1932/2545 | 21 |

- Both: 1911; neither: 554. **Net gain from the preprocessor: -38** (21 won, 59 lost).
- Preprocessor-only solves by family: selection-ltl-2025×13, generated_TLSF×5, sweap×2, specs×1.

### Speed (both produced a controller)
- 903 specs both SOLVED. **Speedup `ltlsynt/preproc`: median ×0.95, geomean ×0.87** (faster 388, slower 515); aggregate wall ×1.12.

![Survival: ltlsynt vs preprocessor + ltlsynt](docs/benchgraph/survival.png)

- Correctness check (ltlsynt authoritative): 0 false-UNREAL, 20 false-REAL from the preprocessor.
<!-- BENCHGRAPH:PREPROCESSOR END -->
