# OxiDD static variable-order experiments

Measured 20 September 2026 on base
`9c664034da0ba72cc4d857f27dcc8c082f06c903`.

## Decision

Keep `input-first` and the existing `gates` construction plan as defaults. Keep
`state-first`, `fanin-dfs`, and strict custom order files as experimental,
explicit runtime options. They are selected per invocation in any OxiDD-enabled
build and require no variant-specific compile flag or rebuild. For the five
issue-24 games, `fanin-dfs` is a large win: all five complete at a 4M-node
arena, and the final recommended settings reduce median peak RSS by 58.6% to
93.5% relative to matched reruns of the previous case-specific recommendations.
End-to-end median time also falls substantially.

Do not implement conjunction fusion or `guard-first` in this sprint. The static
order pilot already removes the material issue on all five targets. The held-out
campaign is mixed: easy toy cases improve, tiny cases are neutral, but several
AMBA and GenBuf cases remain unsolved and use more time or memory under
`fanin-dfs`. That is not enough evidence for a default change or an automatic
selector.

The quantifier order remains `forall u exists c`, variable identities are
unchanged, and the construction plan remains the existing exact AIG gate plan.

## Reproducibility

The machine, compiler, OxiDD archive, binaries, build commands, and hashes are
in [build-manifest.json](build-manifest.json). The unmodified binary was frozen
before source edits. Release measurements used optimized C and Rust builds,
`b_ndebug=true`, `x86-64-v2`, no sanitizer, no tracing, and one solver process
at a time. The release candidate hash was
`d55a29653e9daf1eaa28ef8d10cacf1cf754805f066dca4d3f02bf2bb4e40294`.
Diagnostic timing is reported separately and is not used as release timing.

The issue-24 input identities are recorded in every campaign manifest. The
held-out set was selected before candidate runs from 12 pinned files in four
other families; its deterministic selection rule, Git blob IDs, SHA-256 hashes,
and expected annotations are in
[heldout-manifest.json](heldout-manifest.json). There was no cgroup or other
externally imposed process limit.

## What changed

`--oxidd-var-order=input-first|state-first|fanin-dfs` is parsed at runtime and
changes BDD levels only. The same executable can run different orders on
successive invocations. It computes a complete local-variable permutation
before projections, cubes, substitutions, or circuit roots exist. `fanin-dfs`
walks objective roots, latch updates, and supported fairness/goal roots in a
stable structural order, stops at input/latch leaves, then appends unseen
variables and auxiliaries by identity.

`--oxidd-order-file PATH` accepts a strict complete `tlsfsolve-order-v1`
permutation of local BDD identities. Nondefault orders are rejected on an
already-active shared manager. `--oxidd-build-plan=gates` is an explicit no-op
control; no other plan value is implemented or advertised.

Diagnostic builds add bounded selected-gate and root-union traversal. Release
builds contain neither the options nor their argument evaluation. The runner
now supports pinned per-variant arguments, custom input manifests, independent
success/failure summaries, checkpointed output, and complete grouping metadata.

## Hotspot diagnosis and fusion decision

The input-first 4M/4M diagnostic reproduces the first allocation failure at
normalized gate 562, AIG lhs literal 1398, operation 1367. Stored nodes rise
from 3,276,801 before the AND to 4,194,319 after its failed retry. One operand
has 19 reachable inner nodes; the other has at least 100,000 and hits the bound.

With `fanin-dfs` and a 4M/256K manager, the same gate is **not structurally
bypassed**. It is still constructed by the unchanged `gates` plan. Its stored
node samples are instead 65,537 before and 196,609 after; its right operand has
93,924 nodes exactly at this checkpoint. The final result traversal reaches the
100,000-node diagnostic bound, while all 111 completed construction roots have
only 5,939 distinct reachable inner nodes in their exact union. This is not a
sum of root sizes.

The offline cone analysis confirms source gate 562 and parser-normalized gate
562 are the same gate for this ASCII input. Literal 1398 has one positive
consumer at gate 565, but its left input, literal 1397, is complemented. Deeper
candidate factors repeatedly encounter `negative_edge` barriers. The proposed
conservative fusion therefore cannot flatten the intended enabling chain
without crossing a forbidden signed boundary. See
[beem-cone-gate562.json](beem-cone-gate562.json).

| instance | diagnostic variant | construction time | fixed-point time | extraction/conversion time | sampled stored-node peak | selected root count | count complete? | elided conjunction nodes | GC/retry | first failure |
|---|---|---:|---:|---:|---:|---:|---|---:|---|---|
| beem c0to1 | input-first, 4M/4M | 1.302 s | n/a | n/a | 4,194,319 | n/a | selected right >=100,000, no | 0 | 1/1 | AND gate 562, op 1367 |
| beem c0to1 | fanin-dfs, 4M/256K | 0.304 s | 0.000048 s | 0.001764 s | 1,507,329 | 111 | root union 5,939, yes; selected result >=100,000, no | 0 | 0/0 | none |

Thus the diagnosed intermediate was made tractable by BDD variable order, not
removed by fusion. B2 (`fused-original` and `guard-first`) was deliberately not
implemented or measured. It would add a substantial ownership/planning surface,
would not pass the conservative barrier at the reported edge, and is no longer
needed to meet the low-memory target. All measured gains below are attributable
to variable order; none are credited to fusion or guard priority.

## Issue-24 results

The one-run B1 screen used 32M nodes, 4M cache, and automatic GC. `state-first`
reduced the three beem cases from about 965,000 KiB and 8.6 seconds to
727,492-732,592 KiB and 4.70-4.80 seconds, but regressed driver c2y from
638,532 KiB/5.43 seconds to 895,956 KiB/8.06 seconds and driver c2n from
662,740 KiB/7.88 seconds to 1,144,616 KiB/18.11 seconds. In the same screen,
`fanin-dfs` used 134,400-134,604 KiB and 0.32 seconds on beem, 178,428 KiB and
0.75 seconds on c2y, and 202,864 KiB and 1.37 seconds on c2n. Only `fanin-dfs`
advanced to repeated measurements.

### Matched settings

This table reruns the former case-specific settings on this host. Times are
wall-clock seconds and RSS is KiB. Every row is full synthesis with eager
transitions. Ranges are `[min,max]` over three serial repetitions.

| instance | variant | order | plan | nodes | cache | GC | mode | completed/attempted | verdict | wall median [min,max] | peak RSS median [min,max] | validation |
|---|---|---|---|---:|---:|---|---|---:|---|---|---|---|
| beem c0to1 | original | input-first | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 8.42 [8.01,8.43] | 888,180 [888,100,888,316] | matched baseline |
| beem c0to1 | no-op control | input-first | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 7.99 [7.97,8.10] | 888,132 [887,888,888,264] | verdict agreement |
| beem c0to1 | candidate | fanin-dfs | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 0.26 [0.26,0.28] | 57,740 [57,660,57,856] | controller separately proved at final cap |
| beem c0to3 | original | input-first | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 8.61 [8.00,8.83] | 888,016 [887,880,888,200] | matched baseline |
| beem c0to3 | no-op control | input-first | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 8.53 [8.00,8.94] | 888,252 [888,116,888,272] | verdict agreement |
| beem c0to3 | candidate | fanin-dfs | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 0.26 [0.26,0.29] | 57,740 [57,732,57,744] | controller separately proved at final cap |
| beem c0to7 | original | input-first | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 8.62 [7.92,8.93] | 888,196 [888,060,888,200] | matched baseline |
| beem c0to7 | no-op control | input-first | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 8.82 [8.06,8.94] | 888,128 [887,996,888,208] | verdict agreement |
| beem c0to7 | candidate | fanin-dfs | gates | 32M | 256K | auto | full | 3/3 | REALIZABLE | 0.29 [0.26,0.35] | 57,820 [57,740,57,848] | controller separately proved at final cap |
| driver c2y | original | input-first | gates | 8M | 1M | pressure | full | 3/3 | UNREALIZABLE | 11.94 [11.82,12.44] | 329,516 [329,428,329,568] | expected annotation + baseline agreement |
| driver c2y | no-op control | input-first | gates | 8M | 1M | pressure | full | 3/3 | UNREALIZABLE | 12.42 [11.75,15.04] | 329,456 [329,304,329,580] | expected annotation + baseline agreement |
| driver c2y | candidate | fanin-dfs | gates | 8M | 1M | pressure | full | 3/3 | UNREALIZABLE | 0.96 [0.81,1.76] | 116,992 [116,948,117,040] | expected annotation + baseline agreement |
| driver c2n | original | input-first | gates | 8M | 1M | pressure | full | 3/3 | UNREALIZABLE | 22.65 [19.47,25.86] | 341,652 [341,616,341,696] | expected annotation + baseline agreement |
| driver c2n | no-op control | input-first | gates | 8M | 1M | pressure | full | 3/3 | UNREALIZABLE | 21.42 [20.03,22.15] | 341,596 [340,148,341,604] | expected annotation + baseline agreement |
| driver c2n | candidate | fanin-dfs | gates | 8M | 1M | pressure | full | 3/3 | UNREALIZABLE | 1.80 [1.46,2.15] | 141,568 [141,544,141,572] | expected annotation + baseline agreement |

The no-op control tracks the frozen binary closely in RSS and has the same
verdicts. It gives no evidence that CLI plumbing, the explicit `gates` value, or
the surrounding refactor explains the candidate gain.

### Capacity frontier and final settings

At cache 4M and automatic GC, original/control fail all three repetitions on
all three beem cases at 4M, 8M, and 16M nodes, then complete at 32M. They fail
both drivers at 4M and complete at 8M and above. `fanin-dfs` completes every
one of its 60 runs across all five games and all four node capacities. This is
a tested sufficient frontier, not a proof of the minimum viable arena.

At 4M nodes, lowering cache from 4M to 256K reduces candidate RSS to about
56.3 MiB for beem, 99.3 MiB for driver c2y, and 134.7 MiB for driver c2n in the
one-run screen. A 1M cache gives about 71.3, 114.1, and 150.0 MiB respectively.
At 8M nodes/1M cache, the drivers improve to about 114.2 and 138.0 MiB.
Pressure GC has essentially the same RSS as auto there and is slightly slower,
so the final recommendation uses auto. Three-repetition demand and verdict-only
checks at 4M/1M are similar to eager full synthesis; extraction is not the
dominant cost.

Final tested recommendations on this host are:

| instance | variant | order | plan | nodes | cache | GC | mode | completed/attempted | verdict | wall median [min,max] | peak RSS median [min,max] | validation |
|---|---|---|---|---:|---:|---|---|---:|---|---|---|---|
| beem c0to1 | candidate | fanin-dfs | gates | 4M | 256K | auto | full | 3/3 | REALIZABLE | 0.28 [0.28,0.38] | 57,868 [57,796,57,868] | SAFE, AIGER + combine-aiger + ABC PDR |
| beem c0to3 | candidate | fanin-dfs | gates | 4M | 256K | auto | full | 3/3 | REALIZABLE | 0.29 [0.28,0.30] | 57,808 [57,792,57,912] | SAFE, AIGER + combine-aiger + ABC PDR |
| beem c0to7 | candidate | fanin-dfs | gates | 4M | 256K | auto | full | 3/3 | REALIZABLE | 0.28 [0.28,0.29] | 57,808 [57,792,57,860] | SAFE, AIGER + combine-aiger + ABC PDR |
| driver c2y | candidate | fanin-dfs | gates | 8M | 1M | auto | full | 3/3 | UNREALIZABLE | 0.81 [0.80,0.84] | 117,036 [116,952,117,040] | expected annotation + independent implementation agreement only |
| driver c2n | candidate | fanin-dfs | gates | 8M | 1M | auto | full | 3/3 | UNREALIZABLE | 1.47 [1.47,1.54] | 141,488 [141,460,141,552] | expected annotation + independent implementation agreement only |

The comparison below includes both the order change and the smaller final arena
or auto-GC choice. Equal-setting rows above isolate the order effect.

| instance | original tested sufficient setting | candidate setting | completed-run RSS ratio | end-to-end time ratio | proof status |
|---|---|---|---:|---:|---|
| beem c0to1 | 32M/256K/auto/input-first | 4M/256K/auto/fanin-dfs | 0.065 | 0.033 | SAFE |
| beem c0to3 | 32M/256K/auto/input-first | 4M/256K/auto/fanin-dfs | 0.065 | 0.034 | SAFE |
| beem c0to7 | 32M/256K/auto/input-first | 4M/256K/auto/fanin-dfs | 0.065 | 0.032 | SAFE |
| driver c2y | 8M/1M/pressure/input-first | 8M/1M/auto/fanin-dfs | 0.355 | 0.068 | verdict agreement, not counterstrategy-certified |
| driver c2n | 8M/1M/pressure/input-first | 8M/1M/auto/fanin-dfs | 0.414 | 0.065 | verdict agreement, not counterstrategy-certified |

The independently proved controllers have AAG headers:

| instance | inputs | latches | outputs | ANDs | proof |
|---|---:|---:|---:|---:|---|
| beem c0to1 | 24 | 110 | 2 | 14,980 | SAFE |
| beem c0to3 | 22 | 110 | 4 | 15,002 | SAFE |
| beem c0to7 | 18 | 110 | 8 | 15,194 | SAFE |

The checker validates and normalizes both circuits with Armin Biere's AIGER
utilities, connects the strategy with `combine-aiger`, and proves the one-bad
closed loop with ABC PDR. Result files include exact game, controller, closed
loop, and tool hashes. Losing driver verdicts agree across the original and
candidate implementations and with pinned benchmark annotations, but no
independent counterstrategy proof was produced; they are not called certified.

## Held-out results

The held-out campaign uses 8M nodes, 1M cache, auto GC, eager full synthesis,
and a 60-second timeout. It is a one-run generalization screen, not a timing
benchmark. `error` means the solver reported capacity/allocation failure.

| instance | original status, RSS/time | fanin-dfs status, RSS/time | result |
|---|---|---|---|
| AMBA amba10b10n | error, 271.9 MiB/2.28 s | error, 286.4 MiB/3.43 s | both unsolved; candidate worse |
| AMBA amba10b4unrealn | error, 271.9 MiB/2.29 s | error, 286.4 MiB/3.40 s | both unsolved; candidate worse |
| AMBA amba16b50n | error, 273.9 MiB/2.99 s | error, 325.2 MiB/16.09 s | both unsolved; candidate worse |
| GenBuf genbuf10b4n | timeout, 291.6 MiB/60.01 s | error, 361.6 MiB/34.53 s | both unsolved; failure mode changed |
| GenBuf genbuf10b3unrealn | timeout, 291.5 MiB/60.02 s | error, 361.7 MiB/32.15 s | both unsolved; failure mode changed |
| GenBuf genbuf32c40n | error, 300.9 MiB/2.94 s | timeout, 339.2 MiB/60.02 s | both unsolved; candidate worse |
| toy add10y | REALIZABLE, 31.2 MiB/0.70 s | REALIZABLE, 26.0 MiB/0.03 s | improved |
| toy add10n | REALIZABLE, 31.6 MiB/0.69 s | REALIZABLE, 29.3 MiB/0.05 s | improved |
| toy bs512y | REALIZABLE, 104.6 MiB/1.30 s | REALIZABLE, 74.8 MiB/0.84 s | improved |
| LTL2AIG demo-v10 REAL | REALIZABLE, 23.7 MiB/0.00 s | REALIZABLE, 23.5 MiB/0.01 s | neutral |
| LTL2AIG demo-v11 UNREAL | UNREALIZABLE, 23.6 MiB/0.00 s | UNREALIZABLE, 23.6 MiB/0.01 s | neutral |
| LTL2AIG load_full REAL | timeout, 167.7 MiB/60.01 s | timeout, 168.0 MiB/60.01 s | neutral, unsolved |

No candidate lost a case completed by the baseline, and all cases completed by
both orders have matching verdicts. However, unsolved AMBA/GenBuf cases show
material regressions in RSS, elapsed time, or failure mode. These negative
results are why `fanin-dfs` remains opt-in.

The first held-out run initially labeled `add10n` UNREALIZABLE from its `n`
suffix and stopped on the candidate's REALIZABLE result. That label was a
manifest error: legacy toy `n`/`y` suffixes are encodings, not verdicts. The
selection manifest was corrected to use no expected annotation for those toy
files, and part 2 reran both variants. The initial `SEMANTIC_MISMATCH` record is
retained in raw part-1 evidence for auditability and is not counted as a solver
failure or correctness change.

## Semantic and regression validation

The explicit-state oracle covers all three named orders plus a custom order,
automatic and pressure GC, eager and demand transitions, and full and
verdict-only modes. It completed 3,584 independent closed-loop checks. Unit
tests cover complete permutations, invalid custom files, empty games,
nonidentity manager mappings, shared-session rejection, and order-independent
game semantics. The runner and offline cone analyzer have standalone tests.

The implementation preserves existing GR(1) restrictions and applies complete
orders including auxiliary variables. Release and non-`NDEBUG` builds, the
dependency-free build, and sanitizer coverage are part of the final branch
verification recorded in the pull request.

## Commands and evidence

Every raw JSONL record contains the exact solver argv. Each campaign manifest
contains binary/input/runner hashes and all grouping settings. The principal
commands executed from the repository root were:

```sh
python3 scripts/measure_tlsfsolve_memory.py \
  --variant-config "$PWD/experiments/oxidd-ordering/screen-variants.json" \
  --corpus build-memory-corpus --out build-ordering-screen-b1 \
  --nodes 33554432 --cache 4194304 --gc auto --repetitions 1

python3 scripts/measure_tlsfsolve_memory.py \
  --variant-config "$PWD/experiments/oxidd-ordering/fanin-probe-variant.json" \
  --corpus build-memory-corpus --out build-ordering-probe-4m \
  --nodes 4194304 --cache 4194304 --gc auto --repetitions 1

python3 scripts/measure_tlsfsolve_memory.py \
  --variant-config "$PWD/experiments/oxidd-ordering/finalist-variants.json" \
  --corpus build-memory-corpus --out build-ordering-finalists \
  --nodes 4194304 8388608 16777216 33554432 \
  --cache 4194304 --gc auto --repetitions 3

python3 scripts/measure_tlsfsolve_memory.py \
  --variant-config "$PWD/experiments/oxidd-ordering/heldout-variants.json" \
  --input-manifest "$PWD/experiments/oxidd-ordering/heldout-manifest.json" \
  --corpus build-ordering-heldout --out build-ordering-heldout \
  --nodes 8388608 --cache 1048576 --gc auto \
  --timeout 60 --repetitions 1
```

Cache, GC, transition, verdict, matched-setting, and recommended-setting runs
used the same runner with the settings in their committed manifests. Diagnostic
argv is preserved verbatim in the two diagnostic manifests. Independent proof
commands and tool hashes are preserved in `proof-beem-*.json`.

The [evidence](evidence) directory contains the raw JSONL journals, summaries,
campaign manifests, bounded traces, and proof results. Unsuccessful samples are
reported separately and never averaged into completed-run RSS or time.
