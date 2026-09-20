# Stacked Follow-up: Peak Memory and Recommended Caps

This is the follow-up to [PR #28](https://github.com/gaperez64/tlsf-tools/pull/28),
implemented in [PR #29](https://github.com/gaperez64/tlsf-tools/pull/29).
The first PR's original 90-run measurements remain unchanged in
[peak-memory-results.json](peak-memory-results.json). Its PR description now
reports those first-stage peaks, including the absence of a beem improvement.

## What Actually Improved

**At matched 32M-node/4M-cache settings, the follow-up does not materially lower
peak RSS. It lets both drivers finish at 8M nodes, where PR #28 fails.**
Selecting smaller capacities and caches then lowers the memory needed for a
completed solve. These are distinct findings; none involves automatic arena
growth or secretly raising a cap.

The new campaign contains **102 serial runs**, including three repetitions of
the matched settings and each recommended setting. The following comparison
reruns both versions together on the same host/software environment:

| Instance | PR #28 peak MiB, 32M/4M | Follow-up peak MiB, 32M/4M | PR #28 at 8M/4M | Follow-up at 8M/4M |
| --- | ---: | ---: | --- | --- |
| beem c0to1 | 942.371 | 942.434 | ERROR, 3/3 | ERROR, 3/3 |
| beem c0to3 | 942.379 | 942.445 | ERROR, 3/3 | ERROR, 3/3 |
| beem c0to7 | 942.320 | 942.441 | ERROR, 3/3 | ERROR, 3/3 |
| driver_c2y | 623.723 | 623.758 | ERROR, 3/3 | UNREALIZABLE, 3/3 |
| driver_c2n | 647.098 | 647.113 | ERROR, 3/3 | UNREALIZABLE, 3/3 |

The matched-cap peak differences are below 0.02%. At 8M/4M, successful
follow-up driver medians are 391.395 and 424.562 MiB respectively. The latter
varied from 408.711 to 424.566 MiB; do not mistake a failing old run's lower RSS
for a better completed solve. Retrying unsuccessful beem runs adds about one
second at 8M, without making them finish.

At the historical **4M-node/4M-cache default**, all five still return a diagnosed
allocation error. Defaults have not been changed based on these five cases.

## Recommended Settings

These are tested memory-oriented settings for these exact pinned files, not
proven minimal capacities or general defaults. `M` and `K` below mean binary
entry counts, not bytes. Retain **eager** transitions.

| File | Node cap | Cache cap | GC | Peak RSS median [min, max], MiB | Wall median, s |
| --- | ---: | ---: | --- | ---: | ---: |
| beemprdcell2f1_c0to1.aag | 33554432 | 262144 | auto | 867.398 [867.289, 867.430] | 7.94 |
| beemprdcell2f1_c0to3.aag | 33554432 | 262144 | auto | 867.383 [867.242, 867.441] | 7.92 |
| beemprdcell2f1_c0to7.aag | 33554432 | 262144 | auto | 867.414 [867.375, 867.426] | 7.93 |
| driver_c2y.aag | 8388608 | 1048576 | pressure, 80% | 321.848 [321.816, 321.852] | 11.13 |
| driver_c2n.aag | 8388608 | 1048576 | pressure, 80% | 333.773 [333.633, 333.797] | 18.22 |

Every row completed with the expected verdict in all three repetitions. All
three beem controllers were independently proved safe again using AIGER,
combine-aiger and ABC PDR. **All 33 controller artifacts** emitted by the
campaign match those freshly checked controllers by SHA-256. The driver
UNREALIZABLE verdicts agree with the pinned upstream annotations, but are not
independently certified by a counterstrategy; PDR checking a controller cannot
certify a losing game.

Compared with the rerun PR #28 at 32M/4M, these settings reduce completed-run
peaks by approximately **8.0% for beem and 48.4% for both drivers**. The beem
saving is cache tuning, not a demonstrated construction-memory reduction. The
driver saving combines newly viable smaller arenas with cache and GC choices.
There is a time trade-off: the larger 32M/4M auto setting finishes the drivers
in 5.22 and 7.54 seconds, versus 11.13 and 18.22 seconds above.

Without explicit pressure GC, 8M/1M auto also completes both drivers in every
repetition: medians 356.656 MiB / 11.78 s and 333.898 MiB / 19.40 s. Thus pressure
GC is particularly useful for driver_c2y. For beem, its one-run screens save
only about 2.4 MiB while increasing wall time to about 12.3 seconds; use auto.

Example commands, with a diagnostic or release binary:

```sh
tlsfsolve --oxidd-nodes=33554432 --oxidd-cache=262144 --oxidd-gc=auto \
  beemprdcell2f1_c0to1.aag > controller.aag
tlsfsolve --oxidd-nodes=8388608 --oxidd-cache=1048576 \
  --oxidd-gc=pressure --oxidd-gc-threshold=80 driver_c2y.aag
```

The second command legitimately exits 1 and prints UNREALIZABLE. A node cap is
not a process-memory limit; leave headroom beyond these measured RSS values.

## Implemented Work

- Shared relevant-cone/last-use construction counts every operand occurrence
  and root use; redundant map and extraction roots are released and zeroed.
- Pure BDD operations retain their inputs across at most one explicit GC and
  retry. Dependent operations stop at the first failure. Pressure collections
  are throttled by deterministic operation progress and phase changes.
- Operation/phase/first-failure traces, map-reference statistics, approximate
  stored-node samples, effective session capacities and configuration conflicts
  are observable. Diagnostic bundles retain per-child RSS, interrupted
  operations, signals and timeout classification.
- Conversion memo scope is enforced per pinned root. Tests cover GC churn,
  nonzero session bases, injected failures and GR(1) allocation cleanup.
- Exact demand-driven safety transitions and a typed verdict-only API are
  implemented behind explicit options. Used substitutions are immutable.
  Full synthesis still constructs every required controller-memory update.
- A separate commit fails closed on multiple GR(1) fairness assumptions after
  reproducing the handoff's alternating-fairness counterexample. Parser
  preservation is unchanged; composition callers can fall back. This is a
  correctness restriction, not a measured memory improvement.

Demand construction is **not recommended for these five files**. Its screens
do not show a consistent peak reduction over the recommended eager settings;
even verdict-only beem still demands the expensive update cone. It remains
useful for avoiding irrelevant update construction: a deterministic unused-mux
regression exhausts 1024 nodes in eager verdict-only mode, succeeds exactly in
demand verdict-only mode, and correctly reports extraction failure when full
synthesis must materialize the preserved latch update. No verdict-only result
is presented as completed controller synthesis.

Separate diagnostics locate the remaining beem cost: eager construction builds
all 801 gates and observes about 31.26 million stored nodes. The map holds at
most 254 references instead of retaining all 937 input/latch/gate references;
all map references are released before iteration, but the process peak remains
construction-dominated. Demand mode needs only 9 of 110 updates for the fixed
point, yet those nine contain the expensive cone. Building the remaining 101
for emission raises the total gate builds to 873 through repeated sub-cones.
The recommended driver diagnostic runs each make four explicit collections,
with no failed-operation retries. A 4M beem failure identifies construction
gate index 562, `and` operation 1367, and exactly one unsuccessful retry.

## Evidence and Reproduction

- [followup-results.json](followup-results.json): all 102 runs, per-group
  medians/ranges, exact commands, failures, solver/input hashes and build settings.
- [followup-proofs.json](followup-proofs.json): fresh independent proof commands,
  tool/input/controller hashes, and matching-artifact count.
- [followup-diagnostics.json](followup-diagnostics.json): separate phase, root,
  GC, retry and failure evidence. These are diagnostic runs, not release timing
  samples; stored-node samples are not exact live-node or internal peaks.
- [measurement-method.md](measurement-method.md): the original campaign's
  methodology; the same GNU time per-process-tree RSS mechanism is used here.

The matched sources are PR #28 commit `8515c78` and follow-up solver commit
`55c180d`. Both use GCC 15.3.1, release/O3, `b_ndebug=true`, `cpu=x86-64-v2`, one
OxiDD worker, and the identical pinned OxiDD archive. Later commits add tests,
runner handling and reports, not changes to the measured solver algorithm.
All commands have a 120-second timeout, with no imposed physical-memory limit.
No timed solver runs overlap other timed solver runs or builds. Recommended
and matched settings use three repetitions; other option screens use one.

The host rebooted between the first PR's original campaign and this one,
changing Linux 7.1.5 to 7.2.5. Temporary exploratory follow-up data were lost
and are excluded. Both comparison binaries were rebuilt and rerun after the
reboot; the original first-PR measurements remain a separate historical dataset.
The new build, raw output, proof and diagnostic directories are workspace-local
`build-memory-*` directories, so they survive loss of `/tmp`.

For the matched comparison, build those two commits with the options above,
fetch the pinned corpus, and run:

```sh
python3 scripts/measure_tlsfsolve_memory.py \
  --solver pr28=/path/to/pr28/tlsfsolve --solver stacked=/path/to/new/tlsfsolve \
  --corpus /path/to/corpus --out matched-results \
  --nodes 8388608 33554432 --cache 4194304 --repetitions 3
```

For recommendation trials, use one solver, `--cases` with the desired basenames,
and the table's capacities/GC policy. The manifests preserve every invocation.
Keep diagnostic and full-strategy/verdict-only campaigns separate.

Verification: 271/271 release tests; 281/281 diagnostic tests including all ten
offline corpus tests; 154/154 non-OxiDD tests; 896 explicit-state oracle runs;
six diagnostic-runner contracts; eleven external-checker scenarios; fresh PDR
proofs for all three beem controllers; and output-write failure handling.
Valgrind reports no invalid accesses or definite/indirect leaks in the focused
ownership/failure/session tests. Backend thread-local allocations remain
reported as possibly lost/reachable at process exit. Physical-RAM exhaustion,
Rust allocator abort recovery and general multi-fairness GR(1) repair are not
claimed to be solved.
