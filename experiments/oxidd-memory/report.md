# OxiDD Memory Diagnostics Report

Base branch: `origin/main` on 2026-09-19.

Issue addressed: [#24](https://github.com/gaperez64/tlsf-tools/issues/24),
opened by Sebastian Junges, reporting OxiDD solver failures around the fixed
node budget.  Sebastian's follow-up names these SYNTCOMP benchmark instances:

| Instance | Profile expectation | Status at `--oxidd-nodes 33554432 --oxidd-cache 4194304` |
| --- | --- | --- |
| `HWMCC12/beemprdcell2f1_c0to1.aag` | `legacy-safety` | REALIZABLE, strategy stdout 54,243 bytes |
| `HWMCC12/beemprdcell2f1_c0to3.aag` | `legacy-safety` | REALIZABLE, strategy stdout 54,363 bytes |
| `HWMCC12/beemprdcell2f1_c0to7.aag` | `legacy-safety` | REALIZABLE, strategy stdout 62,175 bytes |
| `driver/driver_c2y.aag` | `legacy-safety` | UNREALIZABLE |
| `driver/driver_c2n.aag` | `legacy-safety` | UNREALIZABLE |

The repository now includes `scripts/fetch_syntcomp_issue24.py` to fetch those
files from the pinned SYNTCOMP commit and verify their Git blob IDs without
vendoring uncertain third-party benchmark data.

Implementation components (not separately benchmarked):

| Label | Contents |
| --- | --- |
| Input correctness | Property-preserving AIGER 1.9 parser, profile resolver, positional legacy output 0, exact `controllable_` ownership, reset rejection for unsupported uninitialised latches. |
| Capacity and collection controls | `--oxidd-nodes`, `--oxidd-cache`, `--oxidd-gc`, and `--oxidd-gc-threshold`. |
| Memory-oriented changes | Construction-root release, per-root conversion memo scopes, allocation-free BDD identity, and fused safety/GR(1) CPre conjunction-exists. |
| Diagnostics | Non-`NDEBUG` `--verbose` trace and `scripts/diagnose_tlsfsolve.py` bundle. |

Sanity measurements in this PR used the release OxiDD build
`build-release-local/tlsfsolve` after fetching the pinned corpus into `/tmp`
with `scripts/fetch_syntcomp_issue24.py`.  The fetcher verified every expected
Git blob ID.  At `--oxidd-nodes 8388608 --oxidd-cache 4194304`, all five cases
still returned diagnosed OxiDD solver failure.  At
`--oxidd-nodes 16777216 --oxidd-cache 4194304`, both driver cases returned the
expected UNREALIZABLE verdict and the three `beemprdcell2f1` cases still failed.
At `--oxidd-nodes 33554432 --oxidd-cache 4194304`, all five reached the status
listed above within a 120-second per-case timeout.

Those initial runs were functional sanity checks. The following controlled
campaign adds process peak-RSS and whole-run time measurements.

## What the Memory Results Establish

On 2026-09-19 we ran 90 serial measurements: five cases, two variants, three
node capacities (8M, 16M, 32M), and three repetitions. Cache capacity was fixed
at 4M and GC at `auto`. Both release builds used GCC 15.3.1, identical settings,
and the same pinned OxiDD static library. GNU time recorded process peak RSS
in KiB. The timeout was 120 seconds per run; no run timed out.

The corrected eager baseline disables four changes together: early construction
root release, fused CPre, allocation-free convergence, and early losing-state
exit. It retains all input and conversion correctness repairs. This measures
their combined effect, not each optimization separately; pressure GC and the
correctness-mandated conversion changes are not isolated. See
[the method and reproduction commands](measurement-method.md), the
[exact baseline patch](corrected-eager-baseline.patch), and
[all measurements/build fingerprints](peak-memory-results.json).

At **32M nodes / 4M cache**, both variants completed every case in all three
repetitions. Values below are medians; RSS uses MiB (1024 KiB):

| Instance | Baseline peak RSS | PR peak RSS | RSS change | Baseline time | PR time |
| --- | ---: | ---: | ---: | ---: | ---: |
| `beemprdcell2f1_c0to1.aag` | 942.21 | 942.27 | +0.006% | 8.67 s | 8.66 s |
| `beemprdcell2f1_c0to3.aag` | 942.18 | 942.26 | +0.008% | 8.66 s | 8.58 s |
| `beemprdcell2f1_c0to7.aag` | 942.27 | 942.25 | -0.001% | 8.64 s | 8.59 s |
| `driver_c2y.aag` | 789.07 | 623.39 | **-21.0%** | 9.03 s | 5.28 s |
| `driver_c2n.aag` | 934.88 | 647.03 | **-30.8%** | 11.60 s | 7.53 s |

Across the three repetitions, each row/variant's peak-RSS range was under
0.4 MiB; all ranges and individual runs are in the data file. There is a clear
peak-memory reduction for the driver cases and no meaningful reduction for the
three beem cases. The driver results also improve at a fixed lower capacity:

| Node/cache cap | Corrected eager baseline | PR solver |
| --- | --- | --- |
| 8M / 4M | All five fail | All five fail |
| 16M / 4M | All five fail | Both drivers return UNREALIZABLE; three beem cases fail |
| 32M / 4M | All five complete | All five complete |

These outcomes held in every repetition. The current changes therefore help
the driver cases beyond merely accepting larger caps. Completion of the beem
cases still depends on the larger tested cap. Among the tested settings, this
PR uses 16M nodes / 4M cache for the drivers and 32M / 4M for the beem cases;
these are tested sufficient settings, not exact minimum capacities. Defaults
remain unchanged and the arenas do not dynamically grow.

All 18 emitted strategies were byte-identical to the respective previously
model-checked controllers. Both builds passed six focused parser/profile/solver
tests before measurement. The driver verdicts remain independently uncertified.
This campaign does not identify the peak's phase, measure peak live/stored BDD
nodes, or establish effects on GR(1) or a broader corpus.

## Remaining Handoff Work

This PR does not yet complete the handoff. In particular, these optimizations
are still absent or incomplete:

| Handoff item | Requirement | Current state |
| --- | --- | --- |
| Relevant-cone construction and last-use release, section 8.2 | Required | Both solvers still build all gates and retain their map references through construction. Only the later bulk root release is implemented. |
| Additional redundant-root release during extraction, section 8.1 | Required | The original safety move relation `M`, for example, stays retained throughout Skolemization. |
| Bounded collection/retry, section 9.2 | Required | No single GC-and-retry attempt for a recoverable failed operation. |
| Pressure-GC throttling/checkpoints, section 9.1 | Required | Basic checkpoints exist; ineffective-collection throttling and the full extraction/operation policy do not. |
| Exact demand-driven latch updates and realizability-only mode, section 10 | Conditional | Not implemented; the handoff calls for construction/retention evidence before starting this package. |

The handoff's detailed operation/failure diagnostics, node/phase accounting,
shared-session configuration, and semantic/ownership/fault-injection regression
matrix are also not complete. The process peak-RSS comparison does not replace
that instrumentation or establish which phase produced the peak. It measures
the current implementation, not the proposed last-use or demand-driven builds.

## Independent Closed-Loop Verification

On 2026-09-19, all three emitted controllers above were independently checked
against their original games using `scripts/verify_aiger_safety.py`:

| Instance | ABC PDR result | Proof process wall time |
| --- | --- | --- |
| `beemprdcell2f1_c0to1.aag` | SAFE (`snl_UNSAT`) | 0.064 s |
| `beemprdcell2f1_c0to3.aag` | SAFE (`snl_UNSAT`) | 0.064 s |
| `beemprdcell2f1_c0to7.aag` | SAFE (`snl_UNSAT`) | 0.064 s |

The runs retained 24, 22, and 18 environment inputs respectively, and each had
220 total latches (110 plant plus 110 controller latches). ABC reported a
one-clause invariant over two flops at
frame 3, successfully verified the invariant, and proved the property. This is
an unbounded safety result, not a depth-3 bounded check. The two UNREALIZABLE
driver results do not emit controllers and are not certified by this check.

The pipeline uses Armin Biere's `aigtoaig` and `aigmove -r`, SYNTCOMP's
`combine-aiger`, and ABC `pdr`. It shares no solver, parser, or composition code
with tlsf-tools. Interface checks require all controllable inputs to be driven
by the controller, retain only environmental inputs, and preserve the original
error predicate and separate plant/controller state. Both wrong-reset and
delayed-violation negative controls were rejected by the model checker.

Tool source revisions:

- AIGER: `8b7c75c3b6e57d67515ca97260e2b1b1e8312cd2` (existing clean checkout).
- combine-aiger: `06982aac91de91cdd62893c16589921cbc631daf`, built with
  `make CFLAGS='-std=c11 -Wall -Wshadow -pedantic -include strings.h'` to expose
  `strcasecmp` with the current compiler.
- ABC: `3660a63a392b276616dd56ffee7e47b29b5df95e`, clean build with
  `make -j4 ABC_USE_NO_READLINE=1`.

Input/controller/circuit and executable SHA-256 fingerprints, exact proof
statuses, and timings are recorded in [closed-loop-results.json](closed-loop-results.json).
The verifier retains full per-step commands, logs, and circuits in its output
directory. Reproduce with the command in
[the diagnostics guide](../../docs/tlsfsolve-diagnostics.md#independent-closed-loop-safety-check)
after regenerating the controller with the 32M-node/4M-cache settings above.
