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

These are functional sanity results, not a full performance campaign: RSS and
solver phase timings were not collected.

## What the Memory Results Establish

All capacity measurements above used the same final solver implementation.
They demonstrate that increasing the configured node cap allows these cases
to complete. They do not isolate the effect of construction-root release,
fused operations, memo lifetimes, or GC changes. No correctness-repaired
pre-optimization baseline was run at matching node/cache capacities, and no
before/after peak-memory or peak-node measurements were collected.

The implementation contains changes intended to reduce memory pressure, but
their net benefit on these benchmarks is currently unmeasured. In particular,
the final implementation still fails all five cases at 8M nodes / 4M cache;
the successful 32M-node runs are not evidence that the changes reduced the
required node capacity or peak RSS. The default capacity heuristic is unchanged,
and explicit larger capacities remain fixed arenas, not dynamic growth.

To establish an optimization benefit, compare the correctness-repaired baseline
and optimized solver at identical node/cache capacities and GC settings, using
the same input semantics, dependency revision, and build settings. Record
completion status, peak RSS, and node/GC measurements. Comparing against the
unmodified solver would confound this with the repaired error-output semantics.

The independent checks below establish correctness of the emitted controllers;
they do not measure memory efficiency.

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
