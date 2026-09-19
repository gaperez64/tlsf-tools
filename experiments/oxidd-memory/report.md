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

Implemented comparison points:

| Label | Contents |
| --- | --- |
| Correctness-repaired baseline | Property-preserving AIGER 1.9 parser, profile resolver, positional legacy output 0, exact `controllable_` ownership, reset rejection for unsupported uninitialised latches. |
| Budgeted | Baseline plus `--oxidd-nodes`, `--oxidd-cache`, `--oxidd-gc`, and `--oxidd-gc-threshold`. |
| Lifetime/fused | Baseline plus construction-root release, per-root conversion memo scopes, allocation-free BDD identity, and fused safety/GR(1) CPre conjunction-exists. |
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

These are functional sanity results, not a full performance campaign: strategies
from the three realizable cases were not independently closed-loop checked in
this run, and RSS/phase timings were not collected.
