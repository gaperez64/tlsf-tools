# OxiDD Memory Diagnostics Report

Base branch: `origin/main` on 2026-09-19.

Issue addressed: [#24](https://github.com/gaperez64/tlsf-tools/issues/24),
opened by Sebastian Junges, reporting OxiDD solver failures around the fixed
node budget.  Sebastian's follow-up names these SYNTCOMP benchmark instances:

| Instance | Profile expectation | Status |
| --- | --- | --- |
| `HWMCC12/beemprdcell2f1_c0to1.aag` | `legacy-safety` | not run |
| `HWMCC12/beemprdcell2f1_c0to3.aag` | `legacy-safety` | not run |
| `HWMCC12/beemprdcell2f1_c0to7.aag` | `legacy-safety` | not run |
| `driver/driver_c2y.aag` | `legacy-safety` | not run |
| `driver/driver_c2n.aag` | `legacy-safety` | not run |

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

No release-performance numbers are recorded in this PR because the external
issue-#24 corpus was not fetched and run in this environment.  Fill measured
results here after running the pinned corpus under fixed node/cache budgets and
an external memory limit.
