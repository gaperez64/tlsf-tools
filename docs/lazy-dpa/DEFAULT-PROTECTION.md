# Syntactic X protection in default admission

Keep syntactic X protection in both modes. It preserves default admission but
can change priorities, state counts, and budget outcomes. This audit compares
`b149ef5` (parent) with `ea89484` on `proofs/lazy-dpa`; measurements are historical.
Current [translation validation and trust limits](../../proofs/README.md#automaton-translation-validation)
cover the uncached executable reference. GR(1) tries general admission after
default decline; standalone DPA defaults stay unchanged.

## Extractor correspondence

`proofs/TlsfProofs/Dpa/Classes.lean` defines `Protected x t` using exact support
of a non-X modal atom and syntactic membership in its `subformulas`, before
operand materialization/simplification. `dropX` simultaneously replaces
unprotected X atoms with true; `elide` recomputes protection per changing pass.
`extractPass` performs REDUCE, elision, unfolding; `rho` retries unfolded raw
input if the first result is finite and raw input was not unfolded.

`Stage1.lean`'s `initial`/ordered `transition` use this `rho`; its `run`/`marks`
feed safety/co-safety, GF/FG, `Converse.lean`'s `flat_global_language`, and
`admitted_product`/`admitted_grammar`. No alternate default extractor is proved.
`simple_run` needs no rejecting field for safety/co-safety; flat G/F does.
`flat_constraint_protected` and `minimal_extractPass_constraint` specifically
preserve failed clauses through syntactic protection.

For the admitted formula

```text
G(F(a | (a & X X b)) | X X b)
```

both inner windows are finite, so the body is `FlatQ` and `Admitted.global`
applies. The supported F atom protects `X X b` even though materializing its
operand absorbs it to a. Retry produces the nontrue initial rejecting class:

```text
a | F(a | (a & X X b)) | X X b
```

The parent's materialized walk loses the protector and initializes true.
The syntactic walk matches the default theorem's extractor, subject to trusted
C representation/tags/constructor correspondence; it does not certify C or
the parent walk. A Lean 4.35.0 diagnostic checked `Admitted` for this syntax, retry,
and nontrue field, with only `propext`, `Classical.choice`, and `Quot.sound`.

## Paired measurements

Each revision's four DPA translation units/private header were compiled with
`cc -O1 -g -std=c23` and linked to identical conversion code, OxiDD, and Spot
2.16 libraries. Inputs/budgets match. Final builds/tests ran serially in
`memory.max=5368709120`, `memory.swap.max=0`, without OOM; peak memory was
2,773,413,888 bytes (2.58 GiB). An overlapping diagnostic/test pair was rerun serially.

| Check | Parent | HEAD |
| --- | ---: | ---: |
| Contract / failure-path gate | pass | pass |
| Revision's Stage 2 structural gate | pass | pass |
| Matched existing equivalence invocation | 110 passes | 110 passes |
| Sum / maximum states over those 110 cases | 800 / 65 | 800 / 65 |
| Fixed-seed random default equivalences | 72 passes | 72 passes |
| Sum / maximum states over those 72 cases | 216 / 9 | 216 / 9 |
| Unexpected admissions declined / budget hits in equivalence checks | 0 / 0 | 0 / 0 |

All 182 paired state counts match; see [per-case data](DEFAULT-PROTECTION-SUITES.tsv).
The matched `ea89484` pre-regression harness includes its research examples;
random tests use default throughout. Each revision uses its own structural
gate to separate research admission from default behavior. Spot harness caps
are 10,000 states, 64 MiB C host storage, and bounded library BDD defaults.
These suites omit the protection regression:

| Mode / bound | Parent | HEAD |
| --- | --- | --- |
| Default, unrestricted | OK, 4 states | OK, 5 states |
| Research, unrestricted | OK, 4 states | OK, 5 states |
| Default, `max_states=4` | OK, 4 states | DECLINED / STATE_LIMIT, 4 partial states |
| Research, `max_states=4` | OK, 4 states | DECLINED / STATE_LIMIT, 4 partial states |

Both unrestricted languages match the formula. A direct-AST C test preserves
frozen syntax, checks the initial field, and pins five-state completion and
four-state decline. It fails the parent field assertion. Spot checks both
formula and negation in both invocations: all eight language checks pass,
with four parent/five revised states. Declined counts are censored, not complete.
Six focused Meson gates pass: default/research equivalence, default/research
random, structure, and BDD limits. The final default invocation has 112
 equivalences, including both additions. clang-format 22.1.8 passes; C has no
warnings, while C++ retains anonymous-struct warnings in `include/tlsf/ast.h`.

## Inventory limits and reproduction

The full 69-objective rerun needs missing `semml-only.list` or its 45 admitted
names. Neither the list at `../../otfpar/semml-only.list` nor original raw
results are committed; the materialized corpus and 1,524-name mapping exist.
The 24 named declines in [STAGE2-INVENTORY.md](STAGE2-INVENTORY.md) are only a
recoverable subset. Historical 45/69 and 69/69 totals are not fresh full runs
on either revision. On that subset:

| Observation, over the named 24 only | Parent | HEAD |
| --- | ---: | ---: |
| Default admissions / unsupported declines | 0 / 24 | 0 / 24 |
| Research admissions / admission declines | 24 / 0 | 24 / 0 |
| Completed research expansions | 0 | 0 |
| Research HOST_LIMIT / BDD_LIMIT / DEADLINE hits | 5 / 2 / 17 | 5 / 2 / 17 |
| Sum / maximum partial research states | 97,184 / 9,414 | 97,215 / 9,414 |

[Per-objective statuses and source hashes](DEFAULT-PROTECTION-INVENTORY-24.tsv)
include every mode. Unsupported default inputs are not expanded. All research
counts are censored; cooperative-deadline progress differences do not establish
completed-size differences. No state limits/errors occurred. Source mapping
is from acacia-bonsai `1571a87b05cdad26deb97ceb96e0f49b2129682b`, SHA-256
`9fbc4007b18065296d592f14bd9ef0e9e95a4893a4d4477e0153013fa531f92f`.

`dpa_admission` defaults to admission-only; `--expand` writes source/mode TSV
with creation status, expansion status/reason, and states. It uses effective-Mealy
conversion without Spot normalization, default then research serially. Per-context
limits include creation: 10,000 states, 512 MiB C host storage, 2^22 BDD nodes,
default cache, and a cooperative ten-second monotonic deadline. BDD storage is
separate from host bytes; the cgroup bounds total memory. Only OK counts are complete.

```sh
meson compile -C build -j1 dpa_admission
build/test/unit/dpa_admission --expand SOURCE1.tlsf SOURCE2.tlsf > inventory.tsv
```

Codes/reasons use `include/tlsf/dpa.h`; `NA` means creation declined. Join the
69 list names one-to-one with
`acacia-bonsai/tests/suites/benchmarks/syntcomp26/tlsf-sources.tsv` and the corpus.
Neither all 1,524 competition inputs nor 46 admitted stored Owl trees replace
these 69 complete API objectives.
