# Default-mode effect of syntactic X protection

Task T now also checks the research component algorithm in an executable Lean
model. Its simulation includes recomputed syntactic protection, simultaneous
DROP_X and retry; the executable regressions pin the review-k/l rejecting
classes below. This strengthens the component evidence without changing C,
default admission, state counts, or the still-open complete constructor bridge.
See `proofs/README.md` for the exact theorem scope and remaining obligations.

Keep syntactic X protection in both modes. The default admission predicate is
unchanged, but the automata can differ, including their priorities, state
counts and resource-budget outcomes. This audit compares parent `b149ef5`
with `ea89484` on branch `proofs/lazy-dpa`.

## Which extractor is proved

`proofs/TlsfProofs/Dpa/Classes.lean` defines `Protected x t` by exact current
class support of a non-X modal atom and **syntactic** membership of t in that
atom's `subformulas`. It does not first materialize or simplify the atom's
operand. `dropX` simultaneously replaces unprotected X atoms by true;
`elide` recomputes protection after each changing pass. `extractPass` is
REDUCE, elision, then unfolding. `rho` retries on unfolded raw input when
the first result is finite and the raw input was not already unfolded.

`Stage1.lean`'s `initial` and ordered `transition` table call this `rho`.
Its `run` and `marks` are the runs used by the Stage 1 safety/co-safety and
GF/FG results, `Converse.lean`'s `flat_global_language`, and ultimately
`admitted_product` / `admitted_grammar`. There is no alternate default-mode
extractor in the formalization. Safety/co-safety components never need a
rejecting obligation (`simple_run`); flat G/F components do. In particular,
`flat_constraint_protected` and `minimal_extractPass_constraint` use
syntactic protection to preserve a failed clause through X elision. The
flat-fragment theorem is not a theorem that protection is irrelevant.

For the admitted formula

```text
G(F(a | (a & X X b)) | X X b)
```

both `a | (a & X X b)` and `X X b` are finite windows, so the outer body is
`FlatQ` and `Admitted.global` applies. The supported F atom syntactically
contains `X X b`, even though materializing its operand absorbs it to `a`.
The retry yields the initial rejecting class

```text
a | F(a | (a & X X b)) | X X b
```

which is not propositionally true. The parent walks the materialized operand,
loses the protector and initializes the rejecting field to true. HEAD's
syntactic walk matches the extractor used by the default theorems. Thus keep
the change in both modes. This establishes the extractor correspondence, with
the documented trusted C representation, tags and constructor bridge; the
theorems do not certify the C implementation or the parent's alternate walk.

A kernel diagnostic checked `Admitted` for this exact syntax, the retry result,
and the non-true initial rejecting field with Lean 4.35.0. Its axiom audit lists
only `propext`, `Classical.choice` and `Quot.sound`.

## Paired measurements

The four DPA translation units and private header were taken from each exact
revision and compiled separately (`cc -O1 -g -std=c23`). They were linked to
the same unchanged conversion code, OxiDD and Spot 2.16 libraries. Every
comparison used the same test inputs and budgets. Builds and final validation
ran serially inside the inherited cgroup (`memory.max=5368709120`,
`memory.swap.max=0`), with no OOM events. A first brief diagnostic accidentally
overlapped a test; that diagnostic and the affected test were rerun serially.
Peak cgroup memory was 2,773,413,888 bytes (2.58 GiB).

### Existing default-mode suites

| Check | Parent | HEAD |
| --- | ---: | ---: |
| Contract / failure-path gate | pass | pass |
| Revision's Stage 2 structural gate | pass | pass |
| Matched existing equivalence invocation | 110 passes | 110 passes |
| Sum / maximum states over those 110 cases | 800 / 65 | 800 / 65 |
| Fixed-seed random default equivalences | 72 passes | 72 passes |
| Sum / maximum states over those 72 cases | 216 / 9 | 216 / 9 |
| Unexpected admissions declined / budget hits in equivalence checks | 0 / 0 | 0 / 0 |

All 182 paired state counts are identical; see
[the per-case table](DEFAULT-PROTECTION-SUITES.tsv). The matched invocation
uses the pre-regression `ea89484` harness, including its always-on research
examples; the random invocation uses default mode throughout. Each revision's
own structural gate avoids treating research-admission changes as default-mode
failures. The Spot harness budgets are 10,000 states and 64 MiB C host storage,
with the library's bounded BDD defaults. These passing suites did not contain
the default protection example.

### Protection regression

| Mode / bound | Parent | HEAD |
| --- | --- | --- |
| Default, unrestricted | OK, 4 states | OK, 5 states |
| Research, unrestricted | OK, 4 states | OK, 5 states |
| Default, `max_states=4` | OK, 4 states | DECLINED / STATE_LIMIT, 4 partial states |
| Research, `max_states=4` | OK, 4 states | DECLINED / STATE_LIMIT, 4 partial states |

Both unrestricted languages are equivalent to the formula. The new C
regression constructs the AST directly to retain its frozen syntax, checks
the initial rejecting field and pins both the five-state completion and
four-state decline. The Spot suite additionally checks the formula and its
negation in both invocations. A partial state count after a decline is
censored data, not the size of a completed automaton.

The new structural regression fails on the parent at the rejecting-field
assertion and passes on HEAD. All eight paired formula/negation/mode language
checks pass, with four states on the parent and five on HEAD. Final focused
Meson validation passes all six gates: default/research equivalence,
default/research random, Stage 2 structure and BDD limits. The final default
invocation now checks 112 equivalences, including the two added examples.
Pinned clang-format 22.1.8 passes on all changed C/C++ files. The changed C
files compile without warnings; the C++ build reports existing anonymous-struct
warnings from `include/tlsf/ast.h`.

### Inventory scope and reproduction

The full 69-objective rerun is pending the missing `semml-only.list` (or its
45 default-admitted names). The list is not in this checkout, the documented
`../../otfpar/semml-only.list` path is absent, and the original raw inventory
results were not committed. The materialized TLSF corpus and 1,524-name source
mapping are present. The 24 named default declines can be recovered from
`STAGE2-INVENTORY.md`; they are a known subset, not a replacement inventory.
The historical 45/69 and 69/69 totals must not be read as a fresh full-corpus
measurement on either revision.

The recovered 24-objective subset was run on both revisions:

| Observation, over the named 24 only | Parent | HEAD |
| --- | ---: | ---: |
| Default admissions / unsupported declines | 0 / 24 | 0 / 24 |
| Research admissions / admission declines | 24 / 0 | 24 / 0 |
| Completed research expansions | 0 | 0 |
| Research HOST_LIMIT / BDD_LIMIT / DEADLINE hits | 5 / 2 / 17 | 5 / 2 / 17 |
| Sum / maximum partial research states | 97,184 / 9,414 | 97,215 / 9,414 |

[Per-objective results and TLSF source hashes](DEFAULT-PROTECTION-INVENTORY-24.tsv)
record every mode and status. Default expansion was not attempted on an
unsupported input. Research counts are all censored; differing progress at a
cooperative deadline does not establish a difference in completed state counts.
There were no state-limit hits or errors in this subset. The source mapping
comes from acacia-bonsai revision `1571a87b05cdad26deb97ceb96e0f49b2129682b`;
its SHA-256 is
`9fbc4007b18065296d592f14bd9ef0e9e95a4893a4d4477e0153013fa531f92f`.

`dpa_admission` retains its admission-only default. Its new optional
`--expand` mode emits a TSV row per source and mode, recording create status,
expansion status/reason and states. It uses the existing effective-Mealy
conversion, with no Spot normalization, and runs default then research serially.
Limits per context, including creation: 10,000 states, 512 MiB C host storage,
2^22 BDD nodes, the default BDD cache, and a cooperative ten-second monotonic
deadline. BDD storage is separate from the C host-byte budget; the cgroup
limits total memory. Only an OK expansion is a complete state count.

```sh
meson compile -C build -j1 dpa_admission
build/test/unit/dpa_admission --expand SOURCE1.tlsf SOURCE2.tlsf > inventory.tsv
```

The numeric code/reason columns use `include/tlsf/dpa.h`; `NA` means expansion
was not attempted because creation declined. Use the 69 names from
`semml-only.list`, joined one-to-one with
`acacia-bonsai/tests/suites/benchmarks/syntcomp26/tlsf-sources.tsv` against the
materialized TLSF corpus. Do not substitute all 1,524 competition inputs or
the 46 admitted stored Owl trees for the API's 69 complete objectives.
