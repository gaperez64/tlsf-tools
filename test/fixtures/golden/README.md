# Golden integration fixtures

Meson/CI read committed expectations and run native checks, without Spot or
other external synthesis oracles. `provenance.json` distinguishes independently
checked semantics from native serialization/metadata snapshots and binds payloads
with SHA-256. `tool-versions.json` pins references; `skipped.json` records censored
cases. Current translation hashes cover only successful unbounded language
checks; bounded lasso memberships alone are regression evidence, not equivalence.

## Checks and trust

| Former oracle | Golden/in-house check |
| --- | --- |
| Lazy DPA full-language comparison | Canonical ASTs and 512 reference membership bits per formula; in-house max-odd parity evaluation; all valuations independently check each state's deterministic, complete transition partition |
| Random and Delta₂ generation/filtering | Committed historical fixed-seed corpora, including all 360 Delta₂ formulas and complements/mixed skeletons |
| Native reduction/Python differential | Both exact/strict reductions of the fixture corpus and generated naming/decline cases; independently confirmed circuit functions, ownership, symbol maps and legacy provenance; native serialization and metadata snapshots |
| Native reduction language | Eleven complete objectives on 52 fixed lasso words each, evaluated directly on the native AAG |
| Monitor encoding/game/controller checks | Cross-size provenance, component lasso memberships, fallback construction, exact/strict difference, native solver verdicts and certificates, 40 alpha pairs, explicit universal controller verification, output/latch mutations and invalid interfaces |
| Optional Stage C external differential | Independently confirmed seeds, role partitions, predicate arities and certificate/policy functions; native evidence and artifact serialization snapshots |
| Disjoint assumptions equivalence | Original/residual formula snapshots and reference verdicts; direct GF/FG semantics on 420 lasso words |
| Decomposition verdicts | Reference verdicts keyed by the complete emitted formula and its signal partition, retaining all original scenarios |
| Compose driver semantics | Complete driver and cluster-file snapshots for every original timing, finite, policy and implicit-input case; driver text checks preserve error/stale-controller handling; no emitted driver is executed |
| Timing and interface exports | Original verdicts, complete scripts and cluster files, exact partitions, lowercase-collision guards and wrapper refusals |
| Normalization equivalence | Complete normalized TLSF and both objectives; reference equivalence confirmed with `ltlfilt --equivalent-to=ORIGINAL -f NORMALIZED` |
| API visitor/string equivalence | Complete visitor, string-API and cluster/partition exports, confirmed with the reference equivalence checker |
| Pinned `8b158d7` runtime rebuild | Complete native API/CLI outputs, artifacts and check reports confirmed by the passing pre-change differential; eliminates the old checkout's transitive Python oracle probe |

Reference verdicts use `ltlsynt --realizability --ins=... --outs=... -f FORMULA`
or `ltlfsynt --realizability --semantics=Mealy|Moore ...`. Infinite Moore uses
the complemented Mealy dual (negate objective, exchange players).
`tools/golden/reference.cc` independently computes memberships with the pinned
parser/translation/word intersection. Initial automaton snapshots used Spot 2.16;
native verdicts also pass `tlsfcertcheck`.

The DPA corpus retains seeds 31415, 27182, 20852, historical generation/filter
commands, committed words/memberships, all 360 Delta₂ formulas and their
complements/mixed skeletons. Running tests need no random generator. Historical
full-language/Π₂ search tools remain under `tools/golden/`, outside Meson.
Product route names in `.route_stats` and external script commands are data.
`test/fixtures/fake_backend.sh` is a deterministic protocol stub invoking no
synthesizer; `bench/bench.sh` measures native work and refuses fallback.
Fault injection uses `src/lib/gr1_reduction_test_hooks.hh`'s test-only macro;
contract tests exercise every fault.

The universal certificate oracle, `test/gr1_one_step.c`, links only OxiDD and
platform libraries. Its independent AAG/JSON parsing and per-goal BDD compilation
check unsatisfiability of violations over all invariant states/uncontrollable
inputs: reset, safety, transitions, inductiveness, moves, goal counters, ordered
fairness ranks, and input-acceptance sampling. Per-goal arenas release handles;
no libtlsf parser/solver internals or handwritten Python BDD package are used.
The 240-game differential retains three original mutations and five symbolic
AAG mutations (invariant/move/rank/state-latch/counter-latch), explicitly checks
the first eight realizable games, and handles two goals over 36 state variables
without enumerating the domain. A long signal-name check also passes.

Native monitors use Stage 1 safety/co-safety, breakpoint recurrence with
`HasTag Pi2`, and a positive Boolean Buchi round. A round sets seen colours true
in residual acceptance, resets on completion, and remembers the incoming mark
for one-hot encoding. Infinitely completed rounds equal the positive Inf-colour
formula; an accepting finite initial mark avoids an extra latch in common
safety/response cases. General parity behavior is unchanged.

C++ handles JSON/provenance/containers/signatures; formulas own native AST views.
Symbolic classes compare propositions, and proved DPAs plus exact max-odd SCC
emptiness compare temporal provenance. Normalized provenance preserves semantic
constants and `G(a R b)=G(b)`, separately retaining construction text. Exact/strict
encoding, lifting, public API, and four profiling stages are unchanged.
Limits bound discovery/one-hot latches; failed expansion reports the first
excluded state as a lower bound. Edge counts use complete rows and may cross
a limit by one row. Deadline/cancel/RSS checks are cooperative. Completed
monitors retain exported labels/names and release managers before the next
conjunct. `fallback_monitor_count` remains zero. No library/default-Meson
include/dependency/oracle needs Spot; `libspot` is not queried or required by
`tlsf.pc`, and the standalone example is outside Meson.

## Offline regeneration

Regeneration is outside build/CI; fixture changes alter the oracle. There is
no test option/environment variable for recording expectations. Every reference
call has a deadline. Mandatory native/lift confirmations fail on timeout,
missing references, or disagreement before data/provenance is written; other
censored cases enter `skipped.json`, never silent new skips. Other independently
checked suites also require references. `--only` selects a batch.

Prepare the retired reducer/lift references first, one heavy job at a time:

```sh
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  python3 tools/golden/prepare_legacy.py \
    --acacia /path/to/acacia-bonsai --build build \
    --spot "$HOME/spot-2.16-install" \
    --spot-source "$HOME/spot-2.16-src/spot-2.16" --output build/reference
# Use the two paths printed by prepare_legacy.py:
for suite in native lift; do
  systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
    python3 tools/golden/regenerate.py --build build \
      --spot "$HOME/spot-2.16-install" --only "$suite" \
      --bindings-site build/reference/spot-python \
      --oracle-root build/reference/prototype
done
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  python3 tools/golden/test_gates.py --build build \
    --spot "$HOME/spot-2.16-install" --bindings-site build/reference/spot-python
```

The prototype comes from Acacia
`b615c3c4c2dc1a2b13c035b62b115c0d1148a977`, before retirement. Matching Spot
2.16 Python bindings are compiled against `$HOME/spot-2.16-install`. The local
libbddx hash differs from its historical allowlist; setup checks every variable
below a conservative 1024-variable ceiling and adds that hash without changing
reduction/lifting/comparison algorithms. It generates the source/binary manifest.
Then run the full recorder (the original baseline build was `7b44d9f` on
`chore/remove-spot`, 2026-10-31):

```sh
PKG_CONFIG_PATH="$HOME/spot-2.16-install/lib/pkgconfig" \
  meson setup build -Dresearch_tools=true
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  env CARGO_BUILD_JOBS=2 meson compile -C build -j2
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  python3 tools/golden/regenerate.py --build build --spot "$HOME/spot-2.16-install" \
    --bindings-site build/reference/spot-python --oracle-root build/reference/prototype
```

The historical `8b158d7` snapshot requires restoring its original differential
before changes. `test_gates.py` rejects the decline-everything mutant at
`aliases_v12.tlsf:exact`, preserving its recording; three original rejection
scenarios and four later recorder checks include unconfirmed pruning verdicts.
Normal tests check hashes and size without Spot. Compact JSON stores one record
per line without losing fields/scenarios/precision. The current total budget is
4,613,734 bytes (4.4 MiB); historical recordings used a 4,629,524-byte cap.

Pruning regeneration is separate:

```sh
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  env TMPDIR="$PWD/build-u/tmp" CARGO_BUILD_JOBS=2 \
  python3 tools/golden/regenerate.py --build build-u \
    --spot "$HOME/spot-2.16-install" --only pruning
```

Translation regeneration requires Lean and is documented in
[the proof guide](../../../proofs/README.md#regeneration-and-recorded-results).
The C-only `dpa_translation_hashes` test recomputes passing dumps exactly.
[translation/report.json](translation/report.json) retains per-set/policy/kind
counts and every timeout; neighboring files bind source/checker/corpus provenance.
Only passing checks enter `translation/hashes.tsv`; timeouts are neither minimized
nor hash-guarded. Runtime formulas without a validated golden rely on the proved
reference plus sample. C memory safety, decoding, hashing, and BDDs stay trusted.

The 2026-11-03 DAG constructor addition updates the source hashes for
`include/tlsf/dpa.h` and `src/lib/dpa.c`; existing translation functions are
unchanged. The recorded Lean validation date, reports, and all 4,134 translation
hashes remain unchanged. CI recomputes those dumps through the existing AST API;
the new DAG API has separate contract tests and is not covered by the historical
Lean validation run.

The deadline clock-sampling update keeps those historical source hashes and
the original compiler-order receipt. `translation/provenance.json` records
explicit old/current source bindings separately; its checker rejects unbound
current sources. `dpa_translation_hashes` recomputes all 4,134 unchanged dumps,
while `dpa_deadline` checks cooperative sampling and exact API boundaries. This
does not rerun the historical Lean validator or prove a wall-time bound.

The separate 2026-11-04 [DAG receipt](translation/dag/provenance.json) is a fresh
run through `tlsf_dpa_create_from_dag`: 72 requests, 68 language-validation
passes, four unsupported Büchi declines, zero failures and zero timeouts. It
binds source revision `ab6d4aea8ce38b4dd955a0609c2963e7b26e6fc1`, all input and
validator source hashes, the actual C/Lean executables, AP partitions/orders,
both signed whole-objective polarities, normalized DAG records and acceptance
kinds. Sharing, nonfinal roots and unused/reordered AP declarations are covered.
`dpa_dag_translation_hashes` recomputes the 68 passing C dumps in CI. The
neighboring report separates the checked claim (automaton recognizes normalized
psi) from the explicit caller-trusted premise (psi is equivalent to signed whole
phi). The conditional Lean theorems require that premise; this receipt does not
check it or the caller's extraction of phi. Only completed automata with closed
full rows and valid targets enter validation, using max-odd parity or recurring
source-state Büchi priority 1. Declines and partial/resource/cancelled/deadline
outcomes have no validated hash. The seven decoding and four added validation
results have permitted-axiom audits. These sample checks do not establish
universal C refinement, memory safety, BDD refinement or compiler correctness.
Historical reports/dates and successful TV1 dumps remain unchanged; the old
provenance points separately to this extension and records its source bindings.

## Recorded reference scope

Independent confirmation on 2026-10-31 compared all 436 exact/strict reductions
with retired `origin/main` (`7b44d9f`): 320 successes, 116 declines (86 unsupported,
30 invalid), zero disagreements. Successes passed circuit functions/reachable
bisimulation, ownership, symbol maps, and legacy provenance. Decline disposition
is independently checked; exact codes/diagnostics are native snapshots.
All 13 lifts matched the archived prototype: seven successes, six matching-stage
declines, with seed values, role classes, predicate arities, methods/verdicts,
and exact certificate/policy functions checked. Expectations did not change.

The six pinned lift declines are `arbiter_on_inpchange_pb_2_pe_`,
`arbiter_pb_2_pe_`, `arbiter_pb_3_pe_`, and both `round_robin_arbiter_unreal2`
cases (`seed_window: no stable index axis`), plus `arbiter_pb_4_pe_`
(`schema: no bounded exact template`). The original 25 data files held
4,621,132 bytes plus this note/tool versions/skips, covering:

- 541 DPA rows × 512 words = 276,992 memberships, eight budget-limit ASTs,
  72 random formulas, and 360 Delta₂ formulas.
- 2,272 further memberships: 572 native-language (11 objectives × 52 words),
  1,280 component-monitor, 420 disjoint-assumption observations.
- 226 reference verdicts, 63 export directories, and 315 emitted files.
- 436 reductions, 118 focused monitor reductions, 89 native solve/certificate
  checks, and 13 lifts, including generated/renamed successes.

No scenarios were dropped or generation cases timed out; `skipped.json` was
empty. The tools-only full-language oracle subsequently passed handwritten,
72-random, and 360-Delta₂ batches with 60-second caps, outside Meson/CI.

### Native-default admission snapshot

The initial native-default rewrite declined 14 previously successful exact/strict
cases (seven specs), returning `TLSF_GR1_REDUCE_UNSUPPORTED`. Reference artifacts were not regenerated.
`provenance.json` archives replaced groups/reasons/sizes and reconstructs the
original payload/hash to prove other expectations unchanged. Historical backend
diagnostics remain archived; native grammar/AP diagnostics compare by category/status.
These rows describe that restricted-admission snapshot, before general fallback:

| Specification | Declined conjunct | Old monitor states | Reason |
| --- | --- | ---: | --- |
| `bounded_until.tlsf` | `G(go -> (p U q))` | 3 | U in a G body is outside the proved finite-window/F(window) grammar. |
| `definition-future.tlsf` | `G(p <-> F q)` | 4 | NNF polarity mixes F and G obligations in the body. |
| `delayed-definition-future.tlsf` | `G(X p <-> F q)` | 6 | The same mixed body, with a delayed output. |
| `ident_m_function.tlsf` | `G(b U (a & b))` | 3 | Until/strong-release beneath G is outside the proved body grammar. |
| `normalization_sickert2.tlsf` | `G(req -> (a U G F p))` | 5 | Nested U/GF is outside proved admission; research admission also declines it without the required syntactic Pi2 tag. |
| `precedence_v12.tlsf` | `(a U b) W c` | 5 | Weak until contains a liveness obligation, outside the proved components. |
| `route_norm_xgf.tlsf` | `X G F g` | 2 | X surrounds a recurrence component; default admission does not admit that wrapper. |

Nine decomposition observations also initially declined: `G(p <-> F q)`
(four, old size 4), `G(X p <-> F q)` (one, 6), `G(X X p <-> F q)` (one, 9),
and `G(F q -> F p)` (three, 4). Their mixed G bodies exceed the default grammar;
original verdicts and payload hashes remain archived. The unregistered spare
`test/oracle/env_lift_capacity.tlsf` also declined `G(r_m -> X((AND_i !g_i) U g_m))`
(old size 4); the active capacity test uses `env_lift_one.tlsf`.

The 217-file `bench/`/`test/` inventory compared baseline `cf33da9` with a fresh
native build, `PKG_CONFIG_PATH` unset and `pkg-config --exists libspot` failing.
Both used exact semantics, 10,000 states, 16 MiB artifacts, and 20-second process
deadlines, with no timeouts:

| Corpus | Specs | Before | Proved default | Research admission/expansion |
| --- | ---: | ---: | ---: | ---: |
| `bench/` | 6 | 1 | 1 | 1 |
| `test/fixtures/cases/` | 198 | 142 | 135 | 141 |
| `test/fixtures/gr1_monitor_game/` | 6 | 6 | 6 | 6 |
| `test/fixtures/arbiter_simple.tlsf` | 1 | 1 | 1 | 1 |
| `test/oracle/` | 6 | 6 | 5 | 6 |
| **Total** | **217** | **156** | **148** | **155** |

Default lost 8/156 specs (5.1%); general admission recovered seven.
Invalids stayed 15; unsupported went 46→54. Excluding the spare, coverage was
155→148/216. Exact/strict successes were 320→306/436, with 100 unsupported and
30 invalid; all six monitor-game specs/13 lift dispositions stayed intact.
The 148 retained successes had 1,215→1,231 monitor states. Full source hashes,
counts, declines, and research results are in `tools/analysis/nospot-phase2.json`.
Reproduce serially:

```sh
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  python3 tools/analysis/gr1_corpus.py BUILD OUTPUT.json
find bench test -name '*.tlsf' -print0 | sort -z | \
  systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
    xargs -0 BUILD/test/unit/gr1_admission
```

`dpa_buchi_goldens` checks 313/541 admitted formulas × 512 words = 160,256
memberships, declines 228, and independently enumerates transition partitions.
Existing memberships/verdicts/certificate/controller mutations remain registered.
Snapshot comparison permits different state encodings while checking languages,
ownership, source bindings, roles, and symmetric signatures against frozen data.

### Assumption pruning

The merged lasso search/cache tests/Lean `Pruning.lean` bridge remain.
`assumption-pruning.json` freezes `test_assumption_pruning.py`’s 85 exports
and 63 Spot 2.16-confirmed verdicts,
covering original/both emitted ordinary/strict objectives: inconsistent joint
environments, winning/losing cores, INITIALLY/REQUIRE, transient prefixes,
nonconstant loops, and search UNKNOWN. Native assertions/snapshots separately
cover transitive support, PRESET/ASSERT, finite/Moore retention, syntax budgets,
and complete source/output partitions. Provenance binds native revision, test
source/payload hashes, counts, and reference scope. Recording on 2026-10-31 had
no skips/timeouts; a second regeneration reproduced every byte.

The recursive external-oracle guard rejects reference command discovery/execution
and static/dynamic imports, including the original pruning script and eight
mutants. Product-script reference names remain data. Research tests read fixtures
and invoke native binaries without reference discovery.

DESCRIPTION-only edits in `cluster_assume.tlsf`/`cluster_prune.tlsf` changed eight
reduction source-hash fields (two per spec/semantics), preserving all circuits,
monitors/statuses/other fields. Recording required other bytes identical and
four ordinary/strict `ltlfilt` equivalence checks. The manifest archives sources
and locations; provenance reverses replacements to verify pre-merge/original
hashes. A circuit mutation still failed after renewing its current payload hash.
Pruning data added 32,134 bytes; no reference circuit was regenerated.

### General admission and translation sample

The fresh 2026-11-01 inventory has 4,134 pass / 0 fail / 36 timeout and 678
unsupported requests under the shared 17-second budget. All admitted corpus
constructors finish/pass; timeouts belong to larger golden/equivalence formulas.
The [proof guide](../../../proofs/README.md#regeneration-and-recorded-results)
contains the complete results table and minimized positivity regressions.
Explicit positivity remains required for rounds; nonpositive cases compare via
the proved Buchi-to-parity embedding. Original/minimized receipts are in
`tools/golden/translation-fixed-rejections.json`, with minimized forms/complements
permanently inventoried.

GR(1) tries general admission after default unsupported decline. Corpus coverage
is 155/217 (previously 148), unsupported 47 (54), invalid 15. Restoring 12 native
exact/strict and nine decomposition observations with
`tools/golden/restore_general_goldens.py` preserved original payload hashes and
reference artifacts. `normalization_sickert2.tlsf` stays declined in both semantics.
Native successes are 318/436 (previously 306), 88 unsupported, 30 invalid.
The directory, archives, provenance, and translation report fit 4.4 MiB.

## Recorded validation

These are historical runs, not results of editing this README. Builds/tests and
heavy offline jobs ran serially with `MemoryMax=5G`, `MemorySwapMax=0`, at most
two workers, and build-local TMPDIR. Formatting used clang-format 22.1.8.

| Run | Result |
|---|---|
| Unchanged baseline / frozen conversion | 378/378 and 384/384; failing Spot command traps and `spot`/`buddy` import hooks had zero hits. Wrapper comment/AP regression used the stub; no generated driver ran. |
| Independent confirmation | 385/385; 240 games (130 REAL/110 UNREAL), 44,990 predicate evaluations, 8,952 explicit steps, three original/five symbolic mutations, two symbolic goals over 36 variables. |
| Native monitors | 386/386 without timeouts; coverage table below. |
| Stable C++23 (`research_tools=false`, no `PKG_CONFIG_PATH`) | All targets compiled; 5/5 focused checks: C limits, 436 reductions, 13 lifts, layout, oracle/dependency guard. Public client `ldd` excludes Spot/libbddx; `tlsf.pc` privately requires yyjson plus existing OxiDD/platform/C++ links. |
| Native benchmark | `bench/bench.sh --build build-r --runs 3 --check`: six inputs, no regression. |
| Pruning integration | Fresh `env -u PKG_CONFIG_PATH meson setup build-u -Dresearch_tools=true`: 390/390, zero attempts under six command traps and `spot`/`buddy`/`acacia_lift` import hooks. No Spot/libbddx client link; 105 proof references/64 anchor targets plus witness ranges passed. |
| Translation integration | 392 verified: 389 serial passes plus three targeted reruns; 30 construction/equivalence checks, 21 protocol checks, 48 permitted-axiom audits, seven Python deadline/verdict regressions. C gate recomputed all 4,134 dumps. |

Coverage used clean counters after generation/compilation, CI's exact `gcovr`
filters/invocation, `-Db_coverage=true -Dresearch_tools=true`, GCC 15.3.1,
Meson 1.8.5, gcovr 8.6. The frozen conversion measured:

| CI metric | Before | After |
| --- | --- | --- |
| Lines | 81.2% (23490/28913) | 82.0% (23741/28945) |
| Functions | 95.3% (1346/1412) | 95.8% (1356/1415) |
| Branches | 57.2% (19294/33758) | 58.3% (19728/33828) |

The later confirmation had identical line/function counts and 58.3% branches
(19,729/33,828). Native monitoring, excluding baseline-build counters, measured:

| CI metric | Frozen monitors | Native default monitors |
| --- | --- | --- |
| Lines | 82.0% (23,741/28,945) | **82.2% (24,205/29,430)** |
| Functions | 95.8% (1,356/1,415) | **96.0% (1,388/1,446)** |
| Branches | 58.3% (19,729/33,828) | **58.7% (20,374/34,707)** |

Recorded directory sizes including provenance/README were 4,629,524 bytes
(4.415 MiB), 2,861,622 (2.729 MiB; 38.2% reduction), 2,947,504 after native
monitoring, and 2,986,929 (2.849 MiB) after pruning, all under the original cap.
No compacted decoded expectation changed. Translation validation retained
release-helper assertions/formula output and used a 180-second aggregate native
test budget (96.89 seconds measured), without changing worker/17-second deadlines.
