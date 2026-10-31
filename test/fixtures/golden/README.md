# Golden integration fixtures (issue #97, phase 1)

Generated on **2026-10-31** from `7b44d9f` on `chore/remove-spot`, before
changing the library's monitor implementation. The library still links its
existing backend in this phase. Exact tool versions are in `tool-versions.json`.
The reference installation was `$HOME/spot-2.16-install` (Spot **2.16**).

Regeneration is deliberately outside the build and CI:

```sh
PKG_CONFIG_PATH="$HOME/spot-2.16-install/lib/pkgconfig" \
  meson setup build -Dresearch_tools=true
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  env CARGO_BUILD_JOBS=2 meson compile -C build -j2
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  python3 tools/golden/regenerate.py --build build --spot "$HOME/spot-2.16-install" \
    --bindings-site build/reference/spot-python --oracle-root build/reference/prototype
```

`--only` selects an individual batch. Prepare the references using the Task Q
commands below before running the full command. Every reference invocation has
a deadline. Mandatory independent confirmations fail on timeouts; otherwise
`skipped.json` records censored cases; tests do not
silently skip new timeouts. Regeneration checks reference results before
writing expectations. Review fixture changes as changes to the test oracle.
There is no environment variable or test option that records new expectations.

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
| Review-4 exports | Original verdicts, complete scripts and cluster files, exact partitions, lowercase-collision guards and wrapper refusals |
| Normalization equivalence | Complete normalized TLSF and both objectives; reference equivalence confirmed with `ltlfilt --equivalent-to=ORIGINAL -f NORMALIZED` |
| API visitor/string equivalence | Complete visitor, string-API and cluster/partition exports, confirmed with the reference equivalence checker |
| Pinned `8b158d7` runtime rebuild | Complete native API/CLI outputs, artifacts and check reports confirmed by the passing pre-change differential; eliminates the old checkout's transitive Python oracle probe |

Reference verdicts use `ltlsynt --realizability --ins=... --outs=... -f FORMULA`
or `ltlfsynt --realizability --semantics=Mealy|Moore ...`. Infinite Moore
reference games use the complemented Mealy dual (negated objective, exchanged
players). `tools/golden/reference.cc` uses the same version's parser,
translation and word intersection to compute independent membership bits.
Automaton snapshots come from the pre-rewrite library, whose monitors are
constructed by Spot 2.16. Native verdicts are also checked by `tlsfcertcheck`.

The DPA generator retains seeds 31415, 27182 and 20852 and the historical
random-generation/filter commands verbatim. Lasso words and memberships are
committed, so the running suite needs no random formula generator. Bounded
membership is regression evidence, not an unbounded equivalence proof. The
historical full-language research oracle and manual Π₂ search remain isolated
under `tools/golden/`; neither is registered with Meson.

The `ltlsynt` route names in existing `.route_stats` fixtures and backend
commands in emitted script snapshots are the current product's output format.
They are compared as data. The deterministic wrapper protocol stub is
`test/fixtures/fake_backend.sh`; it invokes no synthesis tool. `bench/bench.sh`
only measures native work and explicitly refuses external fallback.

Fault injection for the current library's monitor types lives in
`src/lib/gr1_reduction_test_hooks.hh`, under the existing test-only macro.
Contract tests still exercise every fault; the library's normal code and
dependency/link configuration are unchanged.

## Final independent confirmation (Task Q)

On 2026-10-31 the entire frozen reduction and lift corpora were compared again
with the retired independent implementations used by `origin/main` (`7b44d9f`).
All **436** exact/strict reductions agreed: **320 successes** and **116 declines**
(86 native unsupported and 30 native invalid-input statuses). Successful
reductions passed the original circuit-function/reachable-bisimulation,
ownership, symbol-map and legacy-provenance comparisons. The retired contract
compares supported/declined disposition; exact decline codes and diagnostic
spelling remain native snapshots.

All **13** lift cases agreed with the archived `acacia_lift` prototype:
**seven successful lifts** and **six declines**, with matching decline stages.
Successful cases passed the original seed-value, role-equivalence-class,
predicate-arity, method/verdict and exact certificate/policy Boolean-function
comparisons. No expected values changed and **no disagreements** were found.
`provenance.json` separates each suite's independently checked semantics from
native snapshot fields and binds the recorded payload with SHA-256.

The Python reducer and differential comparators live only under `tools/golden`.
The prototype is restored from Acacia commit
`b615c3c4c2dc1a2b13c035b62b115c0d1148a977` (immediately before its retirement).
Spot **2.16** Python bindings were compiled from the matching release sources
against `$HOME/spot-2.16-install`. This local libbddx binary has a different
build hash from the prototype's historical allowlist. The offline setup adds
that hash with a conservative **1024-variable** ceiling after checking every
variable number below that ceiling. This changes the environment allowlist,
not the reduction, lifting or Boolean comparison algorithms. The prototype's
required source/binary manifest is generated from the current build.

Reproduce the setup and independent confirmation, one heavy job at a time:

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

Regeneration refuses missing independent references, disagreements and timeouts
for these two suites before writing either their data or provenance. Reference
checks are also required for the other independently checked suites. The
historical `8b158d7` snapshot cannot be changed without restoring its historical
differential. `test_gates.py` runs the review's decline-everything mutant through
the real recorder: it is rejected at `aliases_v12.tlsf:exact`, and the existing
recording survives unchanged. Normal tests validate provenance hashes and the
original **4,629,524-byte** total-directory cap without invoking Spot.

Golden JSON now uses one compact record per line. All decoded expectations are
identical to the previous recording. This removes indentation overhead without
removing scenarios, fields or precision.

The universal certificate oracle is `test/gr1_one_step.c`, a standalone C
process linked only to OxiDD and platform libraries. It parses the game,
strategy and certificate AAGs and the certificate JSON sidecar itself. For each
goal it compiles the circuits into OxiDD functions and checks that the violation
predicate is unsatisfiable for every invariant state and uncontrollable input.
Checks cover reset membership, safety and transition equality, invariant
inductiveness, move predicates, goal counters and ordered fairness ranks,
including input-acceptance sampling. No solver internals or libtlsf parsers are
used. OxiDD handles are owned by a per-goal arena and released after each goal.
The hand-written Python BDD package has been deleted.

The 240-game explicit certificate differential retains its three original
mutation rejections and adds five calls that reject mutated AAGs through the
OxiDD helper (invariant, move, rank, game-state latch and goal-counter latch).
The first eight realizable random games cross-check the symbolic result with
exhaustive enumeration. A two-goal game with **36 state variables** exercises
universal checking over a domain too large for explicit enumeration.

The complete golden directory, including provenance and this README, shrank
from **4,629,524 bytes (4.415 MiB)** to **2,861,622 bytes (2.729 MiB)** (38.2%).
No decoded expectation changed. The offline gate checks passed three rejection
scenarios, and the helper also passed a long signal-name check.

Task Q's clean research/coverage run passed **385/385 tests** with zero
external-oracle command/import attempts. The certificate differential reported
240 games (130 realizable, 110 unrealizable), 44,990 exact predicate evaluations,
8,952 explicit one-step checks, three original and five symbolic mutations
rejected, plus two symbolic goal checks over the 36-variable game. CI-filtered
coverage is **82.0% lines (23,741/28,945)**, **95.8% functions (1,356/1,415)**,
and **58.3% branches (19,729/33,828)**. The full-tree clang-format check uses
**22.1.8**. All heavy work runs serially in the requested 5 GiB/no-swap scopes;
compilation uses at most two jobs.

## Validation recorded on 2026-10-31

The unchanged baseline passed **378/378** tests. The converted research build
passed **384/384**, with all Spot executables replaced by failing command
traps and a Python import hook rejecting `spot` and `buddy`. No trap was hit.
The full suite includes the original wrapper comment/AP regression using the
protocol stub, without executing generated compose drivers. CI's exact
clang-format **22.1.8** check passed across the source tree.

Coverage counters were deleted after golden generation and compilation, before
the full converted suite. Both measurements used the coverage job's exact
`gcovr` invocation, extracted from `.github/workflows/ci.yml`, with
`-Db_coverage=true -Dresearch_tools=true`. Local versions: GCC 15.3.1,
Meson 1.8.5, gcovr 8.6. Builds/tests used at most two jobs; every build, test,
coverage run and generation batch ran in the requested systemd scope with
`MemoryMax=5G` and `MemorySwapMax=0`.

| CI metric | Before | After |
| --- | --- | --- |
| Lines | 81.2% (23490/28913) | 82.0% (23741/28945) |
| Functions | 95.3% (1346/1412) | 95.8% (1356/1415) |
| Branches | 57.2% (19294/33758) | 58.3% (19728/33828) |

The fixture corpus contains **25 golden data files** (4,621,132 bytes), plus
this provenance note, `tool-versions.json` and `skipped.json`. It includes:

- 541 DPA reference rows × 512 words = 276,992 membership expectations;
  eight additional budget-limit ASTs; 72 fixed random and 360 Delta₂ formulas.
- 2,272 more reference memberships: 572 native-language, 1,280 component-monitor
  and 420 disjoint-assumption observations.
- 226 reference realizability verdicts and 63 complete export-directory
  snapshots containing 315 emitted files.
- 436 exact/strict native reduction cases: 320 successes, 86 unsupported and
  30 invalid-input results; 118 focused monitor reductions with 89 native
  solve/certificate checks; 13 lift cases, including seven successful generated
  or renamed cases and six pinned declines.

No registered scenarios were dropped and no generation cases timed out;
`skipped.json` is empty. The six lift corpus declines are included as checks:
`arbiter_on_inpchange_pb_2_pe_`, `arbiter_pb_2_pe_`, `arbiter_pb_3_pe_`, and
both `round_robin_arbiter_unreal2` cases report `seed_window: no stable index
axis`; `arbiter_pb_4_pe_` reports `schema: no bounded exact template`.
The manual full-language Π₂ research search was relocated to tools, retaining
its historical oracle independently of the build and CI.

After recording clean CI coverage, the relocated tools-only full-language DPA
oracle was built separately and passed the handwritten, 72-formula random and
360-formula Delta₂ corpora, with a 60-second cap per batch. It remains outside
Meson and CI.

## Phase 2: native reduction monitors (Task R)

The reduction now uses the in-house DPA component construction. Safety and
co-safety use Stage 1; recurrence uses the proved Stage 2 breakpoint grammar
and `HasTag Pi2`. Positive Boolean combinations use a deterministic Büchi
round: remember the residual positive acceptance formula after setting colours
seen in the round to true, then reset on completion. Infinitely many completed
rounds are equivalent to the original positive Boolean formula over infinitely
recurring colours. The incoming round mark is remembered in the state, as
required by the existing one-hot game encoder. The finite initial mark can be
chosen accepting to avoid an extra latch in common safety/response monitors.
The general parity construction retains its existing behavior.

C++ remains for the existing JSON/provenance, containers and signature code.
Formula values now own native AST views. Propositional comparisons use the
in-house symbolic classes; temporal provenance comparisons use the proved DPA
and an exact max-odd SCC emptiness check. Normalized provenance preserves
semantic constants and `G(a R b) = G(b)`, while recording the original
construction formula separately. Exact/strict encoding and the lifting
implementations are unchanged. The production reducer always passes the
zero-initialized, proved admission policy. The diagnostic inventory alone
measures `allow_unproved`; it does not enable it in the reducer.

The public API and four profiling stages remain unchanged. State limits bound
DPA discovery and all one-hot latches. A failed state expansion reports the
first excluded state as a lower bound; edge counts report materialized complete
rows, so an edge limit can be crossed by one complete row. Deadlines,
cancellation and RSS checks run cooperatively during symbolic work. Completed
monitors retain only their exported label DAG and names, releasing each
symbolic manager before constructing the next conjunct. The legacy
`fallback_monitor_count` metadata field remains present and is zero.

No library/default-Meson dependency, include or test oracle requires Spot.
Meson no longer
queries `libspot`, and `tlsf.pc` no longer requires it. The standalone example
is no longer registered with Meson. Existing external-driver commands and
historical format/route names remain product data for phase 3.

### Explicit expectation changes

Only **14 native reduction cases** (the seven specifications below, in both
exact and strict mode) change successful expectations to
`TLSF_GR1_REDUCE_UNSUPPORTED`. Successful reference artifacts were not
regenerated. `provenance.json` archives each replaced group, its reason and its
old monitor sizes. The provenance gate reconstructs the complete phase-1
payload and checks its original SHA-256, which also proves that every other
expectation is unchanged. Legacy backend diagnostics are checked by status
and category: native grammar/AP diagnostics replace the retired hierarchy and
parser wording, while their historical messages remain in the payload.

| Specification | Declined conjunct | Old monitor states | Reason |
| --- | --- | ---: | --- |
| `bounded_until.tlsf` | `G(go -> (p U q))` | 3 | U in a G body is outside the proved finite-window/F(window) grammar. |
| `definition-future.tlsf` | `G(p <-> F q)` | 4 | NNF polarity mixes F and G obligations in the body. |
| `delayed-definition-future.tlsf` | `G(X p <-> F q)` | 6 | The same mixed body, with a delayed output. |
| `ident_m_function.tlsf` | `G(b U (a & b))` | 3 | Until/strong-release beneath G is outside the proved body grammar. |
| `normalization_sickert2.tlsf` | `G(req -> (a U G F p))` | 5 | Nested U/GF is outside proved admission; research admission also declines it without the required syntactic Pi2 tag. |
| `precedence_v12.tlsf` | `(a U b) W c` | 5 | Weak until contains a liveness obligation, outside the proved components. |
| `route_norm_xgf.tlsf` | `X G F g` | 2 | X surrounds a recurrence component; default admission does not admit that wrapper. |

The decomposition suite changes **nine admission expectations** from success
to unsupported, retaining all independently recorded realizability verdicts:
`G(p <-> F q)` (four observations, old size 4), `G(X p <-> F q)` (one,
old size 6), `G(X X p <-> F q)` (one, old size **9**), and
`G(F q -> F p)` (three, old size **4**). These changes and the original payload
hash are also archived in `provenance.json`. Their mixed-polarity G bodies are
outside the proved grammar. No other golden expectation changes.

The wider inventory also declines the spare, currently unregistered
`test/oracle/env_lift_capacity.tlsf`: its master clause is
`G(r_m -> X((AND_i !g_i) U g_m))`, whose old monitor had **4 states**. The
unbounded until beneath G/X is outside the proved body grammar. This does not
change a registered golden; the active capacity test uses `env_lift_one.tlsf`.

### Corpus inventory

The inventory contains **217 checked-in TLSF files**: every file under `bench/`
and `test/`, including the spare capacity fixture. Both binaries use the same
sources, exact semantics, a 10,000-state cap, a 16 MiB artifact cap, and a
20-second process deadline. There are no censored timeouts. The baseline binary
is the phase-1 build at `cf33da9`; the rewritten binary is from a fresh build
configured with `PKG_CONFIG_PATH` unset, where `pkg-config --exists libspot`
fails.

| Corpus | Specs | Before | Proved default | Research admission/expansion |
| --- | ---: | ---: | ---: | ---: |
| `bench/` | 6 | 1 | 1 | 1 |
| `test/fixtures/cases/` | 198 | 142 | 135 | 141 |
| `test/fixtures/gr1_monitor_game/` | 6 | 6 | 6 | 6 |
| `test/fixtures/arbiter_simple.tlsf` | 1 | 1 | 1 | 1 |
| `test/oracle/` | 6 | 6 | 5 | 6 |
| **Total** | **217** | **156** | **148** | **155** |

The default loses **8/156 previously handled specs (5.1%)**. Research admission
recovers seven of those eight, leaving only `normalization_sickert2.tlsf`
declined; it remains disabled in production. Before/after invalid-input counts
remain **15**; unsupported counts change **46 -> 54**. Excluding the unused
capacity fixture, the static inventory is **155 -> 148 / 216**.
The frozen exact/strict reduction suite is **320 -> 306 / 436 successes**,
with **100 unsupported** and **30 invalid-input** outcomes after the rewrite.
All six monitor-game specifications and all 13 lift dispositions remain intact.

Across the **148 retained successes**, total monitor states change
**1,215 -> 1,231**. The per-specification state counts, declines, source hashes
and research results are recorded in `tools/analysis/nospot-phase2.json`.
Reproduce the inventory, one heavy job at a time:

```sh
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  python3 tools/analysis/gr1_corpus.py BUILD OUTPUT.json
# Pass the same 217 paths to the diagnostic, not to the production reducer:
find bench test -name '*.tlsf' -print0 | sort -z | \
  systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
    xargs -0 BUILD/test/unit/gr1_admission
```

The added `dpa_buchi_goldens` test checks all 541 frozen DPA formulas: **313**
admitted formulas each pass all **512** reference words (**160,256** additional
Büchi membership checks); **228** are declined. It also independently enumerates
all valuations of every expanded state's transition partition. Existing native
language memberships, component memberships, native verdicts, certificate and
controller mutation checks remain registered. Native snapshot comparisons now
allow state encodings to differ while checking their word languages, ownership,
source bindings, roles and symmetric signatures against the unchanged payloads.

### Phase-2 validation recorded on 2026-10-31

The fresh research/coverage build passed **386/386 tests**, including the new
Büchi corpus check, with no timeouts. The complete source-tree clang-format
**22.1.8** check passed. Coverage counters were removed after compilation and
before the full suite. The CI source filters, with the current build directory
selected to exclude the retired baseline build's counters, report:

| CI metric | Phase 1 | Phase 2 |
| --- | --- | --- |
| Lines | 82.0% (23,741/28,945) | **82.2% (24,205/29,430)** |
| Functions | 95.8% (1,356/1,415) | **96.0% (1,388/1,446)** |
| Branches | 58.3% (19,729/33,828) | **58.7% (20,374/34,707)** |

A second fresh build used **`research_tools=false`, C++23**, and no
`PKG_CONFIG_PATH`. All targets compiled, and **5/5 focused tests** passed:
C reduction limits, all 436 reduction goldens, all 13 lift cases, source layout,
and the no-external-oracle/dependency guard. `ldd` on the C++23 public client
contains neither the former backend nor its BDD runtime. Generated `tlsf.pc`
requires only `yyjson` privately, with the existing OxiDD/platform/C++ link
libraries. `bench/bench.sh --build build-r --runs 3 --check` passed all six
benchmark inputs without a regression.

All compilation, tests, inventory, benchmark and coverage work ran serially in
`systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0`, with at most
two build/test workers. The complete golden directory, including archived
phase-1 expectations and this note, is **2947504 bytes**, below its original
**4,629,524-byte** cap. No successful golden data was regenerated.
