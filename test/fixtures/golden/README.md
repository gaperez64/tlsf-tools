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
  python3 tools/golden/regenerate.py --build build --spot "$HOME/spot-2.16-install"
```

`--only` selects an individual batch. Every external reference invocation has
a 60-second deadline. `skipped.json` records censored cases; tests do not
silently skip new timeouts. Regeneration checks reference results before
writing expectations. Review fixture changes as changes to the test oracle.
There is no environment variable or test option that records new expectations.

| Former oracle | Golden/in-house check |
| --- | --- |
| Lazy DPA full-language comparison | Canonical ASTs and 512 reference membership bits per formula; in-house max-odd parity evaluation; all valuations independently check each state's deterministic, complete transition partition |
| Random and Delta₂ generation/filtering | Committed historical fixed-seed corpora, including all 360 Delta₂ formulas and complements/mixed skeletons |
| Native reduction/Python differential | Both exact/strict reductions of the fixture corpus and generated naming/decline cases; complete AAG, typed provenance, symbol maps and metadata snapshots |
| Native reduction language | Eleven complete objectives on 52 fixed lasso words each, evaluated directly on the native AAG |
| Monitor encoding/game/controller checks | Cross-size provenance, component lasso memberships, fallback construction, exact/strict difference, native solver verdicts and certificates, 40 alpha pairs, explicit universal controller verification, output/latch mutations and invalid interfaces |
| Optional Stage C external differential | Pinned native lift results/evidence/artifacts on generated families, renamed twins and the committed parametric corpus |
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
