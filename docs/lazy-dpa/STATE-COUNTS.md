# Full-expansion state counts

Measurement for [issue #78](https://github.com/gaperez64/tlsf-tools/issues/78),
1 November 2026. The [69 rows](STATE-COUNTS.tsv) are exactly `semml-only.list`
from the acacia-bonsai release `evidence-2026-10-27-otfpar`. Each name joins
once to `tests/suites/benchmarks/syntcomp26/tlsf-sources.tsv` at acacia-bonsai
`1571a87b05cdad26deb97ceb96e0f49b2129682b`. All 69 copied sources match that
checkout's official TLSF SHA-256 manifest. No replacement inputs or external automata were
used. “Complete” means a successful full automaton expansion.

| Tool / admission | Complete | Timeout | OOM | Declined | Error |
| --- | ---: | ---: | ---: | ---: | ---: |
| Lazy, default | 13 | 19 | 8 | 29 | 0 |
| Lazy, general | 22 | 17 | 7 | 23 | 0 |
| Owl 21.0, CLI default | 18 | 49 | 2 | 0 | 0 |
| Owl 21.0, lookahead 0 | 19 | 49 | 1 | 0 | 0 |

All 69 inputs ran in each of four configurations, for 276 isolated runs.
The original 207 results are unchanged. Lazy completed 24 inputs in at least
one mode; 13 also completed with Owl CLI default and 14 with lookahead 0.
At least one configuration completed 29 inputs; 40 have no count in this budget.
Default declines are 24 unsupported requests and five BDD limits; all 23 general
declines are BDD limits.

Ratios are **lazy states / Owl states**, separately for each admission mode,
using only pairs with two OK runs. Quartiles use linear interpolation at
`(n−1)p` (`statistics.quantiles(..., method="inclusive")`). A threshold counts
ratios at or below it: ≤1× means lazy has no more states than Owl.

Against Owl's CLI default (unlimited lookahead, `-1`):

| Lazy mode | Pairs | Q1 | Median | Q3 | Max | ≤1× | ≤2× | ≤10× |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Default | 4 | 1.32 | 5.50 | 13.47 | 24.93 | 0 | 2 | 3 |
| General | 12 | 5.81 | 50.48 | 71.07 | 76.67 | 2 | 3 | 4 |

Against Owl with lookahead 0:

| Lazy mode | Pairs | Q1 | Median | Q3 | Max | ≤1× | ≤2× | ≤10× |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Default | 4 | 1.30 | 2.33 | 5.75 | 12.99 | 0 | 2 | 3 |
| General | 13 | 1.21 | 6.08 | 6.31 | 6.85 | 3 | 4 | 13 |

Lookahead controls how many successor states Owl explores in advance when
choosing the parity structure. Unlimited (`-1`) uses exact semantic information;
zero uses sound approximations and can yield larger DPAs. Zero is the relevant
parity-transformation baseline for synthesis: it is the setting used by
[SemML](https://gitlab.com/live-lab/software/semml/-/blob/20ad6ec7/src/main/java/semml/smarterOwl/OwlUtil.java)
and [Strix](https://github.com/meyerphi/strix/blob/main/src/options.rs).
Only lookahead changes here. AP reordering and realizability simplification
are excluded because they change the AP order or objective; the measurements
therefore isolate this setting within the same Owl CLI pipeline.

Each baseline uses its own completed overlap; failed runs remain missing.
Notable cases:

- `robot-to-target-charging-unreal8.ltl`: general needs 16,715 states versus
  Owl CLI default's 218 (76.67×), the largest general ratio against that baseline.
  Lookahead 0 needs 2,707 (6.17×); default declines as unsupported.
- `robot-to-target-charging-unreal3.ltl`: general's 6,695 states versus Owl
  lookahead 0's 977 (6.85×) is the largest general ratio against that baseline.
- `robot_grid_pb_5_5_pe_.ltl`: default needs 16,278 states versus Owl's 653
  with unlimited lookahead (24.93×) or 1,253 with lookahead 0 (12.99×), the
  largest default ratio against either baseline. General needs 653 (1× / 0.52×).
- `collector_v1_pb_11_pe_.ltl`: general and Owl lookahead 0 both need 4,096
  states; Owl CLI default times out. This adds the thirteenth general pair.
- `lift_gr1_pb_7_pe_.ltl`: general's 26,992 states are the largest completed
  lazy count; default needs 18,462 and both Owl configurations time out.
- `ltl2dba_theta_pb_100_pe_.ltl`: both Owl configurations complete with 400
  states, while both lazy modes hit the memory cap.

## Method

`dpa_admission --expand --measure` uses the documented whole-objective path,
`tlsf_convert(text, "Mealy")`, and exports the actual lowercase AST passed to
`tlsf_dpa_create`. This includes TLSF expansion, assumption/guarantee assembly
and semantics/target adaptation. There is no extra normalization schedule,
decomposition, negation or second TLSF frontend. Both tools receive that same
objective over infinite words. There are 67 Mealy and two strict-Mealy sources;
all source and effective targets are Mealy. The system sees the current input
before choosing its output. Strict semantics are preserved in the assembled
objective; the source metadata is recorded per row.

The exporter quotes APs and parenthesises operator groups, flattening only
associative `&`/`|` groups. The explicit alphabet is inputs followed by outputs,
including unused declarations, in conversion order. Owl's CLI assigns APs by
first occurrence. Its input is `(false & "AP0" & ...) | OBJECTIVE`: the parser
visits all these APs, then its Boolean constructors discard the false disjunct.
`CheckOwlFormula.java`, linked to the official release jar, checked all 69:
this parses to exactly the same Owl formula as parsing the direct AST export
with the explicit alphabet. Owl drops trailing unused APs; its remaining
alphabet is an exact prefix of that order. This does not change the language
or the ownership of any signal. Source, direct-formula and alphabet hashes
are in the TSV; regenerated exports are checked after every run.

The original campaign ran default admission (`allow_unproved=false`), general
admission (`research`, `allow_unproved=true`), then Owl, serially per input.
The fourth configuration adds only `--SLM21-lookahead=0` to the same Owl command;
the original three configurations were not rerun. Every run has its own
`systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0`. The observer
checks the actual cgroup limits and kills the tool's process group at 120 s.
Wall time covers the tool process, including lazy conversion/export or Owl
parsing/HOA emission and process cleanup. If systemd's OOM policy also stops
the observer, the coordinator records its elapsed wall time and the retained
scope `Result=oom-kill`. OOM is checked using `memory.events` or that result.

The opt-in measurement mode removes the old 10,000-state, 512-MiB host and
ten-second caps. It uses 2^24 BDD nodes and a 2^16-entry cache; the library's
syntax, recursive-work and priority limits still apply. A BDD or other API
limit is `declined`, not a completed count. Ordinary `dpa_admission --expand`
keeps its documented budgets and output.

Lazy completion requires `tlsf_dpa_expand` to return OK: every reachable
state has a disjoint symbolic successor row covering all valuations. Both Owl
configurations run `ltl2dpa --complete` with the same default SLM21 translation,
simplifiers and fragment portfolio. `--complete` requests a total transition
relation, adding a rejecting sink if needed. Success requires exit zero and a
finished HOA with the `complete` and `deterministic` properties; states are counted from
its fully emitted reachable graph. Counts cover the reachable word-automaton
graph before splitting input/output moves into game positions.

`*_colours` records the declared priority range (lazy: maximum priority + 1;
Owl: HOA acceptance-set count); `*_used` counts distinct marks on reachable
edges. Both automata use transition acceptance. Lazy uses max-odd;
`owl_parity` records Owl's convention.
Unused priorities can make the two colour columns differ. Every unsuccessful
run has `NA` for states and colours, including a decline with partial progress.

Original validation passed: all 69 formula/alphabet checks, the 207-run raw-result
and resource audit, `dpa_contract`, `dpa_stage2`, and the ordinary `--expand` smoke
check. Pinned clang-format 22.1.8 and the proof-source reference check also passed.
All 69 added runs passed the command, resource and HOA-count audit. Original
raw results, formula exports and TSV columns are unchanged; all four completion
rows and both ratio tables agree with the TSV.

## Versions and hashes

The DPA and conversion implementation is tlsf-tools main
`3bf210a0ba7a36ef6b42984ddec567c99f7b0bda`. The measurement mode was added in
`3d9a2d6`, with the scope OOM fallback in `151deb3` and the zero-lookahead
configuration in `ceaaf1f`. OxiDD is the clean pinned submodule
`288a6efcf553f18fe4bf722635157f2453bb2618`. Build: GCC 15.3.1, Meson 1.8.5,
release configuration, baseline CPU, one build job. Host: Intel i3-8100T,
four cores, 7.6 GiB RAM, Linux 7.2.10. The measurement uses the unmodified
native [official Owl 21.0 release](https://github.com/owl-toolkit/owl/releases/tag/release-21.0).
Java 21 is used only for checking formulas.

SHA-256:

```text
2cda837c9c947eb33d4c8822d9267b2f3693cd7f69b92b001086563eb60ace41  otfpar-20261027.tar.gz
9fbc4007b18065296d592f14bd9ef0e9e95a4893a4d4477e0153013fa531f92f  tlsf-sources.tsv
00f3e4dbe0ea880cb6131a7b0ee5743fbe668b068b4d54246e078b2588999af2  owl-linux-amd64-21.0.zip
e93c0631ec94400f46597624faadb4798a3ceefeb608acee71c043e4c332c7f5  bin/owl
e85f53770886ca6da336fa2f77d507c0fa08c76ffbff0aed13e5cc342cc39973  owl-21.0.jar
0376a3c1d28da6138c3c578780408671d3a7ae18cb28c58621081e444d3a8e04  dpa_admission
bdcf58107ba1a499b25e3db205086767dd409d3f5ab12c90f2d429f55ec774a6  antlr4-runtime-4.8-1.jar
e6dd072f9d3fe02a4600688380bd422bdac184caf6fe2418cfdd0934f09432aa  guava-30.1-jre.jar
```

## Reproduce

Use this branch's helpers and the pinned acacia-bonsai checkout with its
materialized TLSF corpus. Start a new campaign with an empty `build-scratch-m/`;
resume an existing one with `run`, keeping its original build and inventory.
From the tlsf-tools worktree:

```sh
mkdir -p build-scratch-m/{downloads,evidence,checker-libs,tmp}
export TMPDIR="$PWD/build-scratch-m/tmp"
gh release download evidence-2026-10-27-otfpar --repo gaperez64/acacia-bonsai \
  --pattern otfpar-20261027.tar.gz --dir build-scratch-m/downloads
tar xzf build-scratch-m/downloads/otfpar-20261027.tar.gz \
  -C build-scratch-m/evidence _bm-logs.otfpar/semml-only.list
gh release download release-21.0 --repo owl-toolkit/owl \
  --pattern owl-linux-amd64-21.0.zip --dir build-scratch-m/downloads
unzip -q build-scratch-m/downloads/owl-linux-amd64-21.0.zip -d build-scratch-m
curl -fL https://repo.maven.apache.org/maven2/org/antlr/antlr4-runtime/4.8-1/antlr4-runtime-4.8-1.jar \
  -o build-scratch-m/checker-libs/antlr4-runtime-4.8-1.jar
curl -fL https://repo.maven.apache.org/maven2/com/google/guava/guava/30.1-jre/guava-30.1-jre.jar \
  -o build-scratch-m/checker-libs/guava-30.1-jre.jar
sha256sum build-scratch-m/downloads/* build-scratch-m/checker-libs/*.jar
git submodule update --init external/oxidd
meson setup build-scratch-m/build --buildtype=release
CARGO_BUILD_JOBS=1 meson compile -C build-scratch-m/build -j1 dpa_admission
python3 tools/dpa_state_counts.py prepare --acacia ../.. --corpus ../../tlsf-corpus
python3 tools/dpa_state_counts.py run
python3 tools/dpa_state_counts.py summarize
```

Compare the downloaded hashes above before running. Adjust only the two
acacia paths. `prepare` checks the exact 69-name join, official source hashes
and Owl formula/alphabet identity. `run` skips completed records when resumed.
To add only the fourth configuration to an existing three-configuration campaign,
use `python3 tools/dpa_state_counts.py run --tools owl_lookahead0`, then `summarize`.
Scratch contains copies, exports, full HOA, commands, resource observations and
raw results. Among measurement outputs, only the small TSV and this report
belong in git. Preparation refuses to overwrite measured runs.

The individual tool commands inside each scope are:

```sh
build-scratch-m/build/test/unit/dpa_admission --expand --measure default SOURCE PREFIX
build-scratch-m/build/test/unit/dpa_admission --expand --measure research SOURCE PREFIX
build-scratch-m/owl-linux-musl-amd64-21.0/bin/owl ltl2dpa --complete -i PREFIX.owl.ltl
build-scratch-m/owl-linux-musl-amd64-21.0/bin/owl ltl2dpa --complete --SLM21-lookahead=0 -i PREFIX.owl.ltl
```

The Python runner supplies the verified memory scope, external deadline,
status classification and missing-count policy. The runner and formula checker
live in `tools/`. No Meson targets or CI jobs were added; the DPA implementation
is unchanged.
