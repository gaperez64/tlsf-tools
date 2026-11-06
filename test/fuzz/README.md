`roundtrip` decodes bytes into small TLSF specs and checks parse → print → parse
→ print byte equality. This checks canonical printing stability, not independent
semantic equivalence. Without allocation injection, NULL from parsing generated
or printed text aborts; no parser errno contract is assumed.

Replay all checked-in corpora with
`meson test -C build-fz-gcc --num-processes 1 fuzz-roundtrip fuzz-alloc fuzz-dpa`.
Build clang targets with `CC=clang CXX=clang++ meson setup build-fz-clang -Dfuzz=true`
and `ninja -C build-fz-clang -j 1`. Seeds contain decoder bytes named by their
SHA-1; keep generated artifacts in build directories. The decoder and replay main
each compile once; harnesses and shared DPA checks compile per mode (replay/fuzzer).
The allocation target links the library's
arena directly; no source-layout exception is needed.

`alloc` checks allocation failure through parsing, whole-objective conversion,
DPA construction and bounded successor exploration. Its first three bytes select
the phase (`byte[0] % 3`) and a little-endian allocation index (zero disables
indexed refusal). Bit 2 of byte 0 selects `allow_unproved`; remaining bytes go to
the shared decoder. Every input runs unarmed first. If no refusal fires, the armed
run must match its baseline's parse/conversion success and final DPA code/reason.
A fired refusal permits NULL or a documented DPA decline, without consulting errno.
Cleanup runs disarmed, and a caller-thread pointer registry checks that all armed
C heap allocations are freed. Registry exhaustion also refuses allocations.
`tlsf_convert` documents NULL for unsupported input/allocation failure; finite
semantics are one legitimate unarmed NULL result.

GNU ld wraps malloc/calloc/realloc/free and both public arena allocation entry
points. An injected arena refusal calls the real checked array allocator with an
overflowing size, marking the arena failed through its existing API. Heap wrappers
also cover new slabs. During DPA work only `oxidd_host_calloc` is injected/tracked,
as in `dpa_contract`/`native_api_failure`: every DPA C allocation uses that seam.
OxiDD's infallible Rust allocator and allocations hidden inside libc are outside
these wrappers; LeakSanitizer supplies the complementary leak check. The wrappers
work with ASan. Linux/GNU ld is required; other platforms skip `alloc`. Harness
snapshot allocations and sticky-failure probes run disarmed.

`dpa` consumes one leading `allow_unproved` bit, then decoder bytes. It explores
reachable states in BFS order, validates label DAGs (both children, cycles and AP
ranges), checks priorities, and evaluates every row over every assignment of at
most eight APs. Three-color memoization validates shared label children once per
context; value memoization evaluates each label at most once per assignment.
Label IDs have no assumed ordering. Storage grows by the largest encountered ID;
the public API has no label-count accessor. Each letter must match exactly one
edge. The converted AST, a postorder neutral formula DAG made from that AST, and
the converted parse/print/parse spec are independently self-checked. No library
AST-to-neutral-DAG exporter exists.

Both targets use 64 states, 4 MiB C host storage, 4096 BDD nodes, 1024 cache entries,
no deadline/cancellation, and the library's one-worker OxiDD manager. Thus only
UNSUPPORTED, STATE_LIMIT, HOST_LIMIT, BDD_LIMIT and PRIORITY_LIMIT may decline;
HOST_LIMIT is permitted because max_host_bytes is set. OK requires reason NONE.
Other codes, NONE-with-DECLINED, DEADLINE, CANCELLED and unknown reasons abort.
The formula-DAG exporter has a 4096-record/256-depth harness limit; label traversal
has a 256-depth limit. Harness storage/depth exhaustion ends inspection.

Shared checks compare every alphabet name against the supplied input-then-output
partition, including unused declarations. After every successor request, including
declines, state_count must respect max_states. Declines must persist in status and
in a later request, which must again publish an empty row. Copies of all returned
rows and all inspected label nodes, plus borrowed alphabet names, check that prior
outputs remain readable and unchanged after later work, including decline.

These oracles follow `include/tlsf/dpa.h`: constructors copy the partition, failures
publish NULL, observed failures are sticky, successful rows are whole/nonempty/
disjoint/complete, and IDs/borrowed rows/names/nodes survive until context free.
The contract does not promise equal graphs, priorities or row order across
constructions. There is no cross-construction structural or language-equivalence
oracle, nor any deadline, cancellation, foreign allocator or Buchi check.

The corpus has 47 `roundtrip`, 37 `alloc` and 17 `dpa` seeds. It covers finite
rejection, both admission modes, eight APs, delayed equalities reaching the state
limit, unsupported syntax, and bus/definition/bounded expansion. The F2 campaign
witness is `alloc/2ded5dfeb4389047799fb8f29774ee8ade90d60f` (unaltered campaign bytes).
It segfaulted with the original injector before the grammar fix and passes with
both the original injector and the public-API wrappers after the fix.
A separate parser-only sweep (`build-fz-gcc/review-parser-sweep.{c,py,log}`)
refused all 3347 allocation positions across 55 generated, enum, guarded-definition
and printer sources; every refusal returned NULL and released tracked storage.

F3 is `alloc/efb619532ad1f5aa1e9eee965554088417712d9d` (the original 17 bytes).
In the original GCC replay, refusal 45 failed `node_x` inside bounded-G
expansion of `X(G[0:2]((X true) U true))`. Expansion left `ok` true and published
a NULL formula; `wrap_signal_aps` crashed on its first visit to that root.
This witness does not revisit a shared operator. Expansion now propagates OOM,
checks bounded results before metadata writes, and publishes only valid roots.
Target adaptation separately defers all child/root replacements until every
allocation succeeds, stopping at the first failure. Thus failure leaves all six
sections untouched, even for caller-built DAGs with shared operators.

`target_adaptation` compares 532 conversions against explicitly single-shifted
formulas with matching semantics/target (which bypass adaptation). Both the
original and fixed GCC binaries pass. It covers G/F ranges, nested bounds,
indexed/zero next, nullary/parameterized/guarded definitions and pattern guards,
range/set/formula-valued big operators, indexed buses, all six sections separately
and together, both timing
directions and strict semantics. Expansion rebuilds operator nodes per occurrence
but reuses scalar APs/constants, including definition and big-operator leaves;
indexed bus accesses create fresh AP nodes. Bounded metadata also aliases a body,
but adaptation does not traverse metadata. Shared leaves are never mutated, so
these parsed constructs did not double-wrap. `objective_alloc` additionally
checks a shared NOT operator within AND and across all six lists: each AP must
have exactly one X on success (the inline golden is `!X p && !X p`), and every
refused allocation must leave every original slot intact. It also sweeps expansion
failures for F3, indexed X, F and G.

Sibling audit: `expand.c` needed the root-publication/failure-propagation fixes.
Its substitution builds fresh nodes rather than rewriting source children.
`nnf.c`, `rewrite.c`, `ast_api.c`'s lowercase clone, and `section_pattern.c`'s
formula builder likewise build fresh results and reject failure before publishing
them; their source trees retain their children. `normalize.c` was also inspected:
its formula passes rebuild nodes, while its prenormalization list writes are not
on the `tlsf_convert` path. No changes to those siblings were needed for this
in-place-mutation defect.

The checked-in coverage witness runs with both GCC and Clang:

```
meson test -C build-fz-gcc --num-processes 1 fuzz-witness-roundtrip fuzz-witness-alloc fuzz-witness-dpa
```

`CHECK(id, cond)` keeps the why-comment and `if (!(cond)) abort()` behavior.
Replay counts hits; `--witness R|A|D CORPUS` prints counts and fails for any
unreached check in that target (including shared C checks for alloc/dpa).
The shared ID inventory makes new checks participate automatically. Only replay
builds define `FUZZ_REPLAY`; libFuzzer compiles out recording and diagnostics.
This needs no compiler coverage flags or extra tools and runs in every normal
Meson suite. PR CI also runs just the three replays and three witnesses in a
separate Clang `-Dfuzz=true` job. A5/D9 now check that successor IDs name discovered states;
C6 checks the state budget. D5 duplicated the earlier C1 and was removed.

`mutants.json` records one exact one-line **library** mutation and seed SHA-1 per
remaining check, plus reasons for removed checks. Run manually after configuring
and building a GCC build:

```
python3 test/fuzz/mutants.py build-fz-gcc
```

The stdlib-only runner copies `src/lib` to a temporary directory, recompiles each
mutated source using the build's compiler flags, and relinks a temporary replay.
It never edits working-tree sources or archives. Each seed must pass the original
replay, then die by SIGABRT at its recorded check; another crash/check is a failure.
Compiler and replay diagnostics go to `BUILD/fuzz-mutants.log`. This slow check is
outside the default Meson suite.

`.github/workflows/fuzz.yml` runs weekly and via **Run workflow**: Clang builds all
fuzzers, checks the witnesses, then runs each target sequentially for 600 seconds
with a 2048 MiB RSS limit. GCC replays the grown corpora and checks the mutants.
Any finding fails the job; corpora, failing inputs and logs upload even on failure.
Both workflows set `UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1` for every
fuzzer and replay, so a UBSan diagnostic fails the job immediately.
Download the artifact to reproduce a finding with the corresponding plain replay.
