`roundtrip` decodes bytes into small TLSF specs and checks parse → print → parse
→ print byte equality. This checks canonical printing stability, not independent
semantic equivalence. Without allocation injection, NULL from parsing generated
or printed text aborts; no parser errno contract is assumed.

Replay all checked-in corpora with
`meson test -C build-fz-gcc --num-processes 1 fuzz-roundtrip fuzz-alloc fuzz-dpa`.
Build clang targets with `CC=clang CXX=clang++ meson setup build-fz-clang -Dfuzz=true`
and `ninja -C build-fz-clang -j 1`. Seeds contain decoder bytes named by their
SHA-1; keep generated artifacts in build directories. The decoder, replay main
and shared DPA checks each compile once. The allocation target links the library's
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

The corpus has 47 `roundtrip`, 36 `alloc` and 17 `dpa` seeds. It covers finite
rejection, both admission modes, eight APs, delayed equalities reaching the state
limit, unsupported syntax, and bus/definition/bounded expansion. The F2 campaign
witness is `alloc/2ded5dfeb4389047799fb8f29774ee8ade90d60f` (unaltered campaign bytes).
It segfaulted with the original injector before the grammar fix and passes with
both the original injector and the public-API wrappers after the fix.
A separate parser-only sweep (`build-fz-gcc/review-parser-sweep.{c,py,log}`)
refused all 3347 allocation positions across 55 generated, enum, guarded-definition
and printer sources; every refusal returned NULL and released tracked storage.

Fresh GCC gcov execution counts at every property check follow. Shared C counts
combine `alloc` and `dpa`; both unarmed and armed alloc runs contribute. Each check
is reached by the checked-in corpus. Reproduce from `build-fz-gcc` using
`/home/gperez/GIT-repos/acacia-bonsai/.venv/bin/python review-coverage.py`.
The script, `review-coverage.txt`, `review-coverage-build.log`, replay logs and
`review-{roundtrip,alloc,dpa,dpa_checks}.gcov.json.gz` are build artifacts. Only
ordinary replay mains run; coverage-guided clang executables are built separately.

| Check | Hits | Oracle |
| --- | ---: | --- |
| R1 | 47 | Decoder text parses |
| R2 | 47 | Printed text parses |
| R3 | 47 | Canonical printing is stable |
| A1 | 154 | DPA code/reason permitted by these budgets |
| A2 | 72 | Parsing succeeds unless a refusal fired |
| A3 | 6 | Creation failure publishes NULL |
| A4 | 1 | Expansion failure publishes an empty row |
| A5 | 54 | Discovered states respect the budget |
| A6 | 72 | Armed C allocations are freed |
| A7 | 36 | Unfired runs match their baseline result/status |
| A8 | 100 | Successful expansion publishes a nonempty row |
| D1 | 243 | DPA code/reason permitted by these budgets |
| D2 | 744 | Label DAGs are acyclic |
| D3 | 744 | Label/child IDs resolve to valid node kinds |
| D4 | 153 | Decision APs are in range |
| D5 | 45 | Copied alphabet count matches, at most eight |
| D6 | 3 | Declined expansion publishes an empty row |
| D7 | 192 | Successful rows are nonempty |
| D8 | 438 | Priorities respect the advertised maximum |
| D9 | 285 | Discovered states respect the budget |
| D10 | 3792 | Every assignment matches exactly one edge |
| D11 | 3 | Creation failure publishes NULL |
| D12 | 34 | Decoder and printer text parse |
| C1 | 392 | Copied partition count includes unused declarations |
| C2 | 1052 | Every copied and previously borrowed AP name matches |
| C3 | 1331 | Every inspected label resolves |
| C4 | 2258 | Previously borrowed rows survive later work |
| C5 | 1043 | Previously borrowed label nodes and IDs survive |
| C6 | 296 | Context state_count respects max_states after every request |
| C7 | 4 | Decline is reported by context status |
| C8 | 4 | Later requests retain the decline and empty row |
