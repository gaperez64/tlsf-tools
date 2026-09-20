# Peak-Memory Comparison

This experiment measures process peak resident memory (RSS) for the five
issue-24 safety games. It compares two release builds at identical capacities,
using automatic OxiDD GC, one solver process at a time, and three repetitions.
It measures the whole solve, including parsing, BDD construction, fixed points,
strategy extraction, serialization, and teardown. It does not measure the peak
number of live BDD nodes or attribute memory to individual phases.

## Variants

Both builds start from tlsf-tools commit
`b9405aec61e1f1bdf918e448cddf0902a5e86268` and use the same existing OxiDD static
library, whose dependency revision is
`9158645e51ab03b44355aff222fb39aec4d0a0f8`. Compiler and Meson settings match.

- **optimized**: the PR's solver at that commit.
- **baseline**: that same source with
  [corrected-eager-baseline.patch](corrected-eager-baseline.patch) applied. It
  retains the construction roots until cleanup, materializes conjunction before
  existential quantification, uses a checked equivalence BDD for convergence,
  and finishes the fixed point before testing the initial state.

This is a controlled ablation of those four optimizations, not unmodified
`main`. Both variants retain property/profile interpretation, allocation and
reset checks, field-wise memo identity, per-root conversion memo lifetimes,
and bounds checks. The conversion changes are retained as correctness repairs;
their memory effect is not measured by this comparison. The baseline reports
an allocation failure if its equivalence BDD cannot be built. Optional pressure
GC is disabled in both variants, so its effect is also outside this comparison.

## Reproduction

From a checkout containing the experiment files and built OxiDD artifacts,
create two source worktrees. Set `repo` to that checkout's absolute path and
`trial` to a new directory:

```sh
repo=$(pwd)
trial=/tmp/tlsf-memory-reproduction
mkdir -p "$trial"
git worktree add --detach "$trial/optimized" b9405aec61e1f1bdf918e448cddf0902a5e86268
git worktree add --detach "$trial/baseline" b9405aec61e1f1bdf918e448cddf0902a5e86268
git -C "$trial/baseline" apply "$repo/experiments/oxidd-memory/corrected-eager-baseline.patch"
for variant in baseline optimized; do
  mkdir -p "$trial/$variant/external/oxidd"
  ln -s "$repo/external/oxidd/target" "$repo/external/oxidd/build" \
    "$trial/$variant/external/oxidd/"
  meson setup "$trial/$variant-build" "$trial/$variant" \
    --buildtype=release -Db_ndebug=true -Dresearch_tools=true \
    -Doxidd=enabled -Dcpu=x86-64-v2
  meson compile -C "$trial/$variant-build" tlsfsolve aiger_roundtrip
  meson test -C "$trial/$variant-build" aiger_roundtrip \
    tlsfsolve_real tlsfsolve_legacy_unnamed_output tlsfsolve_unreal \
    tlsfsolve_multi_bad_explicit tlsfsolve_multi_bad_auto_refuses
done
python3 scripts/fetch_syntcomp_issue24.py --out "$trial/corpus"
python3 scripts/measure_tlsfsolve_memory.py \
  --solver "baseline=$trial/baseline-build/tlsfsolve" \
  --solver "optimized=$trial/optimized-build/tlsfsolve" \
  --corpus "$trial/corpus" --out "$trial/results" \
  --nodes 8388608 16777216 33554432 --cache 4194304 \
  --repetitions 3 --timeout 120
```

The runner validates the pinned input blobs and fingerprints each executable.
Every timed command explicitly selects `legacy-safety` and `--oxidd-gc=auto`.
It alternates variant order between adjacent pairs and repetitions. No solver
processes or builds run concurrently during the campaign; caches are not
explicitly flushed. There is no warmup exclusion. These settings are intended
for a local comparison, not a claim of general benchmark performance.

GNU time 1.9 records Linux `ru_maxrss` using `%M` in KiB (1024 bytes), along with
wall/user/system time and page faults. It wraps GNU `timeout` and the solver so
timeouts also retain resource measurements. The small timeout process is in
the measured process tree; the Python runner and subsequent model checking
are not. Resource accounting is fresh for every timed process. The reported
MiB values divide KiB by 1024; reserved node capacity is not a byte count.

Raw per-run data are written to `runs.jsonl`; `summary.json` contains median,
minimum, and maximum RSS and wall time for each variant/case/capacity. The
manifest records tools, binaries, input hashes, ordering, and parameters.
Each run keeps its strategy/stdout, stderr, exact command, and resource record.
Failures and timeouts must remain distinct from completed solves when comparing
memory. Successful strategies can be checked with `verify_aiger_safety.py`.
