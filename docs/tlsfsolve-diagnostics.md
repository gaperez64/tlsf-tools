# tlsfsolve Developer Diagnostics

This guide is for maintainers investigating failures and for collecting useful
bug reports; it is not required for normal solver use. For memory tuning on the
five issue-24 files, use the measured
[recommended caps and peak RSS](../experiments/oxidd-memory/followup-report.md).
Recoverable BDD/host allocation failures point here from stderr. A process that
aborts inside an allocator cannot reliably print that hint.

`tlsfsolve` keeps normal strategy output quiet by default.  Diagnostic tracing is
available only in builds where `NDEBUG` is not defined:

```sh
git submodule update --init --recursive external/oxidd
scripts/build_oxidd.sh
meson setup build-oxidd-diagnose \
  -Dresearch_tools=true -Doxidd=enabled \
  --buildtype=debugoptimized -Db_ndebug=false
meson compile -C build-oxidd-diagnose
build-oxidd-diagnose/tlsfsolve --version
```

Run one failing instance with the diagnostic wrapper:

```sh
python3 scripts/diagnose_tlsfsolve.py \
  --solver build-oxidd-diagnose/tlsfsolve \
  --input /path/to/driver_c2y.aag \
  --out diagnosis-driver-c2y \
  -- --oxidd-nodes 8388608
```

The wrapper writes `manifest.json`, `stderr.log`, `summary.json`,
`summary.md`, and either `strategy.aag` or `stdout.txt`.  It does not copy the
input file into the bundle; the manifest records its SHA-256.  Trace timings are
diagnostic, not release-performance measurements.
Use a new output directory for each run. On systems with `wait4`, the wrapper
records that specific child's peak RSS (normalized to KiB), including on
timeout; it does not reuse cumulative usage from earlier runs. Signals,
timeouts, unfinished operations and partial trace lines remain separate in the
summary. A signal alone is not evidence of an OOM kill. Verdict-only success
uses `stdout.txt`, never a misleading empty strategy artifact. Share the
manifest, log and summaries after reviewing paths; keep strategies local.

Useful first request for issue #24:

> Please build with `--buildtype=debugoptimized -Db_ndebug=false`, then run
> `scripts/diagnose_tlsfsolve.py` on one failing issue-#24 instance using the
> same node/cache/GC settings that fail.  Use the original supplied AAG without
> renaming or stripping symbols.  These cases should resolve as
> `legacy-safety` with `O=1,B=C=J=F=0`, objective source ordinary output 0, and
> `forall_u_exists_c`.  Please send the manifest, stderr log and summary.

The node and cache budgets are independent:

```sh
build-oxidd-diagnose/tlsfsolve \
  --oxidd-nodes 8388608 \
  --oxidd-cache 4194304 \
  --game-profile=auto \
  failing.aag > strategy.aag
```

`--oxidd-gc=pressure --oxidd-gc-threshold=80` adds explicit GC checkpoints at
safe phase boundaries and before allocating operations. After a collection,
the policy waits 256 completed operation entries, or 4096 when the explicit
call removed nothing or less than 1% of the configured capacity. A changed
ownership phase rearms the checkpoint. This policy is independent of verbosity.
Both GC modes allow exactly one explicit collection and retry of a failed pure
BDD operation, keeping its original inputs alive. Variable addition,
substitution mutation and AIG insertion are never replayed. A zero GC return
does not prove that the arena is entirely live; another collection may be active.

Use `-vv` to log each operation before entering the FFI. The first failure
contains phase, operation ID and gate/control/iteration index. Phase records
include elapsed time and approximate stored-node samples; the sampled maximum
is not an exact live-node or internal transient peak. Construction records
count map references, not distinct reachable nodes. Session managers report
their actual configured node/cache capacities and reject conflicting overrides.
Rust allocator failures and existing aborting AIG allocation paths may still
terminate the process instead of returning a recoverable error.

## Exact Demand Construction

The existing GR(1) algorithm's pointwise combination of multiple fairness
assumptions is unsound: a forced alternating state satisfies both `GF s` and
`GF !s`, but incorrectly permits an impossible system goal. Until a separately
validated algorithm repair lands, more than one fairness assumption returns a
configuration error (exit 2), allowing composition callers to fall back. The
parser still preserves every fairness property. This restriction is a separate
correctness fix, not a memory optimization.

Safety profiles also accept `--oxidd-transitions=demand`. This builds only
updates in the current state predicate's complete BDD support, retaining the
accumulated updates and publishing a new immutable substitution when it grows.
The default remains `eager`. Every supported state variable gets its exact
update; this is not abstraction. Full synthesis explicitly builds any remaining
updates in the `strategy_updates` phase and preserves all controller latches.

`--realizability-only` skips extraction, emits no stdout, and prints
`REALIZABLE`/`UNREALIZABLE` to stderr with exit 0/1. Failures are exit 2, including
extraction failure after a winning region was found in full synthesis. Both
options reject GR(1). Library callers must use `solve_safety_oxidd_result()` for
verdict-only mode; the legacy strategy-returning interfaces reject that mode.
Compare full synthesis with full synthesis and verdict-only with verdict-only.

## Offline Corpus Suites

Fetch the five pinned files explicitly, then enable the optional offline tests:

```sh
python3 scripts/fetch_syntcomp_issue24.py --out build-issue24-corpus
meson configure build-oxidd-diagnose \
  -Dissue24_corpus="$PWD/build-issue24-corpus"
meson test -C build-oxidd-diagnose --suite issue24-correctness
meson test -C build-oxidd-diagnose --suite issue24-memory
```

The serial correctness suite checks the pins, headers, ownership, resets and
upstream verdicts at a 32M-node/4M-cache budget. Independent strategy proofs
remain the separate check below. The serial memory suite records GNU-time peak
RSS and failures at the historical 4M-node/4M-cache budget in build-local JSON;
capacity exhaustion is recorded, while crashes or changed successful verdicts
are errors. Ordinary tests do not download third-party files.

## Independent Closed-Loop Safety Check

For a `legacy-safety` game, verify the emitted controller against the original
game using external tools:

```sh
python3 scripts/verify_aiger_safety.py \
  --game /path/to/original-game.aag \
  --strategy /path/to/strategy.aag \
  --aiger-dir /path/to/aiger \
  --combine-aiger /path/to/combine-aiger \
  --abc /path/to/abc \
  --out check-result --timeout 120
```

The dependencies are [Armin Biere's AIGER utilities](https://github.com/arminbiere/aiger),
[SYNTCOMP's combine-aiger](https://github.com/SYNTCOMP/combine-aiger), and
[ABC](https://github.com/berkeley-abc/abc). They are optional and are not vendored.
The checker does not use tlsf-tools' parser, BDD implementation, or composition
code. It uses this pipeline:

1. `aigtoaig` validates both input files and normalizes their representation.
2. Interface checks require the controller outputs to match exactly the game's
   `controllable_` inputs. Controller inputs may only observe environmental
   inputs. Missing/duplicate names and `AIGER_NEXT_` aliases are rejected.
3. `aigmove -r` moves the game's ordinary error output 0 into the bad-property
   section, preserving its polarity.
4. `combine-aiger` connects the controller to the game by signal name. The
   original plant and the controller keep separate latches and reset values.
5. `aigtoaig` validates the composition and converts it to binary AIGER. Only
   environmental inputs and exactly one bad property may remain.
6. ABC's unbounded `pdr` checks that the bad property is unreachable.

`SAFE` (exit 0) means PDR proved safety for all environment input sequences.
`UNSAFE` (exit 1) means it found a counterexample. `UNKNOWN` or `ERROR` (exit 2)
is not a successful verification, including timeouts, tool failures, and missing
proof status. A new output directory is required to prevent stale proof
results from being reused. The directory contains normalized circuits, the
closed loop, per-step logs and commands, `proof.status`, and `result.json` with
SHA-256 fingerprints of inputs and tools. ABC startup scripts are disabled.

This checker currently accepts only legacy safety games with named input
signals and constant latch resets. It does not verify GR(1) liveness or certify
UNREALIZABLE results. `aigbmc` is useful for bounded bug finding and `aigsim` for
simulation or witness replay; neither alone proves unbounded safety.

Run the external-tool regression checks directly:

```sh
python3 test/check_aiger_safety.py \
  --aiger-dir /path/to/aiger \
  --combine-aiger /path/to/combine-aiger --abc /path/to/abc
```

Meson also registers `aiger_closed_loop` when these tools are on `PATH` during
configuration. The cases include a safe controller with private memory and
reset 1, an incorrect reset, a delayed safety violation, and invalid interfaces.
