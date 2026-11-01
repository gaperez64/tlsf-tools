# tlsfsolve usage and diagnostics

`tlsfsolve` solves AbsSynthe-style AIGER games. Ordinary inputs are
uncontrollable; `controllable_` inputs belong to the system. Safety games use
a `bad` output; GR(1) also supports AIGER 1.9 bad-state, `justice`, and
`fairness` records. Bad-state records are disjoined and override ordinary outputs.
Without them, exactly one ordinary output means legacy unsafe output;
zero/multiple outputs mean pure justice. Exit 0 writes a strategy AAG to stdout;
exit 1 prints `UNREALIZABLE` to stderr; exit 2 reports input, usage, or internal
OxiDD failure.

For memory-heavy games, try:

```sh
tlsfsolve --oxidd-var-order=fanin-dfs \
  --oxidd-nodes=4194304 --oxidd-cache=262144 game.aag > strategy.aag
```

Order, node arena, and cache can vary per run of the same binary. Capacities
count entries, not bytes; the node cap is not a process memory limit. Automatic
GC is default. `fanin-dfs` sometimes costs more; retry default `input-first`
before raising capacities. See [ordering measurements](../experiments/oxidd-ordering/report.md)
and the five pinned corpus files' [measured caps/RSS](../experiments/oxidd-memory/followup-report.md).
OxiDD sizes worker stacks to finite `RLIMIT_AS`; `OXIDD_STACK_SIZE` overrides it.
Manager creation failure returns an invalid manager instead of aborting.

## Collect a failure report

Tracing requires a build without `NDEBUG`:

```sh
git submodule update --init --recursive external/oxidd
meson setup build-oxidd-diagnose -Dresearch_tools=true \
  --buildtype=debugoptimized -Db_ndebug=false
meson compile -C build-oxidd-diagnose
build-oxidd-diagnose/tlsfsolve --version
python3 scripts/diagnose_tlsfsolve.py \
  --solver build-oxidd-diagnose/tlsfsolve \
  --input /path/to/driver_c2y.aag --out diagnosis-driver-c2y \
  -- --oxidd-nodes 8388608
```

Use a new output directory per run. The wrapper writes `manifest.json`,
`stderr.log`, `summary.json`, `summary.md`, and `strategy.aag` or `stdout.txt`.
It hashes the input without copying it; verdict-only success uses `stdout.txt`.
On systems with `wait4`, peak RSS is that child's usage in KiB, even on timeout.
Signals, timeouts, unfinished operations, and partial lines stay separate;
a signal alone does not establish OOM. Trace times are not release performance.
Share the manifest/log/summaries after reviewing paths; keep strategies local.
Recoverable BDD/host allocation errors link here, but allocator aborts cannot
reliably print a hint.

For the five issue-24 files, retain original AAG symbols and reproduce the
failing node/cache/GC settings. Expect `legacy-safety`, `O=1,B=C=J=F=0`,
ordinary output 0 as objective, and `forall_u_exists_c`. Node/cache budgets are
independent:

```sh
build-oxidd-diagnose/tlsfsolve --oxidd-nodes 8388608 \
  --oxidd-cache 4194304 --game-profile=auto failing.aag > strategy.aag
```

`--oxidd-gc=pressure --oxidd-gc-threshold=80` adds checkpoints at safe phase
boundaries and before allocations, independently of verbosity. After collection
it waits 256 completed operations, or 4096 if nothing or less than 1% of capacity
was removed; ownership-phase changes rearm it. Both GC modes allow one explicit
collection/retry of a failed pure BDD operation with original inputs alive.
Variable addition, substitution mutation, and AIG insertion are never replayed.
A zero GC return does not prove all nodes live: another collection may be active.

`-vv` logs operations before FFI entry. The first failure gives phase, operation
ID, and gate/control/iteration index. Phase timing/node samples are approximate,
not exact live/transient peaks; construction counts map references, not distinct
reachable nodes. Session managers report configured capacities and reject
conflicting overrides. Rust allocator failures and aborting AIG allocation paths
can still terminate the process.

## Variable order and circuit construction

Identities stay inputs, latches, then GR(1) auxiliaries.
`--oxidd-var-order=input-first|state-first|fanin-dfs` changes BDD levels before
projections/construction. Defaults are `input-first` and
`--oxidd-build-plan=gates`. A custom `--oxidd-order-file PATH` uses:

```text
tlsfsolve-order-v1 N
2
0
1
...
```

The count must match local variables and list each identity in `0..N-1` once.
It conflicts with an explicitly named order. Shared composition managers reject
nondefault orders because allocated variables cannot safely move.

```sh
python3 scripts/diagnose_tlsfsolve.py \
  --solver build-oxidd-diagnose/tlsfsolve --input game.aag --out diagnosis \
  -- --oxidd-var-order=fanin-dfs --oxidd-trace-gate=562 \
     --oxidd-trace-roots --oxidd-trace-node-limit=100000 \
     --oxidd-trace-scratch=16777216
python3 scripts/analyze_oxidd_cone.py game.aag --gate-index 562 --out cone.json
```

Trace switches are absent in `NDEBUG` builds. Traversal pins roots, counts
inner-node identities once, releases cofactors, and uses no GC. `complete=false`
is a lower bound; scratch caps may lower the effective limit. Gate events give
signed operands, input/state dependence, remaining uses, stored-node estimates,
and bounded operand/result counts. The offline cone report needs no BDDs;
it distinguishes source/parser-normalized ASCII AIGER indices, signed fan-outs,
root occurrences, and conservative fusion barriers `shared`, `root`,
`negative_edge`, `input_only_barrier`. It does not estimate BDD size.

GR(1) handles multiple fairness assumptions with separate inner greatest
fixpoints, disjoined at each least-fixpoint level; extraction retains `X[k,i]`.
Combining fairness negations pointwise would mishandle a forced alternating
state satisfying both `GF s` and `GF !s`, allowing an impossible system goal.

Safety-only `--oxidd-transitions=demand` builds exact updates for the current
predicate's complete BDD support, accumulating updates and publishing immutable
substitutions as support grows. Default `eager` builds them upfront. Full
synthesis completes `strategy_updates` and preserves every controller latch.
Safety-only `--realizability-only` skips extraction/stdout, prints
`REALIZABLE`/`UNREALIZABLE` to stderr, and exits 0/1. Failures exit 2, including
full-synthesis extraction failure after finding a winning region. Both options
reject GR(1). Library verdict-only callers need `solve_safety_oxidd_result()`;
legacy strategy-returning APIs reject it. Compare like modes when benchmarking.

## Offline checks

```sh
python3 scripts/fetch_syntcomp_issue24.py --out build-issue24-corpus
meson configure build-oxidd-diagnose -Dissue24_corpus="$PWD/build-issue24-corpus"
meson test -C build-oxidd-diagnose --suite issue24-correctness
meson test -C build-oxidd-diagnose --suite issue24-memory
```

Ordinary tests download nothing. The serial correctness suite checks pins,
headers, ownership, resets, and upstream verdicts at 32M-node/4M-cache.
The serial memory suite records GNU-time peak RSS/failures in build-local JSON
at historical 4M-node/4M-cache; exhaustion is recorded, crashes or changed
successful verdicts fail. Independent strategy proofs require the check below.

## Independent closed-loop safety verification

For a `legacy-safety` game:

```sh
python3 scripts/verify_aiger_safety.py \
  --game /path/to/original-game.aag --strategy /path/to/strategy.aag \
  --aiger-dir /path/to/aiger --combine-aiger /path/to/combine-aiger \
  --abc /path/to/abc --out check-result --timeout 120
```

Optional external dependencies are [AIGER utilities](https://github.com/arminbiere/aiger),
[combine-aiger](https://github.com/SYNTCOMP/combine-aiger), and
[ABC](https://github.com/berkeley-abc/abc); none is vendored. The pipeline uses
no tlsf-tools parser, BDD, or composition code:

1. `aigtoaig` validates and normalizes both inputs.
2. Controller outputs must exactly match game `controllable_` inputs; controller
   inputs may observe only environment inputs. Missing/duplicate names and
   `AIGER_NEXT_` aliases fail.
3. `aigmove -r` moves ordinary error output 0 to a bad property, preserving polarity.
4. `combine-aiger` connects by name, retaining separate plant/controller latches
   and resets.
5. `aigtoaig` validates the binary closed loop: only environment inputs and one
   bad property may remain.
6. ABC unbounded `pdr` proves the bad property unreachable; startup scripts are disabled.

`SAFE` exits 0 for all environment sequences; `UNSAFE` exits 1 with a
counterexample. `UNKNOWN`/`ERROR` exit 2, including timeout, tool failure, or
missing proof status. A new directory prevents stale results; it stores
normalized/closed-loop circuits, commands/logs, `proof.status`, and `result.json`
with input/tool SHA-256 fingerprints. Only named-input legacy safety games with
constant resets are supported. GR(1) liveness and UNREALIZABLE are not verified.
`aigbmc` finds bounded bugs and `aigsim` replays/simulates; neither proves
unbounded safety alone.

```sh
python3 test/oracle/check_aiger_safety.py --aiger-dir /path/to/aiger \
  --combine-aiger /path/to/combine-aiger --abc /path/to/abc
```

Meson registers `aiger_closed_loop` if tools are on `PATH` at configuration.
Cases cover private controller memory/reset 1, incorrect resets, delayed safety
violations, and invalid interfaces.
