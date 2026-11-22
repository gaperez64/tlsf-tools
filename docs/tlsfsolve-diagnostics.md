# tlsfsolve usage and diagnostics

`tlsfsolve` solves input-first Mealy AIGER games. Inputs prefixed
`controllable_` belong to the system. Auto mode accepts legacy safety
(one ordinary output, no B/C/J/F records) or GR(1) with singleton justice
records and a controllable input. Bad-only safety needs
`--game-profile=multi-safety`. Invariant constraints are unsupported.
In GR(1), bad records override ordinary outputs; absent bad records, one
ordinary output is unsafe, otherwise safety is true. Exit 0 writes a strategy
AAG to stdout; exit 1 prints `UNREALIZABLE` to stderr; failures exit 2.

## Memory and variable order

```sh
tlsfsolve --oxidd-var-order=fanin-dfs \
  --oxidd-nodes=4194304 --oxidd-cache=262144 game.aag > strategy.aag
```

Capacities count entries, not bytes; a node cap is not a process memory limit.
Defaults are `input-first` order, `gates` construction and automatic GC.
`fanin-dfs` can cost more; retry the default before raising capacities.
`state-first` is also available. `OXIDD_STACK_SIZE` overrides worker stack sizes,
which otherwise account for finite `RLIMIT_AS`.

Variable identities remain inputs, latches, then GR(1) auxiliaries.
`--oxidd-order-file PATH` lists each identity once:

```text
tlsfsolve-order-v1 N
2
0
1
...
```

The count must match local variables. A custom file conflicts with an explicit
named order; shared composition managers reject nondefault orders.
`--oxidd-gc=pressure --oxidd-gc-threshold=80` adds collection checkpoints.

Safety-only `--oxidd-transitions=demand` builds exact updates as predicate
support grows; default `eager` builds them upfront. Full synthesis still
preserves every controller latch. Safety-only `--realizability-only` skips
extraction/stdout, prints a verdict to stderr and exits 0/1; failures exit 2.
Both options reject GR(1). Library verdict-only callers use
`solve_safety_oxidd_result()`; legacy strategy-returning APIs reject that mode.

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

Use a new output directory. The bundle contains manifest, logs, JSON/Markdown
summaries and strategy/stdout. It hashes the input without copying it.
Review paths before sharing; keep strategies local. On systems with `wait4`,
peak RSS is the child's usage in KiB, including on timeout. A signal alone
does not establish OOM. Debug trace times are not release performance.

`-vv` logs operations before FFI entry; failures identify phase, operation ID
and gate/control/iteration index. Node samples are approximate. Allocator
aborts may terminate without a diagnostic. For bounded root traces and an
offline circuit-cone report:

```sh
python3 scripts/diagnose_tlsfsolve.py \
  --solver build-oxidd-diagnose/tlsfsolve --input game.aag --out diagnosis \
  -- --oxidd-var-order=fanin-dfs --oxidd-trace-gate=562 \
     --oxidd-trace-roots --oxidd-trace-node-limit=100000 \
     --oxidd-trace-scratch=16777216
python3 scripts/analyze_oxidd_cone.py game.aag --gate-index 562 --out cone.json
```

Trace switches are absent in `NDEBUG` builds. `complete=false` gives a lower
bound; scratch caps can lower the effective traversal limit. Cone analysis
needs no BDDs and does not estimate BDD size.

## Issue-24 corpus checks

```sh
python3 scripts/fetch_syntcomp_issue24.py --out build-issue24-corpus
meson configure build-oxidd-diagnose -Dissue24_corpus="$PWD/build-issue24-corpus"
meson test -C build-oxidd-diagnose --suite issue24-correctness
meson test -C build-oxidd-diagnose --suite issue24-memory
```

Ordinary tests download nothing. Retain original AAG symbols and reproduce
failing node/cache/GC settings. These five games use legacy safety, ordinary
output 0 and `forall_u_exists_c`. Correctness checks use 32M-node/4M-cache;
memory checks use historical 4M-node/4M-cache and record exhaustion separately
from crashes or changed successful verdicts.

## Independent safety verification

For named-input legacy-safety games with constant resets:

```sh
python3 scripts/verify_aiger_safety.py \
  --game /path/to/original-game.aag --strategy /path/to/strategy.aag \
  --aiger-dir /path/to/aiger --combine-aiger /path/to/combine-aiger \
  --abc /path/to/abc --out check-result --timeout 120
```

Install [AIGER utilities](https://github.com/arminbiere/aiger),
[combine-aiger](https://github.com/SYNTCOMP/combine-aiger) and
[ABC](https://github.com/berkeley-abc/abc). The checker validates names and
resets, connects plant/controller circuits, then runs ABC unbounded `pdr`.
It uses no tlsf-tools parser, BDD or composition code. Controller outputs must
match all controllable inputs; observations may contain only environment inputs.

`SAFE` exits 0; `UNSAFE` exits 1 with a counterexample; `UNKNOWN`/`ERROR` exit 2.
A new output directory stores circuits, logs, `proof.status`, and fingerprinted
`result.json`. This does not verify GR(1) liveness or UNREALIZABLE claims.

```sh
python3 test/oracle/check_aiger_safety.py --aiger-dir /path/to/aiger \
  --combine-aiger /path/to/combine-aiger --abc /path/to/abc
```

Meson registers `aiger_closed_loop` when the tools are on `PATH` at configuration.
