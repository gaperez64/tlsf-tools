# tlsfsolve Diagnostics

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
safe phase boundaries.  It is observable in the trace and is separate from
OxiDD's automatic collection.

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
