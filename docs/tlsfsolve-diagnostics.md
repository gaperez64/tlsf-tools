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
