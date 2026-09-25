# OxiDD index-manager GC thread retirement

The submodule is pinned to OxiDD `be2f69bd704a4b9baf993fe54ff92c7ca17bb177`.
`oxidd-gc-thread-retirement.patch` is byte-for-byte the diff from that revision
to commit `d174f65` in [OxiDD PR #49](https://github.com/OxiDD/oxidd/pull/49).
The PR fixes [OxiDD issue #37](https://github.com/OxiDD/oxidd/issues/37).

The unpatched index manager can leave its GC worker alive after the last caller
handle is dropped. A `Quit` signal sent before the worker first waits can also
be missed. Repeated same-thread creation and destruction can then reuse a stale
thread-local store address and abort.

The patch counts external manager and function handles separately from the GC
worker's `Store` reference. The last external drop signals `Quit` and waits for
the worker to finish. The worker checks for an early `Quit`, announces `Exited`,
and releases its store reference. A handle created inside a GC callback may
revive a zero external count; that transition is synchronized with the worker's
exit check so the worker stays alive. A final drop on the worker itself signals
retirement without joining itself. A joining drop propagates a worker panic
unless it is already unwinding.

The PR also moves the Rust lifetime regressions into
`oxidd-manager-index/src/manager_lifetime_tests.rs`, adds the
`oxidd-rules-bdd` test dependency, and records that dependency in `Cargo.lock`.
The five Rust tests cover repeated lifetimes, concurrent final drops, a final
drop during GC, callback revival, and a transient handle dropped on the worker.
The C `oxidd_manager_lifetime` regression covers manager and certificate
checker lifetimes through the FFI.

`scripts/build_oxidd.sh` applies this patch and records its SHA-256 together
with the archive SHA-256. Its `--verify` mode checks the exact patched source,
including the new Rust test file, plus the archive and build record. The OxiDD
CI cache key hashes the patch, so changing it creates a new cache key; both
consumer jobs apply the patch before configuring Meson.

When an OxiDD release contains this fix, move the submodule to that release
and delete the patch, its build-time application, and its build-info record.
