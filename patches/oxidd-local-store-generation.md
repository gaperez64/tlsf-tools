# OxiDD GC thread retirement on upstream main

Upstream checkout: `be2f69bd704a4b9baf993fe54ff92c7ca17bb177`.
Patch: `oxidd-local-store-generation.patch` (filename retained for build-script continuity).

Upstream commit `9fd1ed0278f69b235d6f87b87a414c64c4ab6026` fixes the stale
`current_store` address: `LocalStoreStateGuard::drop` now clears it even when
there are no preallocated slots. The former local generation and slot-cache
changes are therefore absent from this rebased patch.

Upstream main still lets the index manager's GC thread outlive the last caller
reference. `ManagerRef::drop` checks an `Arc` count but does not wait for that
thread, and a `Quit` sent before the thread's first wait can be missed. On the
unmodified `be2f69b` checkout, the C same-thread manager loop aborted on its
first run because the old GC task was still alive after `drop(manager)`. The
Rust `repeated_manager_lifetimes_on_one_thread` regression failed at lifetime
zero. One unmodified 300-check C checker run passed; that workload is useful
coverage but is not a deterministic detector of GC retirement.

The patch counts external `ManagerRef`s separately from the GC thread's `Arc`.
The final external drop signals `Quit` and joins the GC thread. The GC worker
uses a `Store` `Arc` directly, checks an already pending `Quit` before waiting,
and keeps the existing local-store guard around collection. The Rust tests
exercise repeated same-thread manager creation and concurrent final drops.

Validation on this machine used a temporary offline dependency substitution:
upstream's exact Cargo.lock requires uncached crates and crates.io DNS is
unavailable. The temporary build substituted a local `dashu-int` implementation
only for its integer-conversion API, downgraded the derive crate to cached
`syn` 2 with its one corresponding source adjustment, and resolved compatible
cached crate versions. Those changes were restored before saving the patch;
only `manager.rs` and the Rust lifetime tests in `bdd.rs` differ from upstream.
The lifetime regressions do not use the integer-conversion API. Rebuild from
the original upstream lockfile once the exact crates are available for a fully
reproducible release archive.

With the rebased patch, both Rust lifetime tests passed, as did ten consecutive
C manager runs and ten consecutive C checker runs (300 checks per run). The
full serial Meson suite passed 300/300 tests with a doubled per-test timeout;
the 80-game certificate checker took 196 seconds. The Clang ASan/UBSan native
API selection passed 8/8 tests, including the manager and checker lifetime
modes. Lift and reduction differential tests passed in the full suite.

Regression commands (one job, serial):

```sh
cargo test -j 1 -p oxidd --lib manager_lifetime_tests
build-native4/oxidd_manager_lifetime manager "$PWD"
build-native4/oxidd_manager_lifetime checker "$PWD/test/fixtures/oxidd-manager-lifetime"
```
