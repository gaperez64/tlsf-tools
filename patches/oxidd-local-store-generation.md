# OxiDD index manager: retire GC threads and identify local stores by lifetime

Upstream base: `9158645e51ab03b44355aff222fb39aec4d0a0f8`.
Patch: `oxidd-local-store-generation.patch`.

## Symptom

A process that creates and drops many index based BDD managers on the same
caller thread can leave a manager's GC thread alive after the caller drops its
last reference. In a real certificate checker that constructs a fresh manager
for each check, repeated checks on one thread occasionally recurse indefinitely
in BDD `apply_bin` and abort at the stack guard page. The pinned archive failed
19 of 200 same thread checker runs on the affected certificate. Disabling only
`prepare_local_state()` passed 200 of 200 runs, which implicates the local
allocation path; that experiment does not by itself identify the exact bad slot.

## Minimal reproduction

The added Rust test `bdd::manager_lifetime_tests::repeated_manager_lifetimes_on_one_thread`
creates, uses, and drops 1,000 BDD managers on one test thread. On Linux it
records the GC task ID of each manager while alive and asserts that task has
exited after `drop(manager)` returns, allowing a short bounded poll for `/proc`
to remove a task entry after `pthread_join`. Against the upstream manager source, it
fails immediately with `GC thread outlived manager lifetime 0`; with this patch
it passes. Run it with:

```sh
cargo test -j 1 --offline -p oxidd --lib repeated_manager_lifetimes_on_one_thread -- --exact bdd::manager_lifetime_tests::repeated_manager_lifetimes_on_one_thread
```

The independent C reproducer in `tlsf-tools/test/oxidd_manager_lifetime.c`
creates and destroys 1,000 managers, then separately calls `tlsf_gr1_check`
300 times on the same thread using the recorded certificate fixture. Both
loops are registered in Meson test. On Linux, the manager loop also asserts
that each manager's GC task ID has exited when unref returns. This assertion
fails on the pinned unpatched archive and passes with the patch. The 300-check
workload passed one unpatched run, so it remains useful workload coverage but
is not a deterministic standalone detector of this race.

## Cause in 9158645

`crates/oxidd-manager-index/src/manager.rs:203-229` stores the current `Store`
address and allocation slots in thread local `LOCAL_STORE_STATE` but has no
store lifetime identifier. `prepare_local_state()` at `manager.rs:515-529`
selects a store using only whether the thread local address is zero; node
allocation at `manager.rs:538-540` recognizes a store by address alone. An
allocator can reuse that address after the previous store is freed, allowing
old slot indices to appear to belong to a new store. In addition,
`ManagerRef::drop` at `manager.rs:1995-2004` only signals `Quit`; it does not
wait for the GC thread. Its startup/wait loop at `manager.rs:2244-2262` can
also miss a `Quit` sent before the thread first waits.

## Change

Give every store a monotonically assigned generation and require both address
and generation to match when using a thread local slot cache. Reset the cache
when a new lifetime selects a reused address, and retire it even when a guard
has no pending slots. Count `ManagerRef` instances atomically, separate from
the GC thread's own `Store` reference, so concurrent final reference drops
cannot both miss retirement. Save the GC thread handle, check for a preexisting
`Quit` before waiting, and join the thread at final manager reference release.
Take the handle out of its mutex before joining, because GC can drop a
transient `ManagerRef` as it exits.

## Test

The Rust test fails against the original manager source and passes with this
patch. A second Rust test drops final references concurrently. The C manager
loop fails against the unpatched archive at the GC
retirement assertion; both C loops pass with the patched archive. Run
`meson test -C build-native2 --num-processes 1` after building the patched
archive with `scripts/build_oxidd.sh`. In `tlsf-tools`, the full serial Meson
suite passed 298 of 298 tests. The C loops also passed when the test translation
unit was built with Clang AddressSanitizer; LeakSanitizer was disabled because
the test sandbox prevents its ptrace based scan. The Rust archive itself was
not sanitizer instrumented.
