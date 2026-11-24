# Generated-input tests

`roundtrip` checks parse/print/parse/print byte stability, not semantic equivalence.

`alloc` injects caller-thread C allocation failures during parsing, conversion and DPA exploration, checking cleanup and baseline agreement when no refusal fires. It excludes OxiDD's Rust allocator and requires Linux/GNU ld.

`dpa` checks labels, priorities, complete/disjoint rows, sticky declines and borrowed-data stability along AST, formula-DAG and parse/print paths. It does not check equivalence between constructions.

Allocation/DPA limits are eight APs, 64 states, 4 MiB host storage, 4096 BDD nodes and 1024 cache entries. Unsupported inputs and exhausted budgets may decline.

`alloc` bytes: `byte[0] % 3` selects parsing/conversion/DPA; bit 2 enables `allow_unproved`; bytes 1/2 are a little-endian refusal index (zero disables it); decoder input starts at offset 3. For `dpa`, bit 0 enables `allow_unproved` and decoder input starts at offset 1. Seeds under `test/fuzz/corpus/` are named by SHA-1.

From the repository root, after the [build prerequisites](../../README.md#build), build GCC replays and require every witness check to be reached:

```sh
CC=gcc CXX=g++ meson setup build-fz-gcc
ninja -C build-fz-gcc -j 1 test/fuzz/fuzz-roundtrip-replay test/fuzz/fuzz-alloc-replay test/fuzz/fuzz-dpa-replay
meson test -C build-fz-gcc --num-processes 1 fuzz-witness-roundtrip fuzz-witness-alloc fuzz-witness-dpa
```

For libFuzzer, ASan and UBSan, use Clang for both C and C++:

```sh
CC=clang CXX=clang++ meson setup build-fz-clang -Dfuzz=true
ninja -C build-fz-clang -j 1
```

Run `meson test -C build-fz-clang --num-processes 1 source_layout fuzz-witness-roundtrip fuzz-witness-alloc fuzz-witness-dpa`. Allocation tests are Linux-only; full sanitizer suites can exceed timeouts.

`python3 test/fuzz/mutants.py build-fz-gcc` rebuilds each `mutants.json` mutation in a temporary copy and requires its seed to abort at the recorded check. Logs go to `build-fz-gcc/fuzz-mutants.log`.

The weekly/manual fuzz workflow uploads `fuzz-corpora-and-findings`. Extract it, set `target` to `roundtrip`, `alloc` or `dpa` and `input` to a finding, then replay:

```sh
ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 "build-fz-clang/test/fuzz/fuzz-$target-replay" "$input"
```
