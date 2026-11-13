# Generated-input property tests

`roundtrip` decodes bytes into small TLSF specifications and checks parse/print/parse/print byte equality. This checks printing stability, not semantic equivalence.

`alloc` injects allocation failures during parsing, conversion, DPA construction and successor exploration; it checks cleanup and compares results with an unarmed baseline when no refusal fires. It covers wrapped caller-thread C allocations, excludes OxiDD's Rust allocator, and requires Linux/GNU ld.

`dpa` checks the `dpa.h` contract per construction along the AST, neutral formula DAG and parse/print/parse paths, including labels, priorities, disjoint/complete rows, sticky declines and stability of borrowed data. It does not check cross-construction equivalence.

Both allocation and DPA tests use at most eight APs, 64 states, 4 MiB C host storage, 4096 BDD nodes and 1024 cache entries; unsupported inputs and budget limits may decline, and harness storage/depth exhaustion ends inspection.

`alloc` bytes: `byte[0] % 3` selects parsing/conversion/DPA (0/1/2); bit 2 sets `allow_unproved`; bytes 1 and 2 form a little-endian allocation refusal index (zero disables indexed refusal); bytes from offset 3 go to the decoder.

`dpa` bytes: bit 0 of byte 0 sets `allow_unproved`; bytes from offset 1 go to the decoder.

Run commands from the tlsf-tools root. Seeds under `test/fuzz/corpus/` are named by their SHA-1.

After the [source-build prerequisites](../../README.md#build), build GCC replays
and run the witnesses. Each witness replays its corpus once and fails if any
check remains unreached:

```sh
CC=gcc CXX=g++ meson setup build-fz-gcc
ninja -C build-fz-gcc -j 1 test/fuzz/fuzz-roundtrip-replay test/fuzz/fuzz-alloc-replay test/fuzz/fuzz-dpa-replay
meson test -C build-fz-gcc --num-processes 1 fuzz-witness-roundtrip fuzz-witness-alloc fuzz-witness-dpa
```

Build the libFuzzer targets with Clang (required for both C and C++), ASan and UBSan:

```sh
CC=clang CXX=clang++ meson setup build-fz-clang -Dfuzz=true
ninja -C build-fz-clang -j 1
```

With `-Dfuzz=true`, run `meson test -C build-fz-clang --num-processes 1 source_layout fuzz-witness-roundtrip fuzz-witness-alloc fuzz-witness-dpa`.
The layout check permits exactly the replay/libFuzzer harness owners. Sanitizer
builds of the full suite can exceed timeouts. The allocation target and witness
are Linux-only. Replay binaries also accept individual findings or directories
without `--witness`, as shown below; ordinary replay is not registered as a
second execution of the same seed corpus.

Run `python3 test/fuzz/mutants.py build-fz-gcc` to rebuild each `mutants.json` library mutation in a temporary copy and require its seed to abort at the recorded check. Diagnostics go to `build-fz-gcc/fuzz-mutants.log`; this slow check is outside the default Meson suite.

`.github/workflows/fuzz.yml` runs weekly and manually: Clang checks seeds and witnesses, then fuzzes each target sequentially for 600 seconds with a 2048 MiB RSS limit and a 30-second input timeout. GCC replays the grown corpora and runs the mutants; findings fail the job, and corpora, findings and logs upload even on failure.

Download and extract the `fuzz-corpora-and-findings` artifact. Set `target` to `roundtrip`, `alloc` or `dpa` and `input` to the extracted finding file, then run `ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 "build-fz-clang/test/fuzz/fuzz-$target-replay" "$input"`.
