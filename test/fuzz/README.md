`roundtrip` decodes bytes into small TLSF specs and checks parse → print → parse → print byte equality.
This checks canonical printing stability, not independent semantic equivalence.
Replay the checked-in corpus: `meson test -C build-fz-gcc fuzz-roundtrip`.
Build clang targets: `CC=clang CXX=clang++ meson setup build-fz-clang -Dfuzz=true` then `ninja -C build-fz-clang -j 1`.
Seeds in `corpus/roundtrip/` contain decoder bytes named by their SHA-1; keep generated artifacts in build directories.
