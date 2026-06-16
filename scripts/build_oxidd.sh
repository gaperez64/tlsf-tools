#!/bin/sh
# Build the vendored OxiDD C FFI: a static library plus the cbindgen-generated
# C header.  Mirrors external/AbsSynthe/build.sh: an optional, manual backend
# build so the default build/CI stay dependency-free (no Rust toolchain needed).
#
# Outputs (consumed by the meson -Doxidd feature):
#   external/oxidd/target/release/liboxidd_ffi_c.a
#   external/oxidd/build/include/oxidd/capi.h    (#include <oxidd/capi.h>)
#   external/oxidd/build/include/oxidd/config.h  (empty: C-only, no C++ extras)
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
oxidd="$root/external/oxidd"
crate="$oxidd/crates/oxidd-ffi-c"
incdir="$oxidd/build/include/oxidd"

if [ ! -f "$crate/Cargo.toml" ]; then
  echo "build_oxidd: $crate not found; run 'git submodule update --init" \
       "--recursive external/oxidd' first" >&2
  exit 1
fi

mkdir -p "$incdir"
cargo build --release --manifest-path "$crate/Cargo.toml"
cbindgen --output "$incdir/capi.h" "$crate"
printf '/* C-only OxiDD config (no C++ extras) */\n' > "$incdir/config.h"

echo "build_oxidd: built $oxidd/target/release/liboxidd_ffi_c.a and $incdir/capi.h"
