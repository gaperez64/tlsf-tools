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
patch="$root/patches/oxidd-local-store-generation.patch"
patch_info="$oxidd/build/oxidd-patch-info.txt"
archive="$oxidd/target/release/liboxidd_ffi_c.a"
upstream_commit=be2f69bd704a4b9baf993fe54ff92c7ca17bb177

if [ ! -f "$crate/Cargo.toml" ]; then
  echo "build_oxidd: $crate not found; run 'git submodule update --init" \
       "--recursive external/oxidd' first" >&2
  exit 1
fi

if [ "$(git -C "$oxidd" rev-parse HEAD)" != "$upstream_commit" ]; then
  echo "build_oxidd: expected OxiDD $upstream_commit" >&2
  exit 1
fi
if [ ! -s "$patch" ]; then
  echo "build_oxidd: missing $patch" >&2
  exit 1
fi
patch_sha=$(sha256sum "$patch" | cut -d ' ' -f 1)
patch_record="oxidd-$upstream_commit+gc-retirement+$patch_sha"
patched_source_matches() {
  git -C "$oxidd" diff | cmp -s - "$patch"
}

if [ "${1:-}" = "--verify" ]; then
  if ! git -C "$oxidd" apply -R --check "$patch" 2>/dev/null ||
     ! patched_source_matches ||
     [ ! -f "$patch_info" ] ||
     [ ! -s "$archive" ] ||
     [ ! -s "$incdir/capi.h" ]; then
    echo "build_oxidd: archive/header or recorded OxiDD patch is stale; run scripts/build_oxidd.sh" >&2
    exit 1
  fi
  archive_sha=$(sha256sum "$archive" | cut -d ' ' -f 1)
  if [ "$(cat "$patch_info")" != "$patch_record+archive-$archive_sha" ]; then
    echo "build_oxidd: OxiDD archive differs from recorded patch build; run scripts/build_oxidd.sh" >&2
    exit 1
  fi
  exit 0
fi
if [ "$#" -ne 0 ]; then
  echo "usage: scripts/build_oxidd.sh [--verify]" >&2
  exit 2
fi

# A reverse applicability check makes a second invocation idempotent. A partial
# or conflicting edit must fail here, rather than silently building upstream.
if git -C "$oxidd" apply -R --check "$patch" 2>/dev/null; then
  echo "build_oxidd: patch already applied"
else
  git -C "$oxidd" apply --check "$patch" || {
    echo "build_oxidd: GC-retirement patch does not apply cleanly" >&2
    exit 1
  }
  git -C "$oxidd" apply "$patch"
fi
if ! patched_source_matches; then
  echo "build_oxidd: patched source differs from $patch" >&2
  exit 1
fi

mkdir -p "$incdir"
cargo build -j 1 --release --locked --manifest-path "$crate/Cargo.toml"
cbindgen --output "$incdir/capi.h" "$crate"
printf '/* C-only OxiDD config (no C++ extras) */\n' > "$incdir/config.h"
archive_sha=$(sha256sum "$archive" | cut -d ' ' -f 1)
printf '%s+archive-%s\n' "$patch_record" "$archive_sha" > "$patch_info"

echo "build_oxidd: built $oxidd/target/release/liboxidd_ffi_c.a and $incdir/capi.h"
