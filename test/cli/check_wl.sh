#!/usr/bin/env bash
# Golden check that normalizes embedded TLSF paths to basenames, so goldens are
# independent of the (absolute) paths meson passes.
#   check_wl.sh EXPECTED BINARY [ARGS...]
set -euo pipefail
expected="$1"; shift
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
"$@" | sed -E 's#[^ ]*/([^ /]+\.tlsf)#\1#g' > "$tmp"
if ! diff -u "$expected" "$tmp"; then
  echo "golden mismatch for: $*" >&2
  exit 1
fi
