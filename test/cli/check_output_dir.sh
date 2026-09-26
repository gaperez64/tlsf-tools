#!/usr/bin/env bash
set -euo pipefail

expected="$1"
tool="$2"
shift 2

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
mkdir -p "$tmpdir/out"

"$tool" --output-dir "$tmpdir/out" "$@" > "$tmpdir/stdout"

if ! diff -u "$expected" "$tmpdir/stdout"; then
  echo "output-dir golden mismatch" >&2
  exit 1
fi
