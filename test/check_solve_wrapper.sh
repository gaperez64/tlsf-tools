#!/usr/bin/env bash
set -euo pipefail

expected="$1"
solve_script="$2"
tlsfcompose="$3"
solver="$4"
spec="$5"

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

"$solve_script" \
  --tlsfcompose "$tlsfcompose" \
  --solver "$solver" \
  --work-dir "$tmpdir/work" \
  --output "$tmpdir/strategy.aag" \
  "$spec"

if ! diff -u "$expected" "$tmpdir/strategy.aag"; then
  echo "solve wrapper golden mismatch" >&2
  exit 1
fi
