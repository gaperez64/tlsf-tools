#!/usr/bin/env bash
# Golden-output regression check.
#
#   check.sh EXPECTED_FILE BINARY [ARGS...]
#
# Runs `BINARY ARGS...`, captures stdout, and diffs it byte-for-byte against
# EXPECTED_FILE.  Exits non-zero (printing a unified diff) on any mismatch.
set -euo pipefail

expected="$1"
shift

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

"$@" > "$tmp"

if ! diff -u "$expected" "$tmp"; then
  echo "golden mismatch for: $*" >&2
  exit 1
fi
