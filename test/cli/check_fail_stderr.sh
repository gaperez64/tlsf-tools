#!/usr/bin/env bash
# Golden stderr regression check for commands expected to fail.
#
#   check_fail_stderr.sh EXPECTED_FILE BINARY [ARGS...]
set -euo pipefail

expected="$1"
shift

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

set +e
"$@" > /dev/null 2> "$tmp"
status=$?
set -e

if [ "$status" -eq 0 ]; then
  echo "expected failure but command succeeded: $*" >&2
  exit 1
fi

if ! diff -u "$expected" "$tmp"; then
  echo "stderr golden mismatch for: $*" >&2
  exit 1
fi
