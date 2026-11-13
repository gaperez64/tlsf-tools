#!/usr/bin/env bash
# Asserts that the combined stdout+stderr of a command matches an extended
# regex (grep -E).  Used for normalization-stats smoke checks whose exact
# numeric/timing output is not worth pinning to a byte-identical golden.
#
#   check_contains.sh STATUS PATTERN BINARY [ARGS...]
set -uo pipefail
expected="$1"
shift
pat="$1"
shift
out="$("$@" 2>&1)"
status=$?
if [ "$status" != "$expected" ]; then
  echo "expected status $expected, got $status from: $*" >&2
  echo "$out" >&2
  exit 1
fi
if ! grep -Eq "$pat" <<<"$out"; then
  echo "pattern '$pat' not found in output of: $*" >&2
  echo "$out" >&2
  exit 1
fi
exit 0
