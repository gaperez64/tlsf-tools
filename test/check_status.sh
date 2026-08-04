#!/usr/bin/env bash
# Exact exit-status/stdout/stderr regression check.
#
#   check_status.sh STATUS EXPECTED_STDOUT EXPECTED_STDERR COMMAND [ARGS...]
set -uo pipefail

expected_status="$1"
expected_stdout="$2"
expected_stderr="$3"
shift 3

actual_stdout="$(mktemp)"
actual_stderr="$(mktemp)"
trap 'rm -f "$actual_stdout" "$actual_stderr"' EXIT

"$@" >"$actual_stdout" 2>"$actual_stderr"
status=$?

if [ "$status" -ne "$expected_status" ]; then
  echo "expected exit $expected_status, got $status: $*" >&2
  exit 1
fi
if ! diff -u "$expected_stdout" "$actual_stdout"; then
  echo "stdout mismatch for: $*" >&2
  exit 1
fi
if ! diff -u "$expected_stderr" "$actual_stderr"; then
  echo "stderr mismatch for: $*" >&2
  exit 1
fi
