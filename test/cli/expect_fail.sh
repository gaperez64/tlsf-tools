#!/usr/bin/env bash
# Asserts that the given command exits non-zero (an expected failure).
#
#   expect_fail.sh BINARY [ARGS...]
set -uo pipefail

if "$@" > /dev/null 2>&1; then
  echo "expected failure but command succeeded: $*" >&2
  exit 1
fi
exit 0
