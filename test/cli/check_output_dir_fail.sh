#!/usr/bin/env bash
set -euo pipefail

pattern="$1"
tool="$2"
shift 2

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
mkdir -p "$tmpdir/out"

set +e
out="$("$tool" --output-dir "$tmpdir/out" "$@" 2>&1)"
status=$?
set -e

if [ "$status" -eq 0 ]; then
  echo "expected output-dir command to fail: $tool $*" >&2
  exit 1
fi

if ! grep -Eq "$pattern" <<<"$out"; then
  echo "pattern '$pattern' not found in output of: $tool $*" >&2
  echo "$out" >&2
  exit 1
fi
