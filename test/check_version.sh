#!/usr/bin/env bash
# Check that a program reports a precise git-derived version string.
#
#   check_version.sh PROGRAM EXE
set -euo pipefail

program="$1"
exe="$2"
pattern="^${program} ([0-9][0-9A-Za-z.+-]*|[0-9a-f]{7,40})(-dirty)?( [a-z_]+=[^ ]+)*$"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

"$exe" --version >"$tmp"
lines=()
mapfile -t lines <"$tmp"

if (( ${#lines[@]} != 1 )) || [[ ! "${lines[0]}" =~ $pattern ]]; then
  printf 'invalid version output from %s:\n' "$exe" >&2
  sed 's/^/  /' "$tmp" >&2
  printf 'expected pattern: %s\n' "$pattern" >&2
  exit 1
fi
