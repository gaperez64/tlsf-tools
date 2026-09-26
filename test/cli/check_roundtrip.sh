#!/bin/sh
set -eu

normalizer=$1
converter=$2
input=$3
output=$(mktemp "${TMPDIR:-/tmp}/tlsf-roundtrip.XXXXXX")
trap 'rm -f "$output"' EXIT HUP INT TERM

"$normalizer" --passes nnf "$input" >"$output"
"$converter" <"$output" >/dev/null
