#!/bin/sh
set -eu

normalizer=$1
converter=$2
input=$3
output=$(mktemp "${TMPDIR:-/tmp}/tlsf-roundtrip.XXXXXX")
reprinted=$(mktemp "${TMPDIR:-/tmp}/tlsf-roundtrip.XXXXXX")
trap 'rm -f "$output" "$reprinted"' EXIT HUP INT TERM

"$normalizer" --passes nnf "$input" >"$output"
"$converter" <"$output" >/dev/null
# NNF re-emission must be a printing fixed point, not merely parseable.
"$normalizer" --passes nnf "$output" >"$reprinted"
diff -u "$output" "$reprinted"
