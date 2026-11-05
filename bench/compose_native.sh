#!/bin/sh
# Measure completed native decomposition/solving; unresolved residuals exit 2.
set -eu
compose=$1
spec=$2
work=$(mktemp -d "${TMPDIR:-/tmp}/native-compose.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM
"$compose" --split --preprocess-policy always --output-dir "$work" "$spec"
sh "$work/compose.sh"
