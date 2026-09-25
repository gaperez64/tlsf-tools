#!/bin/sh
set -eu

script=$1
tlsfnorm=$2
tlsf2ltl=$3
tlsfinfo=$4
tlsfbenchgraph=$5
automata_generator=$6
case_file=$7
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT HUP INT TERM

python3 "$script" --output "$temporary/bundle" --schedule 'off=|' \
  --orientation real --tlsfnorm "$tlsfnorm" --tlsf2ltl "$tlsf2ltl" \
  --tlsfinfo "$tlsfinfo" --tlsfbenchgraph "$tlsfbenchgraph" \
  --automata-generator "$automata_generator" "$case_file"

awk -F '\t' '
  NR == 1 {
    for (i = 1; i <= NF; i++) col[$i] = i
    if (!col["generation_status"] || !col["states"]) exit 1
  }
  NR == 2 {
    if ($1 != 2 || $(col["generation_status"]) != "ok" ||
        $(col["states"]) < 1) exit 1
  }
' "$temporary/bundle/automata.tsv"

awk -F '\t' '
  NR == 1 {
    for (i = 1; i <= NF; i++) col[$i] = i
    if (!col["guard_nodes"] || !col["spec_id"]) exit 1
    if (col["file"] || col["solved_blocks"] || col["formula_size_raw"]) exit 1
  }
  NR == 2 {
    if ($1 != 2 || $(col["guard_nodes"]) < 1) exit 1
  }
' "$temporary/bundle/source-features.tsv"
