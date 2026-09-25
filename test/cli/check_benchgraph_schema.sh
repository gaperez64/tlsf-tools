#!/bin/sh
set -eu

tool=$1
case_file=$2
output=$($tool "$case_file")
header=$(printf '%s\n' "$output" | sed -n '1p')
row=$(printf '%s\n' "$output" | sed -n '2p')

header_fields=$(printf '%s\n' "$header" | awk -F '\t' '{print NF}')
row_fields=$(printf '%s\n' "$row" | awk -F '\t' '{print NF}')
test "$header_fields" = "$row_fields"

printf '%s\n' "$output" | awk -F '\t' '
  NR == 1 {
    for (i = 1; i <= NF; i++) col[$i] = i
    if ($2 != "schema_version") exit 1
    next
  }
  NR == 2 {
    if ($2 != "2" || $3 != "ok") exit 1
    if ($(col["guard_nodes"]) != $(col["formula_size_raw"])) exit 1
    if ($(col["guard_temporal_ops"]) < 1) exit 1
    if ($(col["guard_max_depth"]) < $(col["guard_max_temporal_depth"])) exit 1
  }
'

test "$($tool --schema-version)" = 2

source_output=$($tool --source-features "$case_file")
printf '%s\n' "$source_output" | awk -F '\t' '
  NR == 1 {
    for (i = 1; i <= NF; i++) col[$i] = i
    if (!col["guard_nodes"] || !col["inputs"] || !col["outputs"]) exit 1
    if (col["template_candidates"] || col["formula_size_raw"]) exit 1
    next
  }
  NR == 2 {
    if ($2 != "2" || $3 != "ok" || $(col["guard_nodes"]) < 1) exit 1
  }
'

if $tool --source-features --split "$case_file" >/dev/null 2>&1; then
  exit 1
fi
