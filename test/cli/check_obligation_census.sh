#!/bin/sh
# The obligation census must keep a stable schema and count a two-client
# arbiter correctly: two response obligations of one family, both triggered by
# input propositions, and one pair that can be pending together.
set -eu

tool=$1
case_file=$2

output=$("$tool" --format obligations --split "$case_file")
header=$(printf '%s\n' "$output" | sed -n '1p')
row=$(printf '%s\n' "$output" | sed -n '2p')

# Header and row must agree in width, or every downstream reader misaligns.
test "$(printf '%s\n' "$header" | awk -F '\t' '{print NF}')" \
   = "$(printf '%s\n' "$row" | awk -F '\t' '{print NF}')"

field() { printf '%s\n' "$row" | awk -F '\t' -v n="$1" '{print $n}'; }
expect() {
  if [ "$(field "$1")" != "$3" ]; then
    printf 'obligation census: %s = %s, expected %s\n' "$2" "$(field "$1")" "$3" >&2
    exit 1
  fi
}

expect 1  schema_version               1
expect 3  obligation_count             2
expect 4  indexed_obligation_count     2
expect 5  obligation_types             1
expect 6  max_family_size              2
expect 11 persistent_trigger_count     2
expect 12 coactivation_candidate_count 1

# --no-header must drop exactly the header and nothing else.
bare=$("$tool" --format obligations --no-header --split "$case_file")
test "$(printf '%s\n' "$bare" | wc -l)" = "1"
test "$(printf '%s\n' "$bare")" = "$row"
