#!/bin/sh
# Minimal AbsSynthe stand-in for the test suite.  It accepts `-o OUT SPEC`,
# reads controllable inputs from SPEC, and writes an ASCII strategy AIGER whose
# outputs are the same controllable names driven to constant true.

out=""
spec=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    -o|--out_file)
      out=$2
      shift 2
      ;;
    --out_file=*)
      out=${1#--out_file=}
      shift
      ;;
    -*)
      shift
      ;;
    *)
      spec=$1
      shift
      ;;
  esac
done

[ -n "$out" ] || exit 1
[ -n "$spec" ] || exit 1

ctrls=$(sed -n 's/^i[0-9][0-9]* \(controllable_[^[:space:]]*\)$/\1/p' "$spec")
no=$(printf '%s\n' "$ctrls" | grep -c .)

{
  echo "aag 0 0 0 $no 0"
  i=0
  while [ "$i" -lt "$no" ]; do
    echo 1
    i=$((i + 1))
  done
  i=0
  printf '%s\n' "$ctrls" | while IFS= read -r name; do
    [ -n "$name" ] || continue
    echo "o$i $name"
    i=$((i + 1))
  done
} > "$out"

exit 10
