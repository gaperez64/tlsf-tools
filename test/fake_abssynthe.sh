#!/bin/sh
# Minimal AbsSynthe stand-in for the test suite.  It accepts `-o OUT SPEC`,
# reads controllable inputs from SPEC, and writes a vanilla-looking strategy:
# the original `bad` output plus comments mapping replacement gates back to
# controllable input names.

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

envs=$(sed -n 's/^i[0-9][0-9]* \([^[:space:]]*\)$/\1/p' "$spec" | grep -v '^controllable_')
ctrls=$(sed -n 's/^i[0-9][0-9]* \(controllable_[^[:space:]]*\)$/\1/p' "$spec")
ni=$(printf '%s\n' "$envs" | grep -c .)
no=$(printf '%s\n' "$ctrls" | grep -c .)
m=$((ni + no))

{
  echo "aag $m $ni 0 1 $no"
  i=1
  while [ "$i" -le "$ni" ]; do
    echo $((i * 2))
    i=$((i + 1))
  done
  echo 0
  i=0
  while [ "$i" -lt "$no" ]; do
    lhs=$(((ni + i + 1) * 2))
    echo "$lhs 1 1"
    i=$((i + 1))
  done
  i=0
  printf '%s\n' "$envs" | while IFS= read -r name; do
    [ -n "$name" ] || continue
    echo "i$i $name"
    i=$((i + 1))
  done
  echo "o0 bad"
  echo "c"
  i=0
  printf '%s\n' "$ctrls" | while IFS= read -r name; do
    [ -n "$name" ] || continue
    lhs=$(((ni + i + 1) * 2))
    echo "controllable-gate $lhs $name"
    i=$((i + 1))
  done
} > "$out"

exit 10
