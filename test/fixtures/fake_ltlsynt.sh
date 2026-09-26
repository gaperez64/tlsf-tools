#!/bin/sh
# Minimal ltlsynt stand-in for the test suite: parses --ins=/--outs= and emits a
# trivial REALIZABLE strategy (every output driven to constant true) as ASCII
# AIGER.  This exercises wrapper merge paths deterministically without
# depending on a real ltlsynt (CI has none).
ins=""
outs=""
for a in "$@"; do
  case "$a" in
    --ins=*) ins=${a#--ins=} ;;
    --outs=*) outs=${a#--outs=} ;;
  esac
done

# Count inputs / outputs (comma-separated, possibly empty).
count() {
  [ -z "$1" ] && { echo 0; return; }
  printf '%s' "$1" | tr ',' '\n' | grep -c .
}
ni=$(count "$ins")
no=$(count "$outs")

echo REALIZABLE
echo "aag $ni $ni 0 $no 0"
i=1
while [ "$i" -le "$ni" ]; do
  echo $((i * 2))
  i=$((i + 1))
done
k=0
while [ "$k" -lt "$no" ]; do
  echo 1 # output := constant true
  k=$((k + 1))
done
# symbol table
i=0
IFS=,
for n in $ins; do
  echo "i$i $n"
  i=$((i + 1))
done
i=0
for n in $outs; do
  echo "o$i $n"
  i=$((i + 1))
done
