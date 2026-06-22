#!/bin/sh
# Fail only the full-residual policy_profitable_skip call.  Per-cluster calls
# still delegate to the regular fake ltlsynt, exercising fallback-mode auto's
# retry path without depending on a real backend failure.
outs=""
for a in "$@"; do
  case "$a" in
    --outs=*) outs=${a#--outs=} ;;
  esac
done

if [ "$outs" = "g,h" ] || [ "$outs" = "h,g" ]; then
  exit 2
fi

exec "$(dirname "$0")/fake_ltlsynt.sh" "$@"
