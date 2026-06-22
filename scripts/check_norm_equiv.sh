#!/usr/bin/env bash
# Soundness gate: assert that normalizing a TLSF spec preserves its LTL meaning.
# Skips (exit 0) when Spot's ltlfilt is unavailable, so it is a no-op in CI.
#
#   check_norm_equiv.sh TLSFNORM TLSF2LTL SCHEDULE SPEC
set -uo pipefail
tlsfnorm="$1"
tlsf2ltl="$2"
schedule="$3"
spec="$4"

if ! command -v ltlfilt >/dev/null 2>&1; then
  echo "ltlfilt not found; skipping equivalence check" >&2
  exit 0
fi

tmp="$(mktemp --suffix=.tlsf)"
trap 'rm -f "$tmp"' EXIT
if ! "$tlsfnorm" --passes "$schedule" "$spec" >"$tmp"; then
  echo "tlsfnorm failed for $schedule on $spec" >&2
  exit 1
fi

orig="$("$tlsf2ltl" "$spec")"
norm="$("$tlsf2ltl" "$tmp")"
if ltlfilt --equivalent-to="$orig" -f "$norm" >/dev/null 2>&1; then
  exit 0
fi
echo "NOT equivalent: $schedule on $spec" >&2
echo "  orig: $orig" >&2
echo "  norm: $norm" >&2
exit 1
