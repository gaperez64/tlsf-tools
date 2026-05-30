#!/usr/bin/env bash
# Benchmark tlsf-tools against syfco: wall-clock time (median of N runs) and
# peak resident memory, over the specs in bench/specs/.
#
#   bench/bench.sh [--build DIR] [--runs N] [--baseline] [--check]
#
#   --baseline   write our numbers to bench/baseline.tsv
#   --check      compare our numbers to bench/baseline.tsv and fail on a
#                regression beyond the tolerance (TIME_TOL / MEM_TOL)
#
# With neither flag, prints a comparison table (ours vs syfco when available).
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"
build="$root/build"
runs=7
mode=report
# Time is machine-dependent (the committed baseline is from one host), so the
# time tolerance is generous and catches only gross algorithmic regressions;
# peak RSS is far more stable across machines.
TIME_TOL=3.0     # relative: flag above 3x the baseline median time
TIME_ABS_MS=500  # and absolute: only if also >500ms slower than baseline
MEM_TOL=1.5      # peak RSS is machine-independent: flag above 1.5x baseline

while [ $# -gt 0 ]; do
  case "$1" in
    --build) build="$2"; shift 2 ;;
    --runs) runs="$2"; shift 2 ;;
    --baseline) mode=baseline; shift ;;
    --check) mode=check; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

# median wall-clock in milliseconds of `runs` executions of "$@"
median_ms() {
  local times=() i start end
  for ((i = 0; i < runs; i++)); do
    start=$(date +%s%N)
    "$@" > /dev/null 2>&1
    end=$(date +%s%N)
    times+=($(((end - start) / 1000000)))
  done
  printf '%s\n' "${times[@]}" | sort -n | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}'
}

# peak resident set size in KiB of one execution of "$@"
peak_kib() {
  /usr/bin/time -v "$@" 2>&1 >/dev/null |
    awk '/Maximum resident/{print $NF}'
}

ours="$build/tlsf2ltl"
have_syfco=0
command -v syfco >/dev/null 2>&1 && have_syfco=1

mapfile -t specs < <(find "$here/specs" -name '*.tlsf' | sort)
[ ${#specs[@]} -gt 0 ] || { echo "no specs in $here/specs" >&2; exit 2; }

baseline="$here/baseline.tsv"

if [ "$mode" = report ]; then
  printf '%-28s | %10s | %10s | %10s | %10s\n' \
    spec "ours ms" "syfco ms" "ours KiB" "syfco KiB"
  printf -- '-%.0s' {1..86}; echo
fi

declare -A ms_of kib_of
fail=0

for spec in "${specs[@]}"; do
  name="$(basename "$spec" .tlsf)"
  o_ms=$(median_ms "$ours" "$spec")
  o_kib=$(peak_kib "$ours" "$spec")
  ms_of[$name]=$o_ms
  kib_of[$name]=$o_kib

  if [ "$mode" = report ]; then
    s_ms="-"; s_kib="-"
    if [ "$have_syfco" = 1 ] && syfco -f ltlxba "$spec" >/dev/null 2>&1; then
      s_ms=$(median_ms syfco -f ltlxba "$spec")
      s_kib=$(peak_kib syfco -f ltlxba "$spec")
    fi
    printf '%-28s | %10s | %10s | %10s | %10s\n' \
      "$name" "$o_ms" "$s_ms" "$o_kib" "$s_kib"
  fi
done

if [ "$mode" = baseline ]; then
  { echo -e "# spec\tms\tkib"
    for spec in "${specs[@]}"; do
      n="$(basename "$spec" .tlsf)"
      echo -e "$n\t${ms_of[$n]}\t${kib_of[$n]}"
    done
  } > "$baseline"
  echo "wrote baseline: $baseline"
fi

if [ "$mode" = check ]; then
  [ -f "$baseline" ] || { echo "no baseline ($baseline); run --baseline" >&2; exit 2; }
  printf '%-28s | %-22s | %-22s\n' spec "time ms (base->now)" "peak KiB (base->now)"
  printf -- '-%.0s' {1..78}; echo
  while IFS=$'\t' read -r n bms bkib; do
    [ "${n:0:1}" = "#" ] && continue
    nms=${ms_of[$n]:-}; nkib=${kib_of[$n]:-}
    [ -n "$nms" ] || continue
    # +1 ms floor avoids divide-by-zero noise on tiny specs
    tflag=""; mflag=""
    awk -v b="$bms" -v n="$nms" -v t="$TIME_TOL" -v abs="$TIME_ABS_MS" 'BEGIN{exit !((n+1) > (b+1)*t && (n-b) > abs)}' && tflag=" REGRESSION"
    awk -v b="$bkib" -v n="$nkib" -v t="$MEM_TOL" 'BEGIN{exit !(n > b*t)}' && mflag=" REGRESSION"
    [ -n "$tflag$mflag" ] && fail=1
    printf '%-28s | %-22s | %-22s\n' "$n" "$bms -> $nms$tflag" "$bkib -> $nkib$mflag"
  done < "$baseline"
  [ "$fail" = 0 ] && echo "no regressions" || echo "REGRESSIONS DETECTED" >&2
  exit $fail
fi
