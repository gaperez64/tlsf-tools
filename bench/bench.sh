#!/usr/bin/env bash
# Benchmark tlsf-tools against syfco: wall-clock time (median of N runs) and
# peak resident memory, over the specs in bench/specs/.
#
#   bench/bench.sh [--build DIR] [--runs N] [--baseline] [--check]
#   bench/bench.sh --matrix CORPUS [--runs N]
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
matrix_corpus=""
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
    --matrix) matrix_corpus="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

percentile() {
  local pct="$1"
  awk -v pct="$pct" '
    { a[NR] = $1 }
    END {
      if (NR == 0) { print 0; exit }
      idx = int((NR * pct + 99) / 100)
      if (idx < 1) idx = 1
      if (idx > NR) idx = NR
      print a[idx]
    }'
}

cpu_supported() {
  local cpu="$1"
  case "$cpu" in
    baseline|native) return 0 ;;
    x86-64-v2)
      [ -r /proc/cpuinfo ] || return 0
      grep -qi 'sse4_2' /proc/cpuinfo && grep -qi 'popcnt' /proc/cpuinfo
      return $? ;;
    avx2)
      [ -r /proc/cpuinfo ] || return 0
      grep -qi 'avx2' /proc/cpuinfo
      return $? ;;
    *) return 0 ;;
  esac
}

setup_matrix_build() {
  local dir="$1" cpu="$2"
  if ! cpu_supported "$cpu"; then
    echo "skip $cpu: CPU tier not supported by this host" >&2
    return 1
  fi
  if [ -d "$dir/meson-private" ]; then
    meson setup "$dir" --reconfigure -Doxidd=enabled -Dcpu="$cpu" \
      --buildtype=release >/dev/null || return 1
  else
    meson setup "$dir" -Doxidd=enabled -Dcpu="$cpu" --buildtype=release \
      >/dev/null || return 1
  fi
  ninja -C "$dir" >/dev/null
}

measure_once() {
  local tmp start end rc rss
  tmp="$(mktemp)"
  start=$(date +%s%N)
  /usr/bin/time -v -o "$tmp" "$@" >/dev/null 2>/dev/null
  rc=$?
  end=$(date +%s%N)
  rss="$(awk '/Maximum resident/{print $NF}' "$tmp")"
  rm -f "$tmp"
  printf '%s\t%s\t%s\n' "$(((end - start) / 1000000))" "${rss:-0}" "$rc"
}

measure_matrix_once() {
  local build_dir="$1" label="$2" spec="$3"
  local cmd=()
  case "$label" in
    tlsf2ltl)
      cmd=("$build_dir/tlsf2ltl" "$spec") ;;
    tlsfresidual_split)
      cmd=("$build_dir/tlsfresidual" --split "$spec") ;;
    route_stats)
      cmd=("$build_dir/tlsfcompose" --split --route-stats "$spec") ;;
    compose_self_contained)
      cmd=("$build_dir/tlsfcompose" --split --aiger --ltlsynt /bin/false "$spec") ;;
    compose_full)
      cmd=("$build_dir/tlsfcompose" --split --aiger "$spec") ;;
    *)
      return 2 ;;
  esac
  measure_once "${cmd[@]}"
}

summarize_matrix_command() {
  local build_name="$1" cpu="$2" build_dir="$3" label="$4" route_file="$5"
  local times=() rss_values=() failures=0 self_ok=0 total=0 spec run row ms rss rc
  for spec in "${matrix_specs[@]}"; do
    for ((run = 0; run < runs; run++)); do
      row="$(measure_matrix_once "$build_dir" "$label" "$spec")"
      IFS=$'\t' read -r ms rss rc <<< "$row"
      times+=("$ms")
      rss_values+=("$rss")
      [ "$rc" = 0 ] || failures=$((failures + 1))
      if [ "$label" = compose_self_contained ] && [ "$rc" = 0 ]; then
        self_ok=$((self_ok + 1))
      fi
      total=$((total + 1))
    done
  done
  local med p95 max_rss
  med="$(printf '%s\n' "${times[@]}" | sort -n | percentile 50)"
  p95="$(printf '%s\n' "${times[@]}" | sort -n | percentile 95)"
  max_rss="$(printf '%s\n' "${rss_values[@]}" | sort -n | tail -1)"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$build_name" "$cpu" "$label" "${#matrix_specs[@]}" "$med" "$p95" \
    "${max_rss:-0}" "$failures" "$self_ok/$total" "$route_file"
}

run_matrix() {
  [ "$runs" -lt 3 ] && runs=3
  [ -n "$matrix_corpus" ] || { echo "--matrix needs a corpus path" >&2; exit 2; }
  mapfile -t matrix_specs < <(find "$matrix_corpus" -name '*.tlsf' | sort)
  [ ${#matrix_specs[@]} -gt 0 ] || { echo "no TLSF files in $matrix_corpus" >&2; exit 2; }

  local entries=(
    "build-scalar:baseline"
    "build-v2:x86-64-v2"
    "build-avx2:avx2"
    "build-native:native"
  )
  local commands=(tlsf2ltl tlsfresidual_split route_stats compose_self_contained)
  if command -v ltlsynt >/dev/null 2>&1; then
    commands+=(compose_full)
  fi

  printf 'build\tcpu\tcommand\tspecs\tmedian_ms\tp95_ms\tmax_rss_kib\tfailures\tself_contained\troute_summary\n'
  local entry dir cpu route_file
  for entry in "${entries[@]}"; do
    dir="${entry%%:*}"
    cpu="${entry##*:}"
    setup_matrix_build "$root/$dir" "$cpu" || continue
    route_file="$root/bench/route_stats_${cpu}.tsv"
    "$root/scripts/collect_route_stats.py" --compose "$root/$dir/tlsfcompose" \
      --out "$route_file" "$matrix_corpus" >/dev/null || true
    for cmd in "${commands[@]}"; do
      summarize_matrix_command "$dir" "$cpu" "$root/$dir" "$cmd" "$route_file"
    done
  done
}

if [ -n "$matrix_corpus" ]; then
  run_matrix
  exit 0
fi

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
