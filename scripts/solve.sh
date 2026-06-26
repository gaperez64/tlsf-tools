#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat >&2 <<'EOF'
Usage: scripts/solve.sh [OPTIONS] SPEC.tlsf

Options:
  --solver PATH          external solver command (default: ltlsynt)
  --backend NAME         ltlsynt or acacia (default: ltlsynt)
  --tlsfcompose PATH     tlsfcompose binary (default: tlsfcompose)
  --output FILE          merged AIGER output (default: strategy.aag)
  --work-dir DIR         decomposition/work directory (default: mktemp)
  --keep-work            keep the temporary work directory
  --help
EOF
}

solver=${SOLVER:-ltlsynt}
backend=ltlsynt
tlsfcompose=${TLSFCOMPOSE:-tlsfcompose}
output=strategy.aag
work_dir=
keep_work=0
spec=

while [ "$#" -gt 0 ]; do
  case "$1" in
    --solver)
      solver=${2:?--solver requires an argument}
      shift 2
      ;;
    --backend)
      backend=${2:?--backend requires an argument}
      shift 2
      ;;
    --tlsfcompose)
      tlsfcompose=${2:?--tlsfcompose requires an argument}
      shift 2
      ;;
    --output)
      output=${2:?--output requires an argument}
      shift 2
      ;;
    --work-dir)
      work_dir=${2:?--work-dir requires an argument}
      shift 2
      ;;
    --keep-work)
      keep_work=1
      shift
      ;;
    --help)
      usage
      exit 0
      ;;
    -*)
      echo "solve.sh: unknown option '$1'" >&2
      usage
      exit 2
      ;;
    *)
      if [ -n "$spec" ]; then
        echo "solve.sh: multiple specs are not supported" >&2
        exit 2
      fi
      spec=$1
      shift
      ;;
  esac
done

if [ -z "$spec" ]; then
  usage
  exit 2
fi

if [ -z "$work_dir" ]; then
  work_dir=$(mktemp -d "${TMPDIR:-/tmp}/tlsf-solve.XXXXXX")
  if [ "$keep_work" -eq 0 ]; then
    trap 'rm -rf "$work_dir"' EXIT
  fi
else
  mkdir -p "$work_dir"
fi
rm -f "$work_dir"/cluster.*.aag "$work_dir"/cluster.*.formula \
      "$work_dir"/cluster.*.ltl "$work_dir"/compose.sh \
      "$work_dir"/controllers.aag "$work_dir"/controllers.txt \
      "$work_dir"/plan.txt

lowercase=0
case "$backend" in
  ltlsynt)
    lowercase=1
    ;;
  acacia)
    lowercase=0
    ;;
  *)
    echo "solve.sh: unknown backend '$backend' (expected ltlsynt or acacia)" >&2
    exit 2
    ;;
esac

decompose_args=(--split --output-dir "$work_dir")
if [ "$lowercase" -eq 1 ]; then
  decompose_args+=(--lowercase)
fi
"$tlsfcompose" "${decompose_args[@]}" "$spec" > "$work_dir/plan.txt"

cluster_aags=()
shopt -s nullglob
for cluster in "$work_dir"/cluster.*.ltl; do
  id=${cluster##*.}
  id=${cluster%.*}
  id=${id##*.}
  ins=$(sed -n 's/^c ins=//p' "$cluster")
  outs=$(sed -n 's/^c outs=//p' "$cluster")
  formula="$work_dir/cluster.$id.formula"
  grep -v '^c ' "$cluster" > "$formula"
  aag="$work_dir/cluster.$id.aag"

  if [ -f "$aag" ]; then
    cluster_aags+=("$aag")
    continue
  fi

  case "$backend" in
    ltlsynt)
      "$solver" --ins="$ins" --outs="$outs" -F "$formula" --aiger > "$aag"
      if head -n 1 "$aag" | grep -q '^UNREALIZABLE'; then
        echo "solve.sh: cluster $id is UNREALIZABLE" >&2
        exit 1
      fi
      ;;
    acacia)
      cat >&2 <<'EOF'
solve.sh: acacia backend hook is intentionally explicit.
Replace this block with the acacia invocation that reads:
  - formula file: $formula
  - inputs:       $ins
  - outputs:      $outs
and writes the controller AIGER to:
  - $aag
EOF
      exit 2
      ;;
  esac
  cluster_aags+=("$aag")
done
shopt -u nullglob

merge_inputs=("$work_dir/controllers.aag")
merge_inputs+=("${cluster_aags[@]}")
"$tlsfcompose" --merge "${merge_inputs[@]}" --output "$output"

if [ "$keep_work" -eq 1 ]; then
  echo "solve.sh: kept work directory $work_dir" >&2
fi
