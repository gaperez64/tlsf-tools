#!/usr/bin/env bash
set -euo pipefail

case "${DETECTOR_RESULT:?}:${LEAN_NEEDED-}:${LEAN_RESULT:?}" in
  success:true:success|success:false:success|success:false:skipped) exit 0 ;;
  *)
    echo "Lean gate failed: detector=$DETECTOR_RESULT needed=${LEAN_NEEDED-} lean=$LEAN_RESULT" >&2
    exit 1
    ;;
esac
