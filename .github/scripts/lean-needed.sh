#!/usr/bin/env bash
set -euo pipefail

# Dispatch, schedule, and missing/new/force-pushed bases run conservatively.
case "${GITHUB_EVENT_NAME:?}" in
  pull_request|push)
    if [[ -z ${BASE_SHA:-} || $BASE_SHA =~ ^0+$ ]] ||
        ! git cat-file -e "$BASE_SHA^{commit}" 2>/dev/null; then
      echo true
      exit
    fi
    ;;
  *) echo true; exit ;;
esac

# Disable rename detection so moving a proof out of the path set still checks it.
# NUL delimiters also handle spaces, quotes, and newlines in filenames.
git diff --name-only --no-renames -z "$BASE_SHA" HEAD | {
  needed=false
  while IFS= read -r -d '' path; do
    case "$path" in
      # Proof sources, toolchain, Lake configuration, README, and check.sh.
      proofs/*) needed=true ;;
      # External Lean axiom audits run by check.sh.
      tools/golden/*.lean) needed=true ;;
      # The workflow and its change detector are themselves CI inputs.
      .github/workflows/lean.yml|.github/scripts/lean-needed.sh) needed=true ;;
    esac
  done
  echo "$needed"
}
