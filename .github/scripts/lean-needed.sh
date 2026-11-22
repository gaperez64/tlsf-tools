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

# Name-only reports rename destinations; diff both ways to include old paths too.
# Keep the pipe open through EOF so either git failure propagates via pipefail.
{
  git diff --name-only --find-renames -z "$BASE_SHA" HEAD
  git diff --name-only --find-renames -z HEAD "$BASE_SHA"
} | {
  needed=false
  while IFS= read -r -d '' path; do
    case "$path" in
      # Proof sources, toolchain, Lake configuration, README, and check.sh.
      proofs/*) needed=true ;;
      # External Lean axiom audits run by check.sh.
      tools/golden/*.lean) needed=true ;;
      # The workflow and its change detector are themselves CI inputs.
      .github/workflows/lean.yml|.github/scripts/lean-*.sh|test/cli/check_lean_ci.py|test/cli/check_axiom_audit.py) needed=true ;;
    esac
  done
  echo "$needed"
}
