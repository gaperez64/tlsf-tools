#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
export LEAN_STACK_SIZE_KB="${LEAN_STACK_SIZE_KB:-2048}"
export LEAN_MAIN_USE_THREAD="${LEAN_MAIN_USE_THREAD:-0}"

# No proof source currently declares axioms; reject placeholders even in comments.
echo 'Checking for proof placeholders and axiom declarations'
if grep -RnE --include='*.lean' --exclude-dir=.lake '\b(sorry|admit|axiom)\b' \
    . ../tools/golden; then
  echo 'Forbidden proof placeholder or axiom declaration' >&2
  exit 1
else
  status=$?
  # grep errors must fail too, rather than pass as an empty search.
  if [[ $status != 1 ]]; then exit "$status"; fi
fi

# Recompute source hashes even after restoring .lake; never skip on a cache hit.
echo 'Building the proof library'
time timeout 1500 lake --rehash build

# Keep these diagnostics serial: each module can use the full local memory budget.
for module in LTL Game Objective Restriction Passes Definition Cluster Pruning Examples Rewrites SetDedup IntegerLiteral CheckedArithmetic NextStrength Gr1/Region Gr1/Examples; do
  echo "Checking $module directly, then through Lake"
  time timeout 300 lake env lean -j1 -s2048 -DElab.async=false -DwarningAsError=true "TlsfProofs/$module.lean"
  time timeout 300 lake --rehash build "TlsfProofs.${module//\//.}"
done
echo 'Checking the final library build'
time timeout 1500 lake --rehash build

# Build exactly the modules we audit, including unimported nested sources.
# find instead of globstar: macOS ships bash 3.2, which has no globstar.
modules=(TlsfProofs.lean)
while IFS= read -r source; do
  modules+=("$source")
done < <(find TlsfProofs -type f -name '*.lean' | LC_ALL=C sort)
modules=("${modules[@]%.lean}")
modules=("${modules[@]//\//.}")
time timeout 1500 lake --rehash build "${modules[@]}"

echo 'Auditing axioms of every library declaration'
# Separate processes let executable roots declare the same global main.
for module in "${modules[@]}"; do
  time timeout 300 lake env lean -j1 -s2048 -DElab.async=false -DwarningAsError=true --run audit-axioms.lean "$module"
done

for audit in ../tools/golden/*_audit.lean; do
  echo "Running $audit"
  time timeout 300 lake env lean -j1 -s2048 -DElab.async=false -DwarningAsError=true "$audit"
done
