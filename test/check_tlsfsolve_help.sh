#!/usr/bin/env bash
set -euo pipefail

out="$("$1" --help 2>&1)"
for expected in \
  "game interpretation (default: auto)" \
  "BDD node arena capacity, in entries" \
  "BDD apply-cache capacity, in entries" \
  "capacity default: 2^(inputs+latches+6)" \
  "proactive GC policy (default: auto)" \
  "pressure trigger (default: 80; pressure only)" \
  "static BDD order (default: input-first)" \
  "Boolean construction plan (default: gates)" \
  "safety construction (default: eager)" \
  "(default: synthesize a full strategy)" \
  "policies may collect once to retry a failed pure BDD operation"
do
  if ! grep -Fq "$expected" <<<"$out"; then
    printf "missing help text: %s\n%s\n" "$expected" "$out" >&2
    exit 1
  fi
done
