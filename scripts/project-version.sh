#!/bin/sh

# Use the newest version tag reachable from this checkout.  Source archives and
# shallow checkouts may not contain tag history, so keep their version useful
# and predictable without requiring network access.
repo_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)

if tag=$(git -C "$repo_dir" describe --tags --abbrev=0 \
    --match 'v[0-9]*' 2>/dev/null); then
  printf '%s\n' "${tag#v}"
else
  printf '1\n'
fi
