#!/usr/bin/env python3
"""Summarize tlsfcompose --route-stats TSV data."""

import csv
import sys
from collections import Counter


def to_int(row, key, default=0):
    val = row.get(key, "")
    if val in ("", "-"):
        return default
    return int(val)


def is_fallback(row):
    uses_oxidd = row.get("uses_oxidd")
    if uses_oxidd in ("0", "1"):
        return uses_oxidd == "0"
    if row.get("route") in {"ltlsynt", "output-free"}:
        return True
    backend = row.get("backend", "")
    return bool(backend) and not backend.startswith("OxiDD")


def is_exact_oxidd(row):
    uses_oxidd = row.get("uses_oxidd")
    if uses_oxidd in ("0", "1"):
        return row.get("exact") == "1" and uses_oxidd == "1"
    return row.get("exact") == "1" and row.get("backend", "").startswith("OxiDD")


def is_experimental(row):
    return row.get("exact") == "0"


def read_rows(path):
    with open(path, newline="", encoding="utf-8") as fp:
        return list(csv.DictReader(fp, delimiter="\t"))


def main(argv):
    if len(argv) != 1:
        print("usage: summarize_route_stats.py route_stats.tsv", file=sys.stderr)
        return 2

    rows = read_rows(argv[0])
    specs = len({
        row.get("spec") or row.get("file", "")
        for row in rows
        if row.get("spec") or row.get("file", "")
    })
    if not specs and rows:
        specs = 1

    routes = Counter(row.get("route", "") or "-" for row in rows)
    fallback = [row for row in rows if is_fallback(row)]
    fallback_outs = [
        to_int(row, "n_outputs", to_int(row, "n_outs")) for row in fallback
    ]
    fallback_nodes = sum(
        to_int(row, "formula_nodes", to_int(row, "nodes")) for row in fallback
    )
    fallback_burden = sum(2 ** min(out, 20) for out in fallback_outs)
    fallback_mean = (
        sum(fallback_outs) / len(fallback_outs) if fallback_outs else 0.0
    )

    print(f"specs={specs}")
    print(f"clusters={len(rows)}")
    for route, count in sorted(routes.items()):
        print(f"route.{route}={count}")
    print(f"fallback.clusters={len(fallback)}")
    print(f"fallback.nodes={fallback_nodes}")
    print(f"fallback.max_outs={max(fallback_outs) if fallback_outs else 0}")
    print(f"fallback.mean_outs={fallback_mean:.2f}")
    print(f"fallback.burden_pow2={fallback_burden}")
    print(f"exact_oxidd.clusters={sum(1 for row in rows if is_exact_oxidd(row))}")
    print(f"experimental.clusters={sum(1 for row in rows if is_experimental(row))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
