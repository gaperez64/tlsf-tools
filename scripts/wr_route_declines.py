#!/usr/bin/env python3
"""Summarize W/R-safety residuals that still fall back to ltlsynt."""

import argparse
import collections
import csv
import sys


def is_wr_fallback(row):
    return (
        row.get("route") == "ltlsynt"
        and row.get("has_liveness") == "0"
        and (row.get("has_weak_until") == "1" or row.get("has_release") == "1")
    )


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Report W/R-safety fallback reasons from route-stats TSV."
    )
    parser.add_argument("route_stats", help="TSV from collect_route_stats.py")
    parser.add_argument("--examples", type=int, default=5,
                        help="examples per reason")
    return parser.parse_args(argv)


def main(argv):
    args = parse_args(argv)
    by_reason = collections.defaultdict(list)
    with open(args.route_stats, encoding="utf-8", newline="") as fp:
        for row in csv.DictReader(fp, delimiter="\t"):
            if is_wr_fallback(row):
                by_reason[row.get("reason", "")].append(row)

    total = sum(len(rows) for rows in by_reason.values())
    print(f"wr_fallback_rows\t{total}")
    for reason, rows in sorted(by_reason.items(), key=lambda item: -len(item[1])):
        specs = {row.get("spec") or row.get("file") for row in rows}
        nodes = sum(int(row.get("formula_nodes") or 0) for row in rows)
        print(f"reason\t{len(rows)}\t{len(specs)}\t{nodes}\t{reason}")
        for row in rows[:max(args.examples, 0)]:
            print(
                "example\t{spec}\tcluster={cluster}\tnodes={nodes}\t"
                "bytes={bytes}\touts={outs}".format(
                    spec=row.get("spec") or row.get("file"),
                    cluster=row.get("cluster_id", ""),
                    nodes=row.get("formula_nodes", ""),
                    bytes=row.get("formula_bytes", ""),
                    outs=row.get("n_outputs", ""),
                )
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
