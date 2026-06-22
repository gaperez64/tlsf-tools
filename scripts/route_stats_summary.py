#!/usr/bin/env python3
"""Summarize tlsfcompose --route-stats per TLSF spec."""

import argparse
import csv
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path


FIELDS = [
    "spec",
    "n_clusters",
    "n_oxidd_exact_clusters",
    "n_fallback_clusters",
    "total_nodes",
    "oxidd_nodes",
    "fallback_nodes",
    "total_bytes",
    "oxidd_bytes",
    "fallback_bytes",
    "max_outputs_any_cluster",
    "max_outputs_fallback",
    "self_contained_candidate",
    "dominant_fallback_reason",
]


def repo_root():
    return Path(__file__).resolve().parents[1]


def default_compose():
    candidate = repo_root() / "build" / "tlsfcompose"
    if candidate.exists():
        return str(candidate)
    return "tlsfcompose"


def is_discoverable_tlsf(path):
    name = os.path.basename(path)
    if not name.endswith(".tlsf"):
        return False
    if name.startswith(("bad_", "err_", "undef_")):
        return False
    if name.endswith((".basic.tlsf", ".reemit.tlsf", ".subst.tlsf")):
        return False
    try:
        text = Path(path).read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return False
    return "PARAMETERS" not in text


def discover(items):
    files = []
    for item in items:
        if os.path.isdir(item):
            for root, _, names in os.walk(item):
                for name in names:
                    path = os.path.join(root, name)
                    if is_discoverable_tlsf(path):
                        files.append(path)
        else:
            files.append(item)
    return sorted(dict.fromkeys(files))


def to_int(row, *keys, default=0):
    for key in keys:
        val = row.get(key, "")
        if val not in ("", "-", None):
            return int(val)
    return default


def uses_oxidd(row):
    val = row.get("uses_oxidd")
    if val in ("0", "1"):
        return val == "1"
    return row.get("backend", "").startswith("OxiDD")


def exact(row):
    return row.get("exact") == "1"


def selected_oxidd(row, include_experimental):
    return uses_oxidd(row) and (exact(row) or include_experimental)


def fallback(row, include_experimental):
    return not selected_oxidd(row, include_experimental)


def parse_rows(text):
    lines = [line for line in text.splitlines() if line.strip()]
    if not lines:
        return []
    return list(csv.DictReader(lines, delimiter="\t"))


def run_one(args, path):
    cmd = [args.compose, "--split", "--route-stats"]
    cmd.extend(args.compose_extra_arg)
    if args.experimental_bounded is not None:
        cmd.extend(["--experimental-bounded", str(args.experimental_bounded)])
    cmd.append(path)
    try:
        return subprocess.run(
            cmd,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=args.timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return exc


def summarize(path, rows, include_experimental):
    oxidd = [r for r in rows if selected_oxidd(r, include_experimental)]
    exact_oxidd = [r for r in rows if uses_oxidd(r) and exact(r)]
    fallbacks = [r for r in rows if fallback(r, include_experimental)]
    outputs = [to_int(r, "n_outputs", "n_outs") for r in rows]
    fallback_outputs = [to_int(r, "n_outputs", "n_outs") for r in fallbacks]
    reasons = Counter(r.get("reason", "") or "-" for r in fallbacks)
    dominant_reason = "-"
    if reasons:
        dominant_reason = sorted(reasons.items(), key=lambda kv: (-kv[1], kv[0]))[0][0]
    return {
        "spec": path,
        "n_clusters": len(rows),
        "n_oxidd_exact_clusters": len(exact_oxidd),
        "n_fallback_clusters": len(fallbacks),
        "total_nodes": sum(to_int(r, "formula_nodes", "nodes") for r in rows),
        "oxidd_nodes": sum(to_int(r, "formula_nodes", "nodes") for r in oxidd),
        "fallback_nodes": sum(to_int(r, "formula_nodes", "nodes") for r in fallbacks),
        "total_bytes": sum(to_int(r, "formula_bytes") for r in rows),
        "oxidd_bytes": sum(to_int(r, "formula_bytes") for r in oxidd),
        "fallback_bytes": sum(to_int(r, "formula_bytes") for r in fallbacks),
        "max_outputs_any_cluster": max(outputs) if outputs else 0,
        "max_outputs_fallback": max(fallback_outputs) if fallback_outputs else 0,
        "self_contained_candidate": 1 if not fallbacks else 0,
        "dominant_fallback_reason": dominant_reason,
    }


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Emit one route-stat summary TSV row per TLSF spec."
    )
    parser.add_argument("paths", nargs="+", help="TLSF files or directories")
    parser.add_argument("--compose", default=default_compose(),
                        help="path to tlsfcompose")
    parser.add_argument("--include-experimental", action="store_true",
                        help="count experimental OxiDD routes as self-contained candidates")
    parser.add_argument("--experimental-bounded", type=int,
                        help="pass --experimental-bounded N")
    parser.add_argument("--compose-extra-arg", action="append", default=[],
                        help="extra argument passed to tlsfcompose; repeatable")
    parser.add_argument("--timeout", type=float,
                        help="per-spec timeout in seconds")
    return parser.parse_args(argv)


def main(argv):
    args = parse_args(argv)
    files = discover(args.paths)
    if not files:
        print("route_stats_summary: no TLSF files found", file=sys.stderr)
        return 2

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDS, delimiter="\t",
                            lineterminator="\n")
    writer.writeheader()
    failed = False
    for path in files:
        proc = run_one(args, path)
        if isinstance(proc, subprocess.TimeoutExpired):
            failed = True
            print(
                f"route_stats_summary: {path}: timed out after "
                f"{args.timeout:g}s",
                file=sys.stderr,
            )
            continue
        if proc.returncode != 0:
            failed = True
            err = proc.stderr.strip().splitlines()
            msg = err[0] if err else "failed"
            print(f"route_stats_summary: {path}: {msg}", file=sys.stderr)
            continue
        writer.writerow(summarize(path, parse_rows(proc.stdout),
                                  args.include_experimental))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
