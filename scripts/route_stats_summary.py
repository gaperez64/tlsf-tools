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
    "n_oxidd_clusters",
    "n_external_clusters",
    "total_nodes",
    "oxidd_nodes",
    "external_nodes",
    "total_bytes",
    "oxidd_bytes",
    "external_bytes",
    "max_outputs_any_cluster",
    "max_outputs_external",
    "preprocessor_only_candidate",
    "dominant_external_reason",
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


def summarize(path, rows):
    oxidd = [r for r in rows if uses_oxidd(r)]
    external = [r for r in rows if not uses_oxidd(r)]
    outputs = [to_int(r, "n_outputs", "n_outs") for r in rows]
    external_outputs = [to_int(r, "n_outputs", "n_outs") for r in external]
    reasons = Counter(r.get("reason", "") or "-" for r in external)
    dominant_reason = "-"
    if reasons:
        dominant_reason = sorted(reasons.items(), key=lambda kv: (-kv[1], kv[0]))[0][0]
    return {
        "spec": path,
        "n_clusters": len(rows),
        "n_oxidd_clusters": len(oxidd),
        "n_external_clusters": len(external),
        "total_nodes": sum(to_int(r, "formula_nodes", "nodes") for r in rows),
        "oxidd_nodes": sum(to_int(r, "formula_nodes", "nodes") for r in oxidd),
        "external_nodes": sum(to_int(r, "formula_nodes", "nodes") for r in external),
        "total_bytes": sum(to_int(r, "formula_bytes") for r in rows),
        "oxidd_bytes": sum(to_int(r, "formula_bytes") for r in oxidd),
        "external_bytes": sum(to_int(r, "formula_bytes") for r in external),
        "max_outputs_any_cluster": max(outputs) if outputs else 0,
        "max_outputs_external": max(external_outputs) if external_outputs else 0,
        "preprocessor_only_candidate": 1 if not external else 0,
        "dominant_external_reason": dominant_reason,
    }


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Emit one route-stat summary TSV row per TLSF spec."
    )
    parser.add_argument("paths", nargs="+", help="TLSF files or directories")
    parser.add_argument("--compose", default=default_compose(),
                        help="path to tlsfcompose")
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
        writer.writerow(summarize(path, parse_rows(proc.stdout)))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
