#!/usr/bin/env python3
"""Collect tlsfcompose --route-stats rows across TLSF files/directories."""

import argparse
import csv
import os
import subprocess
import sys
from pathlib import Path


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
    if name in {"strong_next_infinite.tlsf"}:
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


def run_one(args, path):
    cmd = [args.compose, "--split", "--route-stats"]
    if args.experimental_bounded is not None:
        cmd.extend(["--experimental-bounded", str(args.experimental_bounded)])
    cmd.append(path)
    return subprocess.run(
        cmd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def parse_rows(text):
    lines = [line for line in text.splitlines() if line.strip()]
    if not lines:
        return [], []
    reader = csv.DictReader(lines, delimiter="\t")
    return reader.fieldnames or [], list(reader)


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Collect tlsfcompose --split --route-stats TSV rows."
    )
    parser.add_argument("paths", nargs="+", help="TLSF files or directories")
    parser.add_argument("--compose", default=default_compose(),
                        help="path to tlsfcompose")
    parser.add_argument("--out", required=True, help="write TSV to FILE")
    parser.add_argument("--experimental-bounded", type=int,
                        help="pass --experimental-bounded N")
    return parser.parse_args(argv)


def main(argv):
    args = parse_args(argv)
    files = discover(args.paths)
    if not files:
        print("collect_route_stats: no TLSF files found", file=sys.stderr)
        return 2

    fieldnames = None
    rows = []
    failed = False
    for path in files:
        proc = run_one(args, path)
        if proc.returncode != 0:
            failed = True
            err = proc.stderr.strip().splitlines()
            msg = err[0] if err else "failed"
            print(f"collect_route_stats: {path}: {msg}", file=sys.stderr)
            continue
        header, parsed = parse_rows(proc.stdout)
        if fieldnames is None:
            fieldnames = ["file"] + header
        for row in parsed:
            out = {"file": path}
            out.update(row)
            rows.append(out)

    if fieldnames is None:
        fieldnames = ["file"]
    with open(args.out, "w", newline="", encoding="utf-8") as fp:
        writer = csv.DictWriter(fp, fieldnames=fieldnames, delimiter="\t",
                                lineterminator="\n", extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
