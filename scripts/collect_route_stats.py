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
    for extra in args.compose_extra_arg:
        cmd.append(extra)
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
    parser.add_argument("--compose-extra-arg", action="append", default=[],
                        help="extra argument passed to tlsfcompose; repeatable")
    parser.add_argument("--experimental-bounded", type=int,
                        help="pass --experimental-bounded N")
    parser.add_argument("--timeout", type=float,
                        help="per-spec timeout in seconds")
    return parser.parse_args(argv)


def main(argv):
    args = parse_args(argv)
    files = discover(args.paths)
    if not files:
        print("collect_route_stats: no TLSF files found", file=sys.stderr)
        return 2

    fieldnames = None
    writer = None
    failed = False
    with open(args.out, "w", newline="", encoding="utf-8") as fp:
        for path in files:
            proc = run_one(args, path)
            if isinstance(proc, subprocess.TimeoutExpired):
                failed = True
                print(
                    f"collect_route_stats: {path}: timed out after "
                    f"{args.timeout:g}s",
                    file=sys.stderr,
                )
                continue
            if proc.returncode != 0:
                failed = True
                err = proc.stderr.strip().splitlines()
                msg = err[0] if err else "failed"
                print(f"collect_route_stats: {path}: {msg}", file=sys.stderr)
                continue
            header, parsed = parse_rows(proc.stdout)
            if fieldnames is None:
                fieldnames = ["file"] + header
                if "spec" not in fieldnames:
                    fieldnames.append("spec")
                writer = csv.DictWriter(fp, fieldnames=fieldnames,
                                        delimiter="\t", lineterminator="\n",
                                        extrasaction="ignore")
                writer.writeheader()
            if writer is None:
                continue
            for row in parsed:
                out = {"file": path}
                out.update(row)
                if not out.get("spec"):
                    out["spec"] = path
                writer.writerow(out)
            fp.flush()
        if fieldnames is None:
            writer = csv.DictWriter(fp, fieldnames=["file"], delimiter="\t",
                                    lineterminator="\n")
            writer.writeheader()

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
