#!/usr/bin/env python3
"""Summarize gcov line coverage without gcovr."""

import argparse
from pathlib import Path
import re
import subprocess
import sys


FILE_RE = re.compile(r"^File '(.+)'$")
LINES_RE = re.compile(r"^Lines executed:([0-9.]+)% of ([0-9]+)$")


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Run gcov over a Meson coverage build and gate line coverage."
    )
    parser.add_argument("--build-dir", default="build-cov",
                        help="Meson coverage build directory")
    parser.add_argument("--root", default=".",
                        help="repository root used to select src/ files")
    parser.add_argument("--gcov", default="gcov", help="gcov executable")
    parser.add_argument("--threshold", type=float, default=75.0,
                        help="minimum line coverage percentage")
    parser.add_argument("--show-files", action="store_true",
                        help="print per-file line coverage")
    return parser.parse_args(argv)


def normalize_reported_path(build_dir, path_text):
    path = Path(path_text)
    if not path.is_absolute():
        path = build_dir / path
    return path.resolve()


def should_count(root, path):
    try:
        rel = path.relative_to(root)
    except ValueError:
        return False
    if not rel.parts or rel.parts[0] != "src":
        return False
    name = rel.name
    return "tlsf_lex" not in name and "tlsf_parse" not in name


def parse_gcov_output(build_dir, output):
    current_file = None
    records = []
    for raw_line in output.splitlines():
        line = raw_line.strip()
        file_match = FILE_RE.match(line)
        if file_match:
            current_file = normalize_reported_path(build_dir, file_match.group(1))
            continue
        line_match = LINES_RE.match(line)
        if line_match is None or current_file is None:
            continue
        percent = float(line_match.group(1))
        total = int(line_match.group(2))
        covered = int(round(total * percent / 100.0))
        records.append((current_file, covered, total))
        current_file = None
    return records


def run_gcov(args, build_dir, gcda_file):
    rel_gcda = gcda_file.relative_to(build_dir)
    proc = subprocess.run(
        [args.gcov, "-n", "-b", "-c", str(rel_gcda)],
        cwd=build_dir,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return proc.stdout


def main(argv):
    args = parse_args(argv)
    root = Path(args.root).resolve()
    build_dir = Path(args.build_dir).resolve()
    gcda_files = sorted(build_dir.rglob("*.gcda"))
    if not gcda_files:
        raise SystemExit(f"no .gcda files found under {build_dir}")

    per_file = {}
    for gcda_file in gcda_files:
        output = run_gcov(args, build_dir, gcda_file)
        for path, covered, total in parse_gcov_output(build_dir, output):
            if total == 0 or not should_count(root, path):
                continue
            old = per_file.get(path)
            if old is not None:
                old_covered, old_total = old
                if old_total != total:
                    sys.stderr.write(
                        f"warning: duplicate coverage for {path} has "
                        f"line totals {old_total} and {total}; using larger "
                        "covered count\n"
                    )
                covered = max(old_covered, covered)
                total = max(old_total, total)
            per_file[path] = (covered, total)

    if not per_file:
        raise SystemExit(f"no covered source files under {root / 'src'}")

    total_covered = sum(covered for covered, _ in per_file.values())
    total_lines = sum(total for _, total in per_file.values())
    percent = 100.0 * total_covered / total_lines

    if args.show_files:
        for path in sorted(per_file):
            covered, total = per_file[path]
            rel = path.relative_to(root)
            print(f"{rel}: {100.0 * covered / total:.2f}% ({covered}/{total})")

    print(f"line coverage: {percent:.2f}% ({total_covered}/{total_lines})")
    if percent + 1e-9 < args.threshold:
        print(f"FAIL: line coverage below {args.threshold:.2f}%", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
