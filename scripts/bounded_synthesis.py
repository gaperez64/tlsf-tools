#!/usr/bin/env python3
"""Run tlsfcompose --aiger over a bounded TLSF sample."""

import argparse
import csv
import os
import random
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path


COLUMNS = [
    "process_status",
    "returncode",
    "file",
    "elapsed_ms",
    "stdout_bytes",
    "stderr_first",
]


def repo_root():
    return Path(__file__).resolve().parents[1]


def default_compose():
    candidate = repo_root() / "build" / "tlsfcompose"
    if candidate.exists():
        return str(candidate)
    return "tlsfcompose"


def default_ltlsynt():
    return os.environ.get("LTLSYNT", "ltlsynt")


def read_file_list(path):
    files = []
    with open(path, encoding="utf-8") as fp:
        for line in fp:
            item = line.strip()
            if item and not item.startswith("#"):
                files.append(item)
    return files


def discover(paths, file_lists):
    files = []
    for fl in file_lists:
        files.extend(read_file_list(fl))
    for item in paths:
        if os.path.isdir(item):
            for root, _, names in os.walk(item):
                for name in names:
                    if name.endswith(".tlsf"):
                        files.append(os.path.join(root, name))
        else:
            files.append(item)
    return sorted(dict.fromkeys(files))


def sample_files(files, sample, seed):
    if sample is None or sample >= len(files):
        return files
    rng = random.Random(seed)
    return sorted(rng.sample(files, sample))


def limit_address_space(mem_mb):
    def _limit():
        lim = mem_mb * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (lim, lim))

    return _limit


def first_stderr_line(stderr):
    for line in stderr.splitlines():
        line = line.strip()
        if line:
            return line[:200]
    return "-"


def classify(returncode, stderr):
    if returncode == 0:
        return "ok"
    if returncode < 0:
        return "signal"
    if "UNREALIZABLE" in stderr:
        return "unrealizable"
    return "error"


def run_one(args, path):
    cmd = [args.compose, "--aiger"]
    if args.ltlsynt:
        cmd.extend(["--ltlsynt", args.ltlsynt])
    if args.experimental_bounded:
        cmd.extend(["--experimental-bounded", str(args.experimental_bounded)])
    if args.split:
        cmd.append("--split")
    cmd.append(path)
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=args.timeout,
            preexec_fn=limit_address_space(args.mem_mb),
            text=False,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = int((time.monotonic() - start) * 1000)
        return {
            "process_status": "timeout",
            "returncode": "-",
            "file": path,
            "elapsed_ms": str(elapsed),
            "stdout_bytes": str(len(exc.stdout or b"")),
            "stderr_first": "-",
        }
    elapsed = int((time.monotonic() - start) * 1000)
    stderr = proc.stderr.decode("utf-8", errors="replace")
    return {
        "process_status": classify(proc.returncode, stderr),
        "returncode": str(proc.returncode),
        "file": path,
        "elapsed_ms": str(elapsed),
        "stdout_bytes": str(len(proc.stdout)),
        "stderr_first": first_stderr_line(stderr),
    }


def read_rows(path):
    with open(path, newline="", encoding="utf-8") as fp:
        return list(csv.DictReader(fp, delimiter="\t"))


def aggregate(rows):
    total = len(rows)
    ok = sum(1 for row in rows if row.get("process_status") == "ok")
    unreal = sum(1 for row in rows if row.get("process_status") == "unrealizable")
    timeout = sum(1 for row in rows if row.get("process_status") == "timeout")
    error = sum(1 for row in rows if row.get("process_status") == "error")
    signal = sum(1 for row in rows if row.get("process_status") == "signal")
    elapsed = sum(int(row.get("elapsed_ms", "0") or "0") for row in rows)
    return {
        "total": total,
        "ok": ok,
        "unrealizable": unreal,
        "timeout": timeout,
        "error": error,
        "signal": signal,
        "elapsed_ms": elapsed,
        "ok_rate": (100.0 * ok / total) if total else 0.0,
    }


def summary_lines(rows, baseline_rows):
    agg = aggregate(rows)
    lines = [
        "# bounded synthesis: "
        f"specs={agg['total']} ok={agg['ok']} "
        f"unrealizable={agg['unrealizable']} timeout={agg['timeout']} "
        f"error={agg['error']} signal={agg['signal']}",
        "# solve-rate: "
        f"ok={agg['ok']}/{agg['total']} ({agg['ok_rate']:.1f}%), "
        f"elapsed={agg['elapsed_ms']}ms",
    ]
    if baseline_rows is not None:
        base = aggregate(baseline_rows)
        lines.append(
            "# delta vs baseline: "
            f"ok_rate={agg['ok_rate'] - base['ok_rate']:+.1f}pp, "
            f"ok={agg['ok'] - base['ok']:+d}, "
            f"unrealizable={agg['unrealizable'] - base['unrealizable']:+d}, "
            f"error={agg['error'] - base['error']:+d}, "
            f"timeout={agg['timeout'] - base['timeout']:+d}"
        )
    return lines


def write_rows(rows, output):
    fp = sys.stdout if output == "-" else open(output, "w", encoding="utf-8")
    try:
        writer = csv.DictWriter(
            fp,
            fieldnames=COLUMNS,
            delimiter="\t",
            lineterminator="\n",
            extrasaction="ignore",
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row.get(key, "-") for key in COLUMNS})
    finally:
        if fp is not sys.stdout:
            fp.close()


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Run tlsfcompose --aiger over a bounded TLSF corpus sample."
    )
    parser.add_argument("paths", nargs="*", help="TLSF files or directories")
    parser.add_argument("--file-list", action="append", default=[],
                        help="read TLSF paths from FILE, one per line")
    parser.add_argument("--compose", default=default_compose(),
                        help="path to tlsfcompose")
    parser.add_argument("--ltlsynt", default=default_ltlsynt(),
                        help="path to ltlsynt; use '' to omit --ltlsynt")
    parser.add_argument("--output", default="-",
                        help="write harness TSV to FILE (default stdout)")
    parser.add_argument("--baseline",
                        help="previous bounded_synthesis TSV for deltas")
    parser.add_argument("--sample", type=int,
                        help="limit the run to N deterministically sampled specs")
    parser.add_argument("--seed", type=int, default=1,
                        help="sample seed (default 1)")
    parser.add_argument("--mem-mb", type=int, default=3000,
                        help="address-space cap per spec in MB (default 3000)")
    parser.add_argument("--timeout", type=float, default=1800,
                        help="wall-clock timeout per spec in seconds")
    parser.add_argument("--experimental-bounded", type=int,
                        help="pass --experimental-bounded N to tlsfcompose")
    parser.add_argument("--split", action="store_true",
                        help="pass --split through to tlsfcompose")
    parser.add_argument("--quiet", action="store_true",
                        help="suppress the human summary on stderr")
    args = parser.parse_args(argv)
    if args.sample is not None and args.sample <= 0:
        parser.error("--sample must be positive")
    if args.mem_mb <= 0:
        parser.error("--mem-mb must be positive")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.ltlsynt == "":
        args.ltlsynt = None
    return args


def main(argv):
    args = parse_args(argv)
    files = sample_files(discover(args.paths, args.file_list), args.sample,
                         args.seed)
    if not files:
        sys.exit("bounded_synthesis: no TLSF input files")

    rows = [run_one(args, path) for path in files]
    write_rows(rows, args.output)

    if not args.quiet:
        baseline_rows = read_rows(args.baseline) if args.baseline else None
        for line in summary_lines(rows, baseline_rows):
            print(line, file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1:])
