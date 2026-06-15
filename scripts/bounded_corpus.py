#!/usr/bin/env python3
"""Run tlsfbenchgraph over a bounded TLSF sample.

Each spec is measured in its own child process with an address-space cap
(RLIMIT_AS) and a wall-clock timeout.  This keeps a single pathological input
from killing the full corpus run while preserving tlsfbenchgraph's TSV metrics.
"""

import argparse
import csv
import os
import random
import resource
import subprocess
import sys
import tempfile
from pathlib import Path


BENCH_COLUMNS = [
    "file",
    "parse_status",
    "inputs",
    "outputs",
    "constraints",
    "safety",
    "liveness",
    "response",
    "mutex",
    "recurrence",
    "persistence",
    "global_recurrence",
    "guarded_next",
    "definition",
    "template_candidates",
    "solved_blocks",
    "certified_blocks",
    "dependent_outputs",
    "residual_constraints",
    "largest_output_component",
    "formula_size_raw",
    "formula_size_norm",
    "wl_stab_depth",
    "fully_solved",
    "conflicts",
    "eliminated_constraints",
    "owned_outputs",
    "residual_clusters",
    "residual_outputs",
    "largest_residual_cluster_outputs",
    "residual_liveness_clusters",
    "residual_size_norm",
]

HARNESS_COLUMNS = ["process_status", "returncode"] + BENCH_COLUMNS


def default_benchgraph():
    root = Path(__file__).resolve().parents[1]
    candidate = root / "build" / "tlsfbenchgraph"
    if candidate.exists():
        return str(candidate)
    return "tlsfbenchgraph"


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
    # ASan maps ~20 TB of shadow memory at startup; RLIMIT_AS=512 MB would
    # abort that immediately.  Skip the cap when running under sanitizers.
    if os.environ.get("ASAN_OPTIONS") or os.environ.get("TSAN_OPTIONS"):
        return None

    def _limit():
        lim = mem_mb * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (lim, lim))

    return _limit


def blank_bench_row(path):
    row = {key: "-" for key in BENCH_COLUMNS}
    row["file"] = os.path.basename(path)
    return row


def failure_row(path, status, returncode="-"):
    row = {"process_status": status, "returncode": str(returncode)}
    row.update(blank_bench_row(path))
    return row


def read_single_bench_row(tsv_path, path):
    with open(tsv_path, newline="", encoding="utf-8") as fp:
        reader = csv.DictReader(
            (line for line in fp if not line.startswith("#")),
            delimiter="\t",
        )
        rows = list(reader)
    if not rows:
        return blank_bench_row(path)
    row = {key: rows[0].get(key, "-") for key in BENCH_COLUMNS}
    row["file"] = row["file"] or os.path.basename(path)
    return row


def run_one(args, path):
    with tempfile.TemporaryDirectory() as td:
        tsv = os.path.join(td, "bench.tsv")
        cmd = [args.benchgraph, "--output", tsv]
        if args.wl is not None:
            cmd.extend(["--wl", str(args.wl)])
        if args.split:
            cmd.append("--split")
        cmd.append(path)
        try:
            proc = subprocess.run(
                cmd,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=args.timeout,
                preexec_fn=limit_address_space(args.mem_mb),
                text=True,
            )
        except subprocess.TimeoutExpired:
            return failure_row(path, "timeout")
        except subprocess.CalledProcessError as exc:
            rc = exc.returncode
            if rc < 0:
                return failure_row(path, "signal", rc)
            return failure_row(path, "error", rc)

        row = {"process_status": "ok", "returncode": str(proc.returncode)}
        row.update(read_single_bench_row(tsv, path))
        return row


def read_rows(path):
    with open(path, newline="", encoding="utf-8") as fp:
        reader = csv.DictReader(
            (line for line in fp if not line.startswith("#")),
            delimiter="\t",
        )
        rows = []
        for row in reader:
            if "process_status" not in row:
                row["process_status"] = "ok"
            if "returncode" not in row:
                row["returncode"] = "0"
            rows.append(row)
    return rows


def int_col(rows, key):
    total = 0
    for row in rows:
        val = row.get(key, "-")
        if val not in ("", "-"):
            total += int(val)
    return total


def pct(num, den):
    if den == 0:
        return 0.0
    return 100.0 * num / den


def int_of(row, key):
    val = row.get(key, "-")
    return int(val) if val not in ("", "-") else 0


def aggregate(rows):
    parsed = [r for r in rows if r.get("parse_status") == "ok"]
    solved = sum(1 for r in parsed if int(r.get("solved_blocks", "0")) > 0)
    fully = sum(1 for r in parsed if int(r.get("fully_solved", "0")) > 0)
    constraints = int_col(parsed, "constraints")
    eliminated = int_col(parsed, "eliminated_constraints")
    outputs = int_col(parsed, "outputs")
    owned = int_col(parsed, "owned_outputs")
    # Residual complexity (monolith -> residual), present only when the
    # benchgraph TSV carries the residual-complexity columns.
    has_residual = any("residual_clusters" in r for r in parsed)
    mono_game = sum(int_of(r, "largest_output_component") for r in parsed)
    res_game = sum(int_of(r, "largest_residual_cluster_outputs") for r in parsed)
    mono_size = sum(int_of(r, "formula_size_norm") for r in parsed)
    res_size = sum(int_of(r, "residual_size_norm") for r in parsed)
    game_smaller = sum(
        1 for r in parsed
        if int_of(r, "largest_residual_cluster_outputs")
        < int_of(r, "largest_output_component"))
    drop_to_safety = sum(
        1 for r in parsed
        if int_of(r, "liveness") > 0 and int_of(r, "fully_solved") == 0
        and int_of(r, "residual_liveness_clusters") == 0)
    factored = sum(1 for r in parsed if int_of(r, "residual_clusters") >= 2)
    return {
        "specs": len(rows),
        "process_ok": sum(1 for r in rows if r.get("process_status") == "ok"),
        "timeouts": sum(1 for r in rows if r.get("process_status") == "timeout"),
        "errors": sum(1 for r in rows if r.get("process_status") == "error"),
        "signals": sum(1 for r in rows if r.get("process_status") == "signal"),
        "parsed": len(parsed),
        "solved": solved,
        "fully": fully,
        "constraints": constraints,
        "eliminated": eliminated,
        "outputs": outputs,
        "owned": owned,
        "solved_rate": pct(solved, len(parsed)),
        "fully_rate": pct(fully, len(parsed)),
        "elim_rate": pct(eliminated, constraints),
        "owned_rate": pct(owned, outputs),
        "has_residual": has_residual,
        "mono_game": mono_game,
        "res_game": res_game,
        "mono_size": mono_size,
        "res_size": res_size,
        "game_smaller": game_smaller,
        "drop_to_safety": drop_to_safety,
        "factored": factored,
    }


def summary_lines(rows, baseline_rows):
    agg = aggregate(rows)
    lines = [
        "# bounded corpus: "
        f"specs={agg['specs']} process_ok={agg['process_ok']} "
        f"timeouts={agg['timeouts']} errors={agg['errors']} "
        f"signals={agg['signals']} parsed={agg['parsed']}",
        "# solve-rate: "
        f"solved={agg['solved']}/{agg['parsed']} ({agg['solved_rate']:.1f}%), "
        f"fully_solved={agg['fully']}/{agg['parsed']} ({agg['fully_rate']:.1f}%)",
        "# residual reduction: "
        f"{agg['eliminated']}/{agg['constraints']} constraints eliminated "
        f"({agg['elim_rate']:.1f}%), "
        f"{agg['owned']}/{agg['outputs']} outputs owned "
        f"({agg['owned_rate']:.1f}%)",
    ]
    if agg["has_residual"]:
        lines.append(
            "# residual complexity: largest sub-game outputs "
            f"{agg['mono_game']}->{agg['res_game']} "
            f"({pct(agg['res_game'], agg['mono_game']):.1f}% of monolith), "
            f"strictly smaller in {agg['game_smaller']} specs; "
            f"{agg['drop_to_safety']} drop liveness->safety, "
            f"{agg['fully']} fully solved; "
            f"{agg['factored']} factor into >=2 clusters; residual size "
            f"{agg['res_size']}/{agg['mono_size']} norm nodes "
            f"({pct(agg['res_size'], agg['mono_size']):.1f}%)")
    if baseline_rows is not None:
        base = aggregate(baseline_rows)
        lines.append(
            "# delta vs baseline: "
            f"solved_rate={agg['solved_rate'] - base['solved_rate']:+.1f}pp, "
            f"fully_solved_rate={agg['fully_rate'] - base['fully_rate']:+.1f}pp, "
            f"constraint_elim={agg['elim_rate'] - base['elim_rate']:+.1f}pp, "
            f"output_owned={agg['owned_rate'] - base['owned_rate']:+.1f}pp"
        )
    return lines


def write_tsv(rows, output):
    fp = sys.stdout if output == "-" else open(output, "w", encoding="utf-8")
    try:
        writer = csv.DictWriter(
            fp,
            fieldnames=HARNESS_COLUMNS,
            delimiter="\t",
            lineterminator="\n",
            extrasaction="ignore",
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row.get(key, "-") for key in HARNESS_COLUMNS})
    finally:
        if fp is not sys.stdout:
            fp.close()


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Run tlsfbenchgraph over a bounded TLSF corpus sample."
    )
    parser.add_argument("paths", nargs="*", help="TLSF files or directories")
    parser.add_argument("--file-list", action="append", default=[],
                        help="read TLSF paths from FILE, one per line")
    parser.add_argument("--benchgraph", default=default_benchgraph(),
                        help="path to tlsfbenchgraph")
    parser.add_argument("--output", default="-",
                        help="write harness TSV to FILE (default stdout)")
    parser.add_argument("--baseline",
                        help="previous benchgraph or harness TSV for deltas")
    parser.add_argument("--sample", type=int,
                        help="limit the run to N deterministically sampled specs")
    parser.add_argument("--seed", type=int, default=1,
                        help="sample seed (default 1)")
    parser.add_argument("--mem-mb", type=int, default=3000,
                        help="address-space cap per spec in MB (default 3000)")
    parser.add_argument("--timeout", type=float, default=1800,
                        help="wall-clock timeout per spec in seconds")
    parser.add_argument("--wl", type=int,
                        help="pass --wl N through to tlsfbenchgraph")
    parser.add_argument("--split", action="store_true",
                        help="pass --split through to tlsfbenchgraph")
    parser.add_argument("--quiet", action="store_true",
                        help="suppress the human summary on stderr")
    args = parser.parse_args(argv)
    if args.sample is not None and args.sample <= 0:
        parser.error("--sample must be positive")
    if args.mem_mb <= 0:
        parser.error("--mem-mb must be positive")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    return args


def main(argv):
    args = parse_args(argv)
    files = sample_files(discover(args.paths, args.file_list), args.sample,
                         args.seed)
    if not files:
        sys.exit("bounded_corpus: no TLSF input files")

    rows = [run_one(args, path) for path in files]
    write_tsv(rows, args.output)

    if not args.quiet:
        baseline_rows = read_rows(args.baseline) if args.baseline else None
        for line in summary_lines(rows, baseline_rows):
            print(line, file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1:])
