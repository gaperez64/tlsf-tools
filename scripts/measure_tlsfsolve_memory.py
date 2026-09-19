#!/usr/bin/env python3
"""Sequential, repeated peak-RSS measurements on the pinned issue-24 corpus.

GNU time measures one timeout/solver process tree per run. No resource usage is
accumulated across runs. Raw stdout/stderr and measurements remain in --out.
"""

import argparse
import collections
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess

from fetch_syntcomp_issue24 import CASES, COMMIT, git_blob_sha


def fingerprint(path):
    path = Path(path).resolve(strict=True)
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return {"path": str(path), "sha256": digest.hexdigest()}


def summarize(records):
    groups = collections.defaultdict(list)
    for record in records:
        groups[(record["instance"], record["nodes"], record["variant"])].append(record)
    rows = []
    for (instance, nodes, variant), samples in sorted(groups.items()):
        row = {"instance": instance, "nodes": nodes, "variant": variant,
               "runs": len(samples), "statuses": sorted({s["status"] for s in samples})}
        for field in ("rss_kib", "elapsed_s"):
            values = [sample[field] for sample in samples]
            row[field] = {"min": min(values), "median": statistics.median(values),
                          "max": max(values)}
        rows.append(row)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", action="append", required=True, metavar="LABEL=PATH")
    parser.add_argument("--corpus", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path, help="new result directory")
    parser.add_argument("--nodes", nargs="+", type=int, default=[8388608, 16777216, 33554432])
    parser.add_argument("--cache", type=int, default=4194304)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    if (min(args.nodes + [args.cache, args.repetitions]) <= 0
            or not math.isfinite(args.timeout) or args.timeout <= 0):
        parser.error("capacities, repetitions, and timeout must be positive and finite")
    timer = Path("/usr/bin/time")
    timeout = shutil.which("timeout")
    if not timer.is_file() or timeout is None:
        parser.error("GNU time (/usr/bin/time) and timeout are required")
    solvers = {}
    for item in args.solver:
        label, separator, path = item.partition("=")
        if not separator or not label or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-_" for c in label):
            parser.error("solver labels must use lowercase letters, digits, '-' or '_'")
        if label in solvers:
            parser.error("duplicate solver label")
        solvers[label] = fingerprint(path)
    inputs = []
    for upstream, expected in CASES:
        path = args.corpus / Path(upstream).name
        if git_blob_sha(path.read_bytes()) != expected:
            parser.error(f"corpus blob mismatch: {path}")
        inputs.append({"instance": upstream, **fingerprint(path)})
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    manifest = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform": platform.platform(), "machine": platform.machine(),
        "cpu_count": os.cpu_count(), "corpus_commit": COMMIT,
        "solvers": solvers, "inputs": inputs, "runner": fingerprint(__file__),
        "nodes": args.nodes, "cache": args.cache, "gc": "auto",
        "repetitions": args.repetitions, "timeout_seconds": args.timeout,
        "time_version": subprocess.check_output([str(timer), "--version"], text=True).splitlines()[0],
        "rss_scope": "Linux ru_maxrss via GNU time %M, KiB, per timeout/solver process tree",
        "ordering": "sequential; reverse variant order on odd repetition+case+capacity index",
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    time_format = ('{"rss_kib":%M,"elapsed_s":%e,"user_s":%U,"system_s":%S,'
                   '"exit_code":%x,"major_faults":%F,"minor_faults":%R,"swaps":%W}')
    records = []
    with (out / "runs.jsonl").open("w") as journal:
        for repeat in range(args.repetitions):
            for case_index, case in enumerate(inputs):
                for cap_index, nodes in enumerate(args.nodes):
                    variants = list(solvers)
                    if (repeat + case_index + cap_index) % 2:
                        variants.reverse()
                    for variant in variants:
                        name = f"r{repeat + 1}-{Path(case['instance']).stem}-{nodes}-{variant}"
                        run_dir = out / name
                        run_dir.mkdir()
                        command = [str(timer), "-q", "-f", time_format,
                                   "-o", str(run_dir / "usage.json"), timeout,
                                   "--kill-after=5", str(args.timeout), solvers[variant]["path"],
                                   "--game-profile=legacy-safety", "--oxidd-nodes", str(nodes),
                                   "--oxidd-cache", str(args.cache), "--oxidd-gc=auto", case["path"]]
                        with (run_dir / "stdout.aag").open("wb") as stdout:
                            with (run_dir / "stderr.log").open("wb") as stderr:
                                proc = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
                        usage = json.loads((run_dir / "usage.json").read_text())
                        if usage["exit_code"] != proc.returncode:
                            raise RuntimeError(f"inconsistent process status: {name}")
                        status = {0: "REALIZABLE", 1: "UNREALIZABLE", 2: "ERROR",
                                  124: "TIMEOUT", 137: "KILLED"}.get(proc.returncode, "ERROR")
                        if status == "REALIZABLE":
                            with (run_dir / "stdout.aag").open("rb") as stream:
                                if not stream.read(4) == b"aag ":
                                    raise RuntimeError(f"missing strategy: {name}")
                        if status == "UNREALIZABLE" and "UNREALIZABLE" not in (run_dir / "stderr.log").read_text():
                            raise RuntimeError(f"missing losing verdict: {name}")
                        record = {"instance": case["instance"], "variant": variant,
                                  "nodes": nodes, "cache": args.cache, "repetition": repeat + 1,
                                  "status": status, "command": command, "artifacts": name,
                                  "stdout_sha256": fingerprint(run_dir / "stdout.aag")["sha256"],
                                  "stderr": (run_dir / "stderr.log").read_text(), **usage}
                        records.append(record)
                        journal.write(json.dumps(record) + "\n")
                        journal.flush()
                        print(f"{name}: {status}, {usage['rss_kib'] / 1024:.1f} MiB, {usage['elapsed_s']:.2f}s", flush=True)
    (out / "summary.json").write_text(json.dumps(summarize(records), indent=2) + "\n")


if __name__ == "__main__":
    main()
