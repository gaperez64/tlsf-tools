#!/usr/bin/env python3
"""Capture one tlsfsolve diagnostic run into a small local bundle."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path


TRACE_PREFIX = "TLSFSOLVE_TRACE "


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def has_verbose(args: list[str]) -> bool:
    return any(a == "-v" or a == "-vv" or a == "--verbose" for a in args)


def parse_events(stderr_path: Path) -> tuple[list[dict], list[str]]:
    events: list[dict] = []
    malformed: list[str] = []
    with stderr_path.open("r", encoding="utf-8", errors="replace") as f:
        for line in f:
            if not line.startswith(TRACE_PREFIX):
                continue
            payload = line[len(TRACE_PREFIX) :].strip()
            try:
                events.append(json.loads(payload))
            except json.JSONDecodeError:
                malformed.append(payload)
    return events, malformed


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", required=True, help="tlsfsolve binary")
    ap.add_argument("--input", required=True, help="AAG input file")
    ap.add_argument("--out", required=True, help="output directory")
    ap.add_argument("--timeout", type=float, default=None)
    ap.add_argument(
        "solver_args",
        nargs=argparse.REMAINDER,
        help="extra tlsfsolve options after --",
    )
    ns = ap.parse_args()

    solver = Path(ns.solver)
    input_path = Path(ns.input)
    out_dir = Path(ns.out)
    extra = list(ns.solver_args)
    if extra and extra[0] == "--":
        extra = extra[1:]
    verbosity = [] if has_verbose(extra) else ["--verbose"]
    argv = [str(solver), *verbosity, *extra, str(input_path)]

    out_dir.mkdir(parents=True, exist_ok=True)
    stdout_tmp = out_dir / "stdout.bin"
    stderr_log = out_dir / "stderr.log"
    started = time.time()

    try:
        version = subprocess.run(
            [str(solver), "--version"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        ).stdout.strip()
    except OSError as exc:
        print(f"diagnose_tlsfsolve: cannot execute solver: {exc}", file=sys.stderr)
        return 2

    timed_out = False
    try:
        with stdout_tmp.open("wb") as out, stderr_log.open("wb") as err:
            proc = subprocess.run(
                argv,
                stdout=out,
                stderr=err,
                timeout=ns.timeout,
                check=False,
            )
            returncode = proc.returncode
    except subprocess.TimeoutExpired:
        timed_out = True
        returncode = None

    ended = time.time()
    final_stdout = out_dir / ("strategy.aag" if returncode == 0 else "stdout.txt")
    if stdout_tmp.exists():
        os.replace(stdout_tmp, final_stdout)

    events, malformed = parse_events(stderr_log)
    first_failure = next(
        (
            e
            for e in events
            if "failure" in str(e.get("event", ""))
            or e.get("completion") == "failure"
            or e.get("kind")
        ),
        None,
    )
    last_event = events[-1] if events else None
    signal = -returncode if isinstance(returncode, int) and returncode < 0 else None

    manifest = {
        "schema": 1,
        "solver": str(solver),
        "solver_sha256": sha256_file(solver) if solver.is_file() else None,
        "input": str(input_path),
        "input_sha256": sha256_file(input_path),
        "argv": argv,
        "solver_version": version,
        "platform": platform.platform(),
        "python": sys.version.split()[0],
        "started_unix": started,
        "ended_unix": ended,
        "timeout_seconds": ns.timeout,
    }
    (out_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    summary = {
        "schema": 1,
        "returncode": returncode,
        "signal": signal,
        "timed_out": timed_out,
        "duration_seconds": ended - started,
        "last_event": last_event,
        "first_failure": first_failure,
        "malformed_trace_lines": malformed[-3:],
        "stdout_file": final_stdout.name,
        "stderr_file": stderr_log.name,
    }
    (out_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    status = "timeout" if timed_out else str(returncode)
    lines = [
        "# tlsfsolve diagnostic summary",
        "",
        f"- status: {status}",
        f"- duration_seconds: {ended - started:.3f}",
        f"- stdout_file: {final_stdout.name}",
        f"- stderr_file: {stderr_log.name}",
    ]
    if last_event:
        lines.append(f"- last_event: `{last_event.get('phase')}/{last_event.get('event')}`")
    if first_failure:
        lines.append(
            f"- first_failure: `{first_failure.get('phase')}/"
            f"{first_failure.get('event')}`"
        )
    (out_dir / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    return 0 if not timed_out else 124


if __name__ == "__main__":
    raise SystemExit(main())
