#!/usr/bin/env python3
"""Replay an automata-study bundle through Acacia and apply zero-loss gates."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import pathlib
import signal
import statistics
import subprocess
import sys
import time
import uuid


RESULT_FIELDS = (
    "result_schema", "spec_id", "source", "schedule", "orientation",
    "repetition", "generation_status", "verdict", "seconds", "returncode",
    "timed_out", "scope_result", "resource_limited", "stdout_sha256",
    "stderr_sha256",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", required=True, type=pathlib.Path)
    parser.add_argument("--acacia-replay", required=True, type=pathlib.Path)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    parser.add_argument("--baseline", default="off")
    parser.add_argument("--schedule", action="append", dest="schedules")
    parser.add_argument("--orientation", action="append", dest="orientations")
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--memory-max", default="8G")
    parser.add_argument("--memory-swap-max", default="0")
    parser.add_argument("--spot-fast", choices=("off", "det"), default="det")
    parser.add_argument("-K", type=int, default=99)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument(
        "--no-systemd-scope", action="store_true",
        help="testing only: omit the memory-limited user scope",
    )
    return parser.parse_args()


def write_tsv(path: pathlib.Path, rows: list[dict], fields) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, delimiter="\t", fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    temporary.replace(path)


def file_sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_results(path: pathlib.Path) -> list[dict]:
    if not path.exists():
        return []
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != RESULT_FIELDS:
            raise ValueError(f"{path}: incompatible result schema")
        return list(reader)


def stop_scope(unit: str) -> None:
    try:
        subprocess.run(
            ["systemctl", "--user", "stop", f"{unit}.scope"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            timeout=10, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        pass


def read_scope_result(unit: str) -> str:
    try:
        result = subprocess.run(
            ["systemctl", "--user", "show", f"{unit}.scope", "--property=Result",
             "--value"],
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
            timeout=5, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return "unavailable"
    return result.stdout.strip() or "unavailable"


def terminate_group(process: subprocess.Popen) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=2)
    except (ProcessLookupError, subprocess.TimeoutExpired):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass


def run_bounded(command: list[str], args: argparse.Namespace):
    unit = "tlsf-autstudy-" + uuid.uuid4().hex[:12]
    scoped = command
    if not args.no_systemd_scope:
        scoped = [
            "systemd-run", "--user", "--scope", "--quiet", f"--unit={unit}",
            "--property=KillMode=control-group",
            f"--property=MemoryMax={args.memory_max}",
            f"--property=MemorySwapMax={args.memory_swap_max}", *command,
        ]
    started = time.monotonic()
    process = subprocess.Popen(
        scoped, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True,
    )
    timed_out = False
    scope_result = "disabled" if args.no_systemd_scope else "unavailable"
    try:
        try:
            stdout, stderr = process.communicate(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            if not args.no_systemd_scope:
                stop_scope(unit)
            terminate_group(process)
            stdout, stderr = process.communicate()
        if not args.no_systemd_scope:
            scope_result = read_scope_result(unit)
    finally:
        if not args.no_systemd_scope:
            stop_scope(unit)
        terminate_group(process)
    resource_limited = (
        scope_result in {"resources", "oom-kill"}
        or (not args.no_systemd_scope and not timed_out
            and process.returncode in {-9, 137})
    )
    return (process.returncode, timed_out, resource_limited, scope_result,
            time.monotonic() - started, stdout, stderr)


def classify(returncode: int, timed_out: bool, resource_limited: bool,
             output: str) -> str:
    if timed_out:
        return "TIMEOUT"
    if resource_limited:
        return "RESOURCE_LIMIT"
    for verdict, expected in (("UNREALIZABLE", 1), ("REALIZABLE", 0),
                              ("UNKNOWN", 2)):
        if verdict in output:
            return verdict if returncode == expected else "ERROR"
    if "WINNING" in output and returncode == 0:
        return "WINNING"
    return "ERROR"


def is_win(row: dict) -> bool:
    if row["orientation"] == "direct":
        return row["verdict"] == "WINNING"
    expected = "REALIZABLE" if row["orientation"] in {"real", "direct"} \
        else "UNREALIZABLE"
    return row["verdict"] == expected


def summary_rows(results: list[dict], baseline: str) -> list[dict]:
    base = {
        (row["spec_id"], row["orientation"], row["repetition"]): row
        for row in results if row["schedule"] == baseline
    }
    summaries = []
    for schedule in sorted({row["schedule"] for row in results}):
        selected = [row for row in results if row["schedule"] == schedule]
        wins = [row for row in selected if is_win(row)]
        losses = gains = 0
        for row in selected:
            reference = base.get(
                (row["spec_id"], row["orientation"], row["repetition"])
            )
            if reference is not None:
                losses += is_win(reference) and not is_win(row)
                gains += not is_win(reference) and is_win(row)
        conflicts = 0
        for spec_id in {row["spec_id"] for row in selected}:
            spec_wins = {
                row["orientation"] for row in selected
                if row["spec_id"] == spec_id and is_win(row)
            }
            conflicts += bool(
                "real" in spec_wins and
                any(orientation.startswith("unreal") for orientation in spec_wins)
            )
        summaries.append({
            "schedule": schedule,
            "samples": len(selected),
            "wins": len(wins),
            "timeouts": sum(row["verdict"] == "TIMEOUT" for row in selected),
            "resource_limits": sum(
                row["verdict"] == "RESOURCE_LIMIT" for row in selected
            ),
            "errors": sum(row["verdict"] == "ERROR" for row in selected),
            "baseline_losses": losses,
            "baseline_gains": gains,
            "opposite_conflicts": conflicts,
            "median_winning_seconds": (
                f"{statistics.median(float(row['seconds']) for row in wins):.6f}"
                if wins else ""
            ),
            "zero_loss_gate": str(losses == 0 and conflicts == 0).lower(),
        })
    return summaries


def main() -> int:
    args = parse_args()
    if args.timeout <= 0 or args.repetitions < 1:
        raise ValueError("timeout and repetitions must be positive")
    replay = args.acacia_replay.resolve()
    manifest = args.bundle.resolve() / "automata.tsv"
    if not replay.is_file() or not manifest.is_file():
        raise FileNotFoundError(replay if not replay.is_file() else manifest)
    with manifest.open(newline="", encoding="utf-8") as handle:
        automata = list(csv.DictReader(handle, delimiter="\t"))
    if args.schedules:
        automata = [row for row in automata if row["schedule"] in args.schedules]
    if args.orientations:
        automata = [
            row for row in automata if row["orientation"] in args.orientations
        ]
    selected_schedules = sorted({row["schedule"] for row in automata})
    if automata and args.baseline not in selected_schedules:
        raise ValueError("the selected schedules must include the baseline")
    args.output.mkdir(parents=True, exist_ok=True)
    result_path = args.output / "results.tsv"
    if result_path.exists() and not args.resume:
        raise FileExistsError(f"{result_path} exists; pass --resume")
    results = read_results(result_path)
    completed = {
        (row["spec_id"], row["schedule"], row["orientation"], row["repetition"])
        for row in results
    }
    metadata = {
        "result_schema": 2, "bundle": str(args.bundle.resolve()),
        "replay": str(replay),
        "replay_sha256": file_sha256(replay),
        "orchestrator_sha256": file_sha256(pathlib.Path(__file__)),
        "manifest_sha256": file_sha256(manifest),
        "selected_schedules": selected_schedules,
        "selected_orientations": sorted(
            {row["orientation"] for row in automata}
        ),
        "baseline": args.baseline, "timeout_seconds": args.timeout,
        "repetitions": args.repetitions, "memory_max": args.memory_max,
        "memory_swap_max": args.memory_swap_max, "spot_fast": args.spot_fast,
        "K": args.K, "systemd_scope": not args.no_systemd_scope,
    }
    metadata_path = args.output / "metadata.json"
    if metadata_path.exists() and args.resume:
        existing = json.loads(metadata_path.read_text(encoding="utf-8"))
        if existing != metadata:
            raise ValueError("resume metadata does not match this invocation")
    else:
        metadata_path.write_text(
            json.dumps(metadata, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    for index, row in enumerate(automata, 1):
        for repetition in range(1, args.repetitions + 1):
            key = (row["spec_id"], row["schedule"], row["orientation"],
                   str(repetition))
            if key in completed:
                continue
            verdict = "GENERATION_" + row.get("generation_status", "error").upper()
            seconds, returncode, timed_out = 0.0, -1, False
            resource_limited, scope_result = False, "not-run"
            stdout = stderr = ""
            if row.get("generation_status", "ok") == "ok":
                command = [
                    str(replay), "--hoa", row["hoa"], "--inputs", row["inputs"],
                    "--outputs", row["outputs"], "--orientation", row["orientation"],
                    "--spot-fast", args.spot_fast, "-K", str(args.K),
                ]
                (returncode, timed_out, resource_limited, scope_result, seconds,
                 stdout, stderr) = run_bounded(command, args)
                verdict = classify(
                    returncode, timed_out, resource_limited, stdout + stderr
                )
            result = {
                "result_schema": 2, "spec_id": row["spec_id"],
                "source": row["source"], "schedule": row["schedule"],
                "orientation": row["orientation"], "repetition": repetition,
                "generation_status": row.get("generation_status", "ok"),
                "verdict": verdict, "seconds": f"{seconds:.6f}",
                "returncode": returncode, "timed_out": str(timed_out).lower(),
                "scope_result": scope_result,
                "resource_limited": str(resource_limited).lower(),
                "stdout_sha256": hashlib.sha256(stdout.encode()).hexdigest(),
                "stderr_sha256": hashlib.sha256(stderr.encode()).hexdigest(),
            }
            results.append(result)
            completed.add(key)
            write_tsv(result_path, results, RESULT_FIELDS)
            summaries = summary_rows(results, args.baseline)
            write_tsv(args.output / "summary.tsv", summaries, tuple(summaries[0]))
            print(
                f"[{index}/{len(automata)}] {row['spec_id']} {row['schedule']} "
                f"{row['orientation']} r{repetition}: {verdict} {seconds:.3f}s",
                flush=True,
            )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"evaluate_automata_study: {error}", file=sys.stderr)
        raise SystemExit(1)
