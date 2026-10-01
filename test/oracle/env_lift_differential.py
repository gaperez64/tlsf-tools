#!/usr/bin/env python3
"""Fail on any native/prototype environment-lift stage or work mismatch."""

import argparse
import json
import os
import pathlib
import subprocess
import time


def fields(output):
    return dict(part.split("=", 1) for part in output.split()
                if "=" in part)


def reference(path):
    value = json.loads(path.read_text())
    return value[0] if isinstance(value, list) else value


def run(binary, source, output, mode):
    timing = pathlib.Path(str(output) + ".time")
    command = ["/usr/bin/time", "-f", "seconds=%e rss_kb=%M", "-o",
               str(timing), str(binary), str(source), str(output), mode]
    started = time.monotonic()
    process = subprocess.run(command, capture_output=True, text=True,
                             timeout=300, check=False)
    work = fields(process.stdout.splitlines()[0] if process.stdout else "")
    elapsed = time.monotonic() - started
    measured = fields(timing.read_text())
    return {"exit": process.returncode, "work": work,
            "error": process.stderr.strip(), "elapsed_seconds": elapsed,
            "cpu_wall_seconds": float(measured["seconds"]),
            "peak_rss_bytes": int(measured["rss_kb"]) * 1024}


def stage(result):
    return "verified" if result["exit"] == 0 else result["work"].get("stage")


def compare_work(result, expected):
    if expected["stage"] not in ("verified", "schema_capacity"):
        return True
    work = result["work"]
    nodes = int(work["nodes"])
    applies = int(work["applies"])
    original = expected["work"]
    node_gap = abs(nodes - original["bdd_nodes"])
    apply_gap = abs(applies - original["bdd_ops"])
    result["node_gap"] = node_gap
    result["apply_gap"] = apply_gap
    # Native seed AIGs can differ by a few intermediate operations. Policy
    # work may amplify that gap; 0.1% is well below either frozen budget.
    return (node_gap <= max(128, original["bdd_nodes"] // 1000) and
            apply_gap <= max(128, original["bdd_ops"] // 1000))


def marker_run(sprint, action):
    marker = sprint / "TRACKB-BUILDING"
    others = [sprint / name for name in ("DRIVER-BUILDING", "TIMED-RUN-ACTIVE")]
    token = f"env-lift-differential-{os.getpid()}"
    while marker.exists() or any(path.exists() for path in others):
        time.sleep(2)
    fd = os.open(marker, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(fd, "w") as stream:
        stream.write(token + "\n")
    try:
        if any(path.exists() for path in others):
            raise RuntimeError("another managed run started")
        return action()
    finally:
        if marker.exists() and marker.read_text().strip() == token:
            marker.unlink()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=pathlib.Path, required=True)
    parser.add_argument("--binary", type=pathlib.Path, required=True)
    parser.add_argument("--fault-binary", type=pathlib.Path, required=True)
    parser.add_argument("--real-source", type=pathlib.Path, required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    args = parser.parse_args()
    if args.out.exists() and any(args.out.iterdir()):
        raise SystemExit("output directory must be fresh")
    args.out.mkdir(parents=True, exist_ok=True)
    args.binary = args.binary.resolve()
    args.fault_binary = args.fault_binary.resolve()
    args.base = args.base.resolve()
    rows = []
    failures = []

    def verify():
        for size in (7, 9):
            directory = args.base / str(size)
            expected_rows = json.loads((directory / "summary.json").read_text())
            if len(expected_rows) != 11 or len({item["index"] for item in expected_rows}) != 11:
                raise RuntimeError(f"{size}: regular row inventory differs")
            for item in expected_rows:
                name = f"case-{item['index']:03d}"
                source = directory / name / f"{name}-target.tlsf"
                result = run(args.binary, source,
                             args.out / f"{size}-{name}", "--lift")
                result.update(size=size, row=name,
                              expected_stage=item["stage"],
                              native_stage=stage(result))
                detail = reference(directory / name / "results.json")
                good = result["native_stage"] == item["stage"]
                good &= compare_work(result, detail)
                if item["stage"] == "verified":
                    good &= (result["work"].get("checks") == "1" and
                             result["work"].get("verdict") == "0")
                if item["stage"] == "schema_capacity":
                    good &= (result["work"].get("applies") == "12000001" and
                             result["error"] ==
                             "cumulative rank apply cap exhausted at "
                             "policy_reconstruct/mode_relation mode 0" and
                             result["work"].get("checks") == "0" and
                             result["work"].get("verdict") == "4")
                if not good:
                    failures.append(f"{size}/{name}: stage, checker, phase or work")
                rows.append(result)
                print(json.dumps(result), flush=True)

            control_rows = json.loads((directory / "controls.json").read_text())
            controls = {item["case"]: item for item in control_rows}
            if len(control_rows) != 4 or len(controls) != 4:
                raise RuntimeError(f"{size}: control row inventory differs")
            cases = [
                ("renamed-case-13", args.binary,
                 directory / "renamed-case-13" / "case-000-target.tlsf",
                 "--lift"),
                ("sibling-swap", args.fault_binary,
                 directory / "case-013" / "case-013-target.tlsf",
                 "--lift-fault=5"),
                ("target-real", args.binary,
                 directory / "target-real" / "case-000-target.tlsf",
                 "--lift"),
                ("mutated-rank", args.fault_binary,
                 directory / "case-013" / "case-013-target.tlsf",
                 "--lift-fault=8")]
            for name, binary, source, mode in cases:
                result = run(binary, source, args.out / f"{size}-{name}", mode)
                expected = controls[name]
                result.update(size=size, row=name,
                              expected_stage=expected["stage"],
                              native_stage=stage(result))
                good = result["native_stage"] == expected["stage"]
                if name in ("renamed-case-13", "mutated-rank"):
                    good &= result["work"].get("checks") == "1"
                else:
                    good &= result["work"].get("checks") == "0"
                if name == "renamed-case-13":
                    good &= result["work"].get("verdict") == "0"
                    original = reference(directory / name / "results.json")
                    good &= compare_work(result, original)
                else:
                    good &= result["work"].get("verdict") == "4"
                if not good:
                    failures.append(f"{size}/{name}: control mismatch")
                rows.append(result)
                print(json.dumps(result), flush=True)

            real = args.out / f"{size}-real-seed.tlsf"
            real.write_text(args.real_source.read_text().replace(
                "width = 7", f"width = {size}"))
            result = run(args.binary, real,
                         args.out / f"{size}-real-seed", "--lift")
            result.update(size=size, row="real-seed", expected_stage="seed_check",
                          native_stage=stage(result))
            if (result["native_stage"] != "seed_check" or
                    result["work"].get("verdict") != "4"):
                failures.append(f"{size}/real-seed: control mismatch")
            rows.append(result)
            print(json.dumps(result), flush=True)
        if len(rows) != 32:
            failures.append("total row inventory differs")
        (args.out / "all-results.json").write_text(json.dumps(rows, indent=2))
        (args.out / "failures.json").write_text(json.dumps(failures, indent=2))
        if failures:
            raise SystemExit("\n".join(failures))

    marker_run(pathlib.Path(__file__).resolve().parents[3], verify)


if __name__ == "__main__":
    main()
