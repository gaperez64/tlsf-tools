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


LABEL_CHARS = frozenset("abcdefghijklmnopqrstuvwxyz0123456789-_")
CAMPAIGN_OPTIONS = (
    "--game-profile",
    "--oxidd-nodes",
    "--oxidd-cache",
    "--oxidd-gc",
    "--oxidd-gc-threshold",
    "--oxidd-transitions",
    "--realizability-only",
)
GROUP_FIELDS = (
    "instance",
    "input_sha256",
    "variant",
    "binary_sha256",
    "variable_order",
    "order_file_sha256",
    "build_plan",
    "plan_version",
    "profile",
    "nodes",
    "cache",
    "gc",
    "gc_threshold",
    "transitions",
    "mode",
)
ISSUE24_EXPECTED = {
    "beemprdcell2f1_c0to1": "REALIZABLE",
    "beemprdcell2f1_c0to3": "REALIZABLE",
    "beemprdcell2f1_c0to7": "REALIZABLE",
    "driver_c2y": "UNREALIZABLE",
    "driver_c2n": "UNREALIZABLE",
}


def fingerprint(path):
    path = Path(path).resolve(strict=True)
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return {"path": str(path), "sha256": digest.hexdigest()}


def checked_label(label):
    return (isinstance(label, str) and bool(label) and
            all(character in LABEL_CHARS for character in label))


def option_value(arguments, index, name):
    argument = arguments[index]
    if argument == name:
        if index + 1 >= len(arguments):
            raise ValueError(f"{name} requires a value")
        return arguments[index + 1], 2
    prefix = name + "="
    if argument.startswith(prefix):
        return argument[len(prefix):], 1
    return None, 0


def normalize_variant_args(arguments, base_directory):
    """Validate experiment-owned arguments and derive grouping metadata."""
    if not isinstance(arguments, list) or not all(
            isinstance(arg, str) for arg in arguments):
        raise ValueError("variant args must be an array of strings")
    normalized = []
    order = "input-first"
    plan = "gates"
    order_file = None
    named_order = False
    plan_supplied = False
    index = 0
    while index < len(arguments):
        argument = arguments[index]
        if not argument or "\0" in argument:
            raise ValueError("variant args may not be empty or contain NUL")
        if any(argument == name or argument.startswith(name + "=")
               for name in CAMPAIGN_OPTIONS):
            raise ValueError(f"campaign-owned option in variant args: {argument}")
        value, consumed = option_value(arguments, index, "--oxidd-var-order")
        if consumed:
            if named_order or order_file:
                raise ValueError("duplicate or conflicting variable-order option")
            if value not in ("input-first", "state-first", "fanin-dfs"):
                raise ValueError(f"invalid variable order: {value}")
            order = value
            named_order = True
            normalized.append(f"--oxidd-var-order={value}")
            index += consumed
            continue
        value, consumed = option_value(arguments, index, "--oxidd-order-file")
        if consumed:
            if named_order or order_file or not value:
                raise ValueError("duplicate or conflicting order file")
            path = Path(value)
            if not path.is_absolute():
                path = base_directory / path
            order_file = fingerprint(path)
            order = "custom"
            normalized.append(f"--oxidd-order-file={order_file['path']}")
            index += consumed
            continue
        value, consumed = option_value(arguments, index, "--oxidd-build-plan")
        if consumed:
            if plan_supplied:
                raise ValueError("duplicate build-plan option")
            if value not in ("gates", "fused-original", "guard-first"):
                raise ValueError(f"invalid build plan: {value}")
            plan = value
            plan_supplied = True
            normalized.append(f"--oxidd-build-plan={value}")
            index += consumed
            continue
        if argument.startswith("-"):
            raise ValueError(f"unsupported per-variant option: {argument}")
        raise ValueError(f"input path is campaign-owned: {argument}")
    return normalized, {
        "variable_order": order,
        "order_file": order_file,
        "build_plan": plan,
        "plan_version": 1,
    }


def load_variants(solver_specs, config_path):
    variants = {}
    if config_path:
        config_path = Path(config_path).resolve(strict=True)
        try:
            config = json.loads(config_path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise ValueError(f"cannot read variant config: {error}") from error
        if not isinstance(config, dict) or config.get("schema") != 1:
            raise ValueError("variant config must be an object with schema 1")
        entries = config.get("variants")
        if not isinstance(entries, list) or not entries:
            raise ValueError("variant config must contain a non-empty variants array")
        for entry in entries:
            if not isinstance(entry, dict):
                raise ValueError("each variant must be an object")
            label, solver = entry.get("label"), entry.get("solver")
            if not checked_label(label):
                raise ValueError("variant labels must use lowercase letters, digits, '-' or '_'")
            if label in variants:
                raise ValueError(f"duplicate variant label: {label}")
            if not isinstance(solver, str) or not Path(solver).is_absolute():
                raise ValueError(f"variant solver must be an absolute path: {label}")
            arguments, metadata = normalize_variant_args(
                entry.get("args"), config_path.parent)
            variants[label] = {**fingerprint(solver), "args": arguments, **metadata}
    else:
        for item in solver_specs:
            label, separator, path = item.partition("=")
            if not separator or not checked_label(label):
                raise ValueError("solver labels must use lowercase letters, digits, '-' or '_'")
            if label in variants:
                raise ValueError(f"duplicate solver label: {label}")
            arguments, metadata = normalize_variant_args([], Path.cwd())
            variants[label] = {**fingerprint(path), "args": arguments, **metadata}
    return variants


def load_inputs(corpus, manifest_path, requested_cases):
    custom_manifest = manifest_path is not None
    if manifest_path:
        manifest_path = Path(manifest_path).resolve(strict=True)
        try:
            manifest = json.loads(manifest_path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise ValueError(f"cannot read input manifest: {error}") from error
        if not isinstance(manifest, dict) or manifest.get("schema") != 1:
            raise ValueError("input manifest must be an object with schema 1")
        source_commit = manifest.get("source_commit")
        cases = manifest.get("cases")
        if not isinstance(source_commit, str) or not isinstance(cases, list) or not cases:
            raise ValueError("input manifest needs source_commit and non-empty cases")
    else:
        manifest_path = None
        source_commit = COMMIT
        cases = [
            {
                "path": upstream,
                "file": Path(upstream).name,
                "git_blob_sha1": expected,
                "expected_status": ISSUE24_EXPECTED[Path(upstream).stem],
            }
            for upstream, expected in CASES
        ]
    known = set()
    inputs = []
    for case in cases:
        if not isinstance(case, dict):
            raise ValueError("each input manifest case must be an object")
        upstream = case.get("path")
        filename = case.get("file")
        expected_blob = case.get("git_blob_sha1")
        expected_sha256 = case.get("sha256")
        expected_status = case.get("expected_status")
        if (not isinstance(upstream, str) or not isinstance(filename, str) or
                not filename or Path(filename).name != filename or
                not isinstance(expected_blob, str) or
                (custom_manifest and
                 (not isinstance(expected_sha256, str) or
                  len(expected_sha256) != 64 or
                  any(character not in "0123456789abcdef"
                      for character in expected_sha256))) or
                expected_status not in (None, "REALIZABLE", "UNREALIZABLE")):
            raise ValueError("invalid input manifest case")
        name = Path(filename).stem
        if name in known:
            raise ValueError(f"duplicate input case basename: {name}")
        known.add(name)
        if requested_cases and name not in requested_cases:
            continue
        path = Path(corpus) / filename
        data = path.read_bytes()
        if git_blob_sha(data) != expected_blob:
            raise ValueError(f"corpus blob mismatch: {path}")
        file_data = fingerprint(path)
        if expected_sha256 and file_data["sha256"] != expected_sha256:
            raise ValueError(f"corpus SHA-256 mismatch: {path}")
        inputs.append({"instance": upstream, "expected_status": expected_status,
                       **file_data})
    if requested_cases and set(requested_cases) != known & set(requested_cases):
        raise ValueError("unknown case name")
    return inputs, source_commit, (fingerprint(manifest_path)
                                   if manifest_path else None)


def metric_summary(samples, field):
    values = [sample[field] for sample in samples if sample.get(field) is not None]
    if not values:
        return None
    return {"min": min(values), "median": statistics.median(values),
            "max": max(values)}


def summarize(records):
    groups = collections.defaultdict(list)
    for record in records:
        groups[tuple(record[field] for field in GROUP_FIELDS)].append(record)
    rows = []
    for key, samples in sorted(groups.items()):
        completed = [sample for sample in samples
                     if sample["status"] in ("REALIZABLE", "UNREALIZABLE")]
        failed = [sample for sample in samples if sample not in completed]
        row = dict(zip(GROUP_FIELDS, key))
        row.update({
            "attempted_runs": len(samples),
            "completed_runs": len(completed),
            "completed_statuses": sorted({sample["status"] for sample in completed}),
            "rss_kib": metric_summary(completed, "rss_kib"),
            "elapsed_s": metric_summary(completed, "elapsed_s"),
            "failures": [
                {
                    "status": status,
                    "runs": len(status_samples),
                    "rss_kib": metric_summary(status_samples, "rss_kib"),
                    "elapsed_s": metric_summary(status_samples, "elapsed_s"),
                }
                for status, status_samples in sorted(
                    (status, [sample for sample in failed if sample["status"] == status])
                    for status in {sample["status"] for sample in failed})
            ],
        })
        rows.append(row)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    variants = parser.add_mutually_exclusive_group(required=True)
    variants.add_argument("--solver", action="append", metavar="LABEL=PATH")
    variants.add_argument("--variant-config", type=Path)
    parser.add_argument("--corpus", required=True, type=Path)
    parser.add_argument("--input-manifest", type=Path,
                        help="schema-1 pinned corpus manifest (default: issue-24)")
    parser.add_argument("--out", required=True, type=Path, help="new result directory")
    parser.add_argument("--nodes", nargs="+", type=int, default=[8388608, 16777216, 33554432])
    parser.add_argument("--cache", type=int, default=4194304)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--gc", choices=("auto", "pressure"), default="auto")
    parser.add_argument("--gc-threshold", type=int, default=80)
    parser.add_argument("--transitions", choices=("eager", "demand"))
    parser.add_argument("--realizability-only", action="store_true")
    parser.add_argument("--cases", nargs="+", help="optional case basenames without .aag")
    args = parser.parse_args()
    if (min(args.nodes + [args.cache, args.repetitions, args.gc_threshold]) <= 0
            or args.gc_threshold > 100
            or not math.isfinite(args.timeout) or args.timeout <= 0):
        parser.error("capacities, repetitions, and timeout must be positive and finite")
    timer = Path("/usr/bin/time")
    timeout = shutil.which("timeout")
    if not timer.is_file() or timeout is None:
        parser.error("GNU time (/usr/bin/time) and timeout are required")
    try:
        solvers = load_variants(args.solver, args.variant_config)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    try:
        inputs, corpus_commit, input_manifest = load_inputs(
            args.corpus, args.input_manifest, args.cases)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    manifest = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform": platform.platform(), "machine": platform.machine(),
        "cpu_count": os.cpu_count(), "corpus_commit": corpus_commit,
        "input_manifest": input_manifest,
        "solvers": solvers, "inputs": inputs, "runner": fingerprint(__file__),
        "variant_config": (fingerprint(args.variant_config)
                           if args.variant_config else None),
        "nodes": args.nodes, "cache": args.cache, "gc": args.gc,
        "gc_threshold": args.gc_threshold,
        "transitions": args.transitions or "eager",
        "realizability_only": args.realizability_only,
        "repetitions": args.repetitions, "timeout_seconds": args.timeout,
        "time_version": subprocess.check_output([str(timer), "--version"], text=True).splitlines()[0],
        "rss_scope": "Linux ru_maxrss via GNU time %M, KiB, per timeout/solver process tree",
        "external_process_limit": None,
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
                                   *solvers[variant]["args"],
                                   "--game-profile=legacy-safety", "--oxidd-nodes", str(nodes),
                                   "--oxidd-cache", str(args.cache), f"--oxidd-gc={args.gc}",
                                   f"--oxidd-gc-threshold={args.gc_threshold}",
                                   f"--oxidd-transitions={args.transitions or 'eager'}"]
                        if args.realizability_only:
                            command += ["--realizability-only"]
                        command += [case["path"]]
                        with (run_dir / "stdout.aag").open("wb") as stdout:
                            with (run_dir / "stderr.log").open("wb") as stderr:
                                proc = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
                        usage = {}
                        usage_error = None
                        try:
                            usage = json.loads((run_dir / "usage.json").read_text())
                        except (OSError, json.JSONDecodeError) as error:
                            usage_error = str(error)
                        if proc.returncode == 0:
                            status = "REALIZABLE"
                        elif proc.returncode == 1:
                            status = "UNREALIZABLE"
                        elif proc.returncode == 2:
                            status = "SOLVER_ERROR"
                        elif proc.returncode == 124:
                            status = "TIMEOUT"
                        elif proc.returncode == 137:
                            status = "KILLED"
                        elif proc.returncode < 0 or proc.returncode >= 128:
                            status = "SIGNAL_TERMINATION"
                        else:
                            status = "PROCESS_ERROR"
                        malformed = None
                        if status == "REALIZABLE" and not args.realizability_only:
                            with (run_dir / "stdout.aag").open("rb") as stream:
                                if not stream.read(4) == b"aag ":
                                    malformed = "missing strategy"
                        if status == "REALIZABLE" and args.realizability_only:
                            if ((run_dir / "stdout.aag").stat().st_size or
                                    "REALIZABLE" not in (run_dir / "stderr.log").read_text()):
                                malformed = "invalid verdict-only result"
                        if status == "UNREALIZABLE" and "UNREALIZABLE" not in (run_dir / "stderr.log").read_text():
                            malformed = "missing losing verdict"
                        if malformed:
                            status = "MALFORMED_OUTPUT"
                        semantic_mismatch = (
                            case["expected_status"] is not None and
                            status in ("REALIZABLE", "UNREALIZABLE") and
                            status != case["expected_status"])
                        if semantic_mismatch:
                            malformed = (f"expected {case['expected_status']}, got {status}")
                            status = "SEMANTIC_MISMATCH"
                        variant_data = solvers[variant]
                        time_exit_code = usage.get("exit_code")
                        record = {"instance": case["instance"],
                                  "input_sha256": case["sha256"], "variant": variant,
                                  "binary_sha256": variant_data["sha256"],
                                  "solver_args": variant_data["args"],
                                  "variable_order": variant_data["variable_order"],
                                  "order_file_sha256": (variant_data["order_file"] or {}).get("sha256"),
                                  "build_plan": variant_data["build_plan"],
                                  "plan_version": variant_data["plan_version"],
                                  "profile": "legacy-safety",
                                  "nodes": nodes, "cache": args.cache, "repetition": repeat + 1,
                                  "gc": args.gc, "gc_threshold": args.gc_threshold,
                                  "transitions": args.transitions or "eager",
                                  "mode": ("verdict-only" if args.realizability_only else "full"),
                                  "status": status, "command": command, "artifacts": name,
                                  "process_returncode": proc.returncode,
                                  "usage_status_consistent": (time_exit_code is None or
                                                              time_exit_code == proc.returncode),
                                  "stdout_sha256": fingerprint(run_dir / "stdout.aag")["sha256"],
                                  "stderr": (run_dir / "stderr.log").read_text(errors="replace"),
                                  "usage_error": usage_error,
                                  "malformed_reason": malformed, **usage}
                        records.append(record)
                        journal.write(json.dumps(record) + "\n")
                        journal.flush()
                        rss = (f"{usage['rss_kib'] / 1024:.1f} MiB"
                               if "rss_kib" in usage else "RSS unavailable")
                        elapsed = (f"{usage['elapsed_s']:.2f}s"
                                   if "elapsed_s" in usage else "time unavailable")
                        print(f"{name}: {status}, {rss}, {elapsed}", flush=True)
                        (out / "summary.json").write_text(
                            json.dumps(summarize(records), indent=2) + "\n")
                        if malformed:
                            raise RuntimeError(f"{malformed}: {name}")
    (out / "summary.json").write_text(json.dumps(summarize(records), indent=2) + "\n")


if __name__ == "__main__":
    main()
