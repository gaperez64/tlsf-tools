#!/usr/bin/env python3
"""Generate durable, Acacia-compatible HOA bundles for TLSF schedules.

Normalization and automaton construction are deliberately separate stages.
The resulting manifest contains both source-only schedule metadata and
automaton measurements, while selector training is restricted to the
``guard_`` columns emitted independently by ``tlsfbenchgraph``.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import pathlib
import subprocess
import sys
import time


DEFAULT_SCHEDULES = (
    "off=|",
    "split=|split",
    "split-safe=|split,nnf,weak,bool-canon",
    "pre-match=pre-safe|split,match-safe",
    "route=|split,route-safe",
    "sickert-1=|split,sickert-bounded:1",
    "sickert-2=|split,sickert-bounded:2",
)
AUTOMATON_FIELDS = (
    "schema_version",
    "name",
    "schedule",
    "orientation",
    "preference",
    "inputs",
    "outputs",
    "formula_nodes",
    "states",
    "edges",
    "acceptance_sets",
    "sccs",
    "state_acc",
    "deterministic",
    "complete",
    "universal",
    "hoa",
)


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_schedule(text: str) -> tuple[str, str, str]:
    name, separator, passes = text.partition("=")
    if not separator or not name:
        raise argparse.ArgumentTypeError("schedule must be NAME=PRE|POST")
    pre, separator, post = passes.partition("|")
    if not separator:
        raise argparse.ArgumentTypeError("schedule must contain a | separator")
    return name, pre, post


def collect_specs(corpus: pathlib.Path | None, file_list: pathlib.Path | None,
                  explicit: list[pathlib.Path]) -> list[pathlib.Path]:
    specs = [path.resolve() for path in explicit]
    if corpus:
        specs.extend(sorted(path.resolve() for path in corpus.rglob("*.tlsf")))
    if file_list:
        for raw in file_list.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if line and not line.startswith("#"):
                specs.append(pathlib.Path(line).resolve())
    return sorted(dict.fromkeys(specs))


def run(command: list[str], timeout: float, *, capture: bool = False) -> str:
    result = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE if capture else subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    if result.returncode != 0:
        detail = result.stderr.strip().splitlines()
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(command)}"
            + (f": {detail[-1]}" if detail else "")
        )
    return result.stdout.strip() if capture else ""


def tool_version(tool: pathlib.Path) -> str:
    return run([str(tool), "--version"], 30, capture=True)


def write_tsv(path: pathlib.Path, rows: list[dict], fields: tuple[str, ...]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, delimiter="\t", fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("specs", nargs="*", type=pathlib.Path)
    parser.add_argument("--corpus", type=pathlib.Path)
    parser.add_argument("--file-list", type=pathlib.Path)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    parser.add_argument("--tlsfnorm", required=True, type=pathlib.Path)
    parser.add_argument("--tlsf2ltl", required=True, type=pathlib.Path)
    parser.add_argument("--tlsfinfo", required=True, type=pathlib.Path)
    parser.add_argument("--tlsfbenchgraph", required=True, type=pathlib.Path)
    parser.add_argument("--automata-generator", required=True, type=pathlib.Path)
    parser.add_argument(
        "--schedule", action="append", type=parse_schedule, dest="schedules"
    )
    parser.add_argument(
        "--orientation",
        action="append",
        choices=("real", "unreal-formula", "unreal-automaton", "direct"),
        dest="orientations",
    )
    parser.add_argument(
        "--preference", choices=("any", "small", "deterministic"), default="small"
    )
    parser.add_argument("--no-realizability-simplify", action="store_true")
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--resume", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    tools = {
        "tlsfnorm": args.tlsfnorm.resolve(),
        "tlsf2ltl": args.tlsf2ltl.resolve(),
        "tlsfinfo": args.tlsfinfo.resolve(),
        "tlsfbenchgraph": args.tlsfbenchgraph.resolve(),
        "automata_generator": args.automata_generator.resolve(),
    }
    for tool in tools.values():
        if not tool.is_file():
            raise FileNotFoundError(tool)
    schedules = args.schedules or [parse_schedule(value) for value in DEFAULT_SCHEDULES]
    if len({name for name, _, _ in schedules}) != len(schedules):
        raise ValueError("schedule names must be unique")
    orientations = args.orientations or [
        "real",
        "unreal-formula",
        "unreal-automaton",
    ]
    specs = collect_specs(args.corpus, args.file_list, args.specs)
    if args.limit:
        specs = specs[: args.limit]
    if not specs:
        raise ValueError("no TLSF specifications")

    output = args.output.resolve()
    manifest_path = output / "automata.tsv"
    if output.exists() and not args.resume:
        raise FileExistsError(f"{output} exists; pass --resume to continue")
    output.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    if manifest_path.exists():
        with manifest_path.open(newline="", encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle, delimiter="\t"))
    fields = (
        "bundle_schema",
        "spec_id",
        "source",
        "source_sha256",
        "pre_schedule",
        "post_schedule",
        "generation_status",
        "generation_seconds",
        "generation_error",
        *AUTOMATON_FIELDS,
    )
    completed = {
        (row["spec_id"], row["schedule"], row["orientation"]) for row in rows
    }
    metadata = {
        "bundle_schema": 2,
        "generator_sha256": sha256(pathlib.Path(__file__)),
        "specs": [
            {"path": str(source), "sha256": sha256(source)} for source in specs
        ],
        "schedules": [
            {"name": name, "pre": pre, "post": post}
            for name, pre, post in schedules
        ],
        "orientations": orientations,
        "preference": args.preference,
        "realizability_simplify": not args.no_realizability_simplify,
        "tools": {
            name: {
                "path": str(path),
                "version": tool_version(path),
                "sha256": sha256(path),
            }
            for name, path in tools.items()
        },
    }
    metadata_path = output / "metadata.json"
    if metadata_path.exists() and args.resume:
        existing = json.loads(metadata_path.read_text(encoding="utf-8"))
        if existing != metadata:
            raise ValueError("resume metadata does not match this invocation")
    else:
        metadata_path.write_text(
            json.dumps(metadata, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    # Persist one source-only feature row per specification.  These rows are
    # deliberately generated before and independently of every schedule, HOA,
    # and replay result so they form a leakage-free selector input table.
    feature_path = output / "source-features.tsv"
    feature_rows: list[dict] = []
    feature_fields: tuple[str, ...] | None = None
    for source in specs:
        lines = run(
            [str(tools["tlsfbenchgraph"]), "--source-features", str(source)],
            args.timeout,
            capture=True,
        ).splitlines()
        if len(lines) != 2:
            raise ValueError("tlsfbenchgraph returned an incompatible row count")
        raw_names = tuple(lines[0].split("\t"))
        raw_values = lines[1].split("\t")
        if len(raw_names) != len(raw_values):
            raise ValueError("tlsfbenchgraph returned an incompatible schema")
        raw_row = dict(zip(raw_names, raw_values, strict=True))
        # Keep the selector table admissible by construction, not merely by
        # convention.  Template recognizers and residual measurements in the
        # full benchgraph schema depend on processing choices and are omitted.
        names = tuple(
            name for name in raw_names
            if name in {"schema_version", "inputs", "outputs"}
            or name.startswith("guard_")
        )
        raw_feature = {name: raw_row[name] for name in names}
        current_feature_fields = (
            "bundle_schema", "spec_id", "source_sha256", *names
        )
        if feature_fields is None:
            feature_fields = current_feature_fields
        elif feature_fields != current_feature_fields:
            raise ValueError("tlsfbenchgraph schema changed within one bundle")
        digest = sha256(source)
        feature_rows.append(
            {
                "bundle_schema": 2,
                "spec_id": digest[:16],
                "source_sha256": digest,
                **raw_feature,
            }
        )
    assert feature_fields is not None
    write_tsv(feature_path, feature_rows, feature_fields)

    for index, source in enumerate(specs, 1):
        source_digest = sha256(source)
        spec_id = source_digest[:16]
        for schedule_name, pre_schedule, post_schedule in schedules:
            bundle = output / "bundles" / spec_id / schedule_name
            bundle.mkdir(parents=True, exist_ok=True)
            normalized = source
            if pre_schedule or post_schedule:
                normalized = bundle / "normalized.tlsf"
                command = [str(tools["tlsfnorm"])]
                if pre_schedule:
                    command.extend(["--pre-passes", pre_schedule])
                if post_schedule:
                    command.extend(["--passes", post_schedule])
                command.extend(["--output", str(normalized), str(source)])
                run(command, args.timeout)
            formula = bundle / "formula.ltl"
            run(
                [
                    str(tools["tlsf2ltl"]),
                    "--format",
                    "ltlxba",
                    "--output",
                    str(formula),
                    str(normalized),
                ],
                args.timeout,
            )
            inputs = run(
                [str(tools["tlsfinfo"]), "--expanded-ins", str(normalized)],
                args.timeout,
                capture=True,
            )
            outputs = run(
                [str(tools["tlsfinfo"]), "--expanded-outs", str(normalized)],
                args.timeout,
                capture=True,
            )
            for orientation in orientations:
                key = (spec_id, schedule_name, orientation)
                if key in completed:
                    continue
                hoa = bundle / f"{orientation}.hoa"
                command = [
                    str(tools["automata_generator"]),
                    "--formula",
                    str(formula),
                    "--hoa",
                    str(hoa),
                    "--name",
                    spec_id,
                    "--schedule",
                    schedule_name,
                    "--inputs",
                    inputs,
                    "--outputs",
                    outputs,
                    "--orientation",
                    orientation,
                    "--preference",
                    args.preference,
                    "--no-header",
                ]
                if not args.no_realizability_simplify:
                    command.append("--realizability-simplify")
                started = time.monotonic()
                status = "ok"
                error = ""
                try:
                    metric_values = run(command, args.timeout, capture=True).split("\t")
                    if len(metric_values) != len(AUTOMATON_FIELDS):
                        raise ValueError(
                            "automata generator returned an incompatible schema"
                        )
                    metric = dict(zip(AUTOMATON_FIELDS, metric_values, strict=True))
                except subprocess.TimeoutExpired:
                    status = "timeout"
                    error = f"translation exceeded {args.timeout:g}s"
                    metric = {field: "" for field in AUTOMATON_FIELDS}
                    hoa.unlink(missing_ok=True)
                except (OSError, RuntimeError, ValueError) as failure:
                    status = "error"
                    error = str(failure).replace("\t", " ").replace("\n", " ")[:500]
                    metric = {field: "" for field in AUTOMATON_FIELDS}
                    hoa.unlink(missing_ok=True)
                row = {
                    "bundle_schema": 2,
                    "spec_id": spec_id,
                    "source": str(source),
                    "source_sha256": source_digest,
                    "pre_schedule": pre_schedule,
                    "post_schedule": post_schedule,
                    "generation_status": status,
                    "generation_seconds": f"{time.monotonic() - started:.6f}",
                    "generation_error": error,
                    **metric,
                }
                rows.append(row)
                completed.add(key)
                write_tsv(manifest_path, rows, fields)
                detail = (
                    f"{metric['states']} states/{metric['edges']} edges"
                    if status == "ok"
                    else status
                )
                print(
                    f"[{index}/{len(specs)}] {spec_id} {schedule_name} "
                    f"{orientation}: {detail}",
                    flush=True,
                )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"automata_study: {error}", file=sys.stderr)
        raise SystemExit(1)
