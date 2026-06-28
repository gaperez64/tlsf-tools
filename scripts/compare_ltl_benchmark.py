#!/usr/bin/env python3
"""Compare template recognition and OxiDD routing on a TLSF corpus.

Typical use:

  scripts/compare_ltl_benchmark.py \
    --baseline-build /tmp/tlsf-tools-main-build \
    --current-build /tmp/tlsf-tools-section-build \
    --out /tmp/ltl-benchmark.compare.tsv \
    /path/to/ltl-benchmark

The script compares two tool builds over the same corpus:
  * tlsftemplates: candidate/certified/solved template counts.
  * tlsfcompose --route-stats: exact OxiDD versus external residual routing.
"""

from __future__ import annotations

import argparse
import csv
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path


BLOCKS_RE = re.compile(
    r"blocks:\s+(?P<blocks>\d+)\s+\(solved\s+(?P<solved>\d+),\s+"
    r"certified\s+(?P<certified>\d+),\s+candidate\s+(?P<candidate>\d+)\)"
)
RESIDUAL_RE = re.compile(r"residual constraints:\s+(?P<residual>\d+)")
BLOCK_LINE_RE = re.compile(r"\s+\[(?P<status>[^\]]+)\]\s+(?P<name>\S+)")


@dataclass
class TemplateMetrics:
    status: str = "not-run"
    blocks: int = 0
    solved: int = 0
    certified: int = 0
    candidate: int = 0
    residual: int = 0
    accepted: int = 0
    conflicts: int = 0
    timeout: bool = False
    error: str = ""
    by_status: dict[str, Counter] = field(default_factory=dict)


@dataclass
class RouteMetrics:
    status: str = "not-run"
    clusters: int = 0
    oxidd_clusters: int = 0
    exact_oxidd_clusters: int = 0
    external_clusters: int = 0
    total_nodes: int = 0
    oxidd_nodes: int = 0
    external_nodes: int = 0
    max_outputs_external: int = 0
    timeout: bool = False
    error: str = ""
    routes: Counter = field(default_factory=Counter)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def default_corpus() -> list[str]:
    path = repo_root() / "benchmarks" / "tlsf"
    return [str(path)] if path.exists() else []


def exe_from_build(build: str | None, name: str) -> str | None:
    if not build:
        return None
    return str(Path(build) / name)


def default_current_tool(name: str) -> str:
    for build in ("build-oxidd", "build-research", "build"):
        path = repo_root() / build / name
        if path.exists():
            return str(path)
    return name


def is_discoverable_tlsf(path: str) -> bool:
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


def discover(paths: list[str]) -> list[str]:
    files: list[str] = []
    for item in paths:
        if os.path.isdir(item):
            for root, _, names in os.walk(item):
                for name in names:
                    path = os.path.join(root, name)
                    if is_discoverable_tlsf(path):
                        files.append(path)
        else:
            files.append(item)
    return sorted(dict.fromkeys(files))


def run_cmd(cmd: list[str], timeout: float | None):
    try:
        return subprocess.run(
            cmd,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return exc


def short_error(stderr: str) -> str:
    lines = [line.strip() for line in stderr.splitlines() if line.strip()]
    return lines[0] if lines else "failed"


def parse_templates(text: str) -> TemplateMetrics:
    m = TemplateMetrics(status="ok")
    for line in text.splitlines():
        blocks = BLOCKS_RE.search(line)
        if blocks:
            m.blocks = int(blocks.group("blocks"))
            m.solved = int(blocks.group("solved"))
            m.certified = int(blocks.group("certified"))
            m.candidate = int(blocks.group("candidate"))
            continue
        residual = RESIDUAL_RE.search(line)
        if residual:
            m.residual = int(residual.group("residual"))
            continue
        block = BLOCK_LINE_RE.match(line)
        if block:
            status = block.group("status")
            name = block.group("name")
            m.by_status.setdefault(status, Counter())[name] += 1
            continue
        if line.startswith("composition: residual="):
            parts = dict(
                item.split("=", 1)
                for item in line.removeprefix("composition: ").split()
                if "=" in item
            )
            m.accepted = int(parts.get("accepted", "0"))
            m.conflicts = int(parts.get("conflicts", "0"))
        elif line.startswith("composition: fully-solved"):
            m.accepted = m.solved
            m.conflicts = 0
    return m


def run_templates(exe: str, path: str, timeout: float | None) -> TemplateMetrics:
    proc = run_cmd(
        [
            exe,
            "--split",
            "--certify",
            "--solve",
            "--check",
            "--format",
            "text",
            path,
        ],
        timeout,
    )
    if isinstance(proc, subprocess.TimeoutExpired):
        return TemplateMetrics(status="timeout", timeout=True)
    if proc.returncode != 0:
        return TemplateMetrics(status="error", error=short_error(proc.stderr))
    return parse_templates(proc.stdout)


def to_int(row: dict[str, str], key: str, default: int = 0) -> int:
    val = row.get(key, "")
    return default if val in ("", "-", None) else int(val)


def row_uses_oxidd(row: dict[str, str]) -> bool:
    uses = row.get("uses_oxidd")
    if uses in ("0", "1"):
        return uses == "1"
    return row.get("backend", "").startswith("OxiDD")


def row_exact_oxidd(row: dict[str, str]) -> bool:
    return row_uses_oxidd(row) and row.get("exact") == "1"


def parse_routes(text: str) -> RouteMetrics:
    lines = [line for line in text.splitlines() if line.strip()]
    if not lines:
        return RouteMetrics(status="ok")
    rows = list(csv.DictReader(lines, delimiter="\t"))
    m = RouteMetrics(status="ok")
    m.clusters = len(rows)
    for row in rows:
        uses = row_uses_oxidd(row)
        exact = row_exact_oxidd(row)
        nodes = to_int(row, "formula_nodes", to_int(row, "nodes"))
        outputs = to_int(row, "n_outputs", to_int(row, "n_outs"))
        m.total_nodes += nodes
        m.routes[row.get("route", "") or "-"] += 1
        if uses:
            m.oxidd_clusters += 1
            m.oxidd_nodes += nodes
            if exact:
                m.exact_oxidd_clusters += 1
        else:
            m.external_clusters += 1
            m.external_nodes += nodes
            m.max_outputs_external = max(m.max_outputs_external, outputs)
    return m


def run_routes(exe: str, path: str, timeout: float | None) -> RouteMetrics:
    proc = run_cmd([exe, "--split", "--route-stats", path], timeout)
    if isinstance(proc, subprocess.TimeoutExpired):
        return RouteMetrics(status="timeout", timeout=True)
    if proc.returncode != 0:
        status = "error"
        if "trusted UNREAL" in proc.stderr or "trusted one-sided" in proc.stderr:
            status = "trusted-unreal"
        return RouteMetrics(status=status, error=short_error(proc.stderr))
    return parse_routes(proc.stdout)


def counter_string(c: Counter) -> str:
    return ",".join(f"{k}:{v}" for k, v in sorted(c.items())) or "-"


def template_names_string(m: TemplateMetrics, status: str) -> str:
    return counter_string(m.by_status.get(status, Counter()))


FIELDS = [
    "file",
    "template_status_base",
    "template_status_curr",
    "base_solved",
    "curr_solved",
    "delta_solved",
    "base_certified",
    "curr_certified",
    "delta_certified",
    "base_candidate",
    "curr_candidate",
    "delta_candidate",
    "base_residual_constraints",
    "curr_residual_constraints",
    "delta_residual_constraints",
    "base_solved_templates",
    "curr_solved_templates",
    "route_status_base",
    "route_status_curr",
    "base_clusters",
    "curr_clusters",
    "base_exact_oxidd_clusters",
    "curr_exact_oxidd_clusters",
    "delta_exact_oxidd_clusters",
    "base_oxidd_clusters",
    "curr_oxidd_clusters",
    "delta_oxidd_clusters",
    "base_external_clusters",
    "curr_external_clusters",
    "delta_external_clusters",
    "base_external_nodes",
    "curr_external_nodes",
    "delta_external_nodes",
    "base_max_outputs_external",
    "curr_max_outputs_external",
    "base_routes",
    "curr_routes",
    "base_template_error",
    "curr_template_error",
    "base_route_error",
    "curr_route_error",
]


def row_for(path: str, bt: TemplateMetrics, ct: TemplateMetrics,
            br: RouteMetrics, cr: RouteMetrics) -> dict[str, object]:
    return {
        "file": path,
        "template_status_base": bt.status,
        "template_status_curr": ct.status,
        "base_solved": bt.solved,
        "curr_solved": ct.solved,
        "delta_solved": ct.solved - bt.solved,
        "base_certified": bt.certified,
        "curr_certified": ct.certified,
        "delta_certified": ct.certified - bt.certified,
        "base_candidate": bt.candidate,
        "curr_candidate": ct.candidate,
        "delta_candidate": ct.candidate - bt.candidate,
        "base_residual_constraints": bt.residual,
        "curr_residual_constraints": ct.residual,
        "delta_residual_constraints": ct.residual - bt.residual,
        "base_solved_templates": template_names_string(bt, "solved"),
        "curr_solved_templates": template_names_string(ct, "solved"),
        "route_status_base": br.status,
        "route_status_curr": cr.status,
        "base_clusters": br.clusters,
        "curr_clusters": cr.clusters,
        "base_exact_oxidd_clusters": br.exact_oxidd_clusters,
        "curr_exact_oxidd_clusters": cr.exact_oxidd_clusters,
        "delta_exact_oxidd_clusters": cr.exact_oxidd_clusters
        - br.exact_oxidd_clusters,
        "base_oxidd_clusters": br.oxidd_clusters,
        "curr_oxidd_clusters": cr.oxidd_clusters,
        "delta_oxidd_clusters": cr.oxidd_clusters - br.oxidd_clusters,
        "base_external_clusters": br.external_clusters,
        "curr_external_clusters": cr.external_clusters,
        "delta_external_clusters": cr.external_clusters - br.external_clusters,
        "base_external_nodes": br.external_nodes,
        "curr_external_nodes": cr.external_nodes,
        "delta_external_nodes": cr.external_nodes - br.external_nodes,
        "base_max_outputs_external": br.max_outputs_external,
        "curr_max_outputs_external": cr.max_outputs_external,
        "base_routes": counter_string(br.routes),
        "curr_routes": counter_string(cr.routes),
        "base_template_error": bt.error,
        "curr_template_error": ct.error,
        "base_route_error": br.error,
        "curr_route_error": cr.error,
    }


def print_summary(rows: list[dict[str, object]]) -> None:
    def total(key: str) -> int:
        return sum(int(row[key]) for row in rows)

    ok_templates = sum(
        1
        for row in rows
        if row["template_status_base"] == "ok" and row["template_status_curr"] == "ok"
    )
    ok_routes = sum(
        1
        for row in rows
        if row["route_status_base"] == "ok" and row["route_status_curr"] == "ok"
    )
    base_route_status = Counter(str(row["route_status_base"]) for row in rows)
    curr_route_status = Counter(str(row["route_status_curr"]) for row in rows)

    more_solved = sum(1 for row in rows if int(row["delta_solved"]) > 0)
    less_solved = sum(1 for row in rows if int(row["delta_solved"]) < 0)
    same_solved = ok_templates - more_solved - less_solved

    more_oxidd = sum(1 for row in rows if int(row["delta_oxidd_clusters"]) > 0)
    less_oxidd = sum(1 for row in rows if int(row["delta_oxidd_clusters"]) < 0)
    same_oxidd = ok_routes - more_oxidd - less_oxidd

    more_exact = sum(
        1 for row in rows if int(row["delta_exact_oxidd_clusters"]) > 0
    )
    less_exact = sum(
        1 for row in rows if int(row["delta_exact_oxidd_clusters"]) < 0
    )
    same_exact = ok_routes - more_exact - less_exact

    fewer_external = sum(
        1 for row in rows if int(row["delta_external_clusters"]) < 0
    )
    more_external = sum(
        1 for row in rows if int(row["delta_external_clusters"]) > 0
    )

    print(f"specs={len(rows)}")
    print(f"templates.ok_specs={ok_templates}")
    print(f"templates.solved.same_specs={same_solved}")
    print(f"templates.solved.more_specs={more_solved}")
    print(f"templates.solved.less_specs={less_solved}")
    print(f"templates.solved.base={total('base_solved')}")
    print(f"templates.solved.current={total('curr_solved')}")
    print(f"templates.certified.base={total('base_certified')}")
    print(f"templates.certified.current={total('curr_certified')}")
    print(f"templates.candidate.base={total('base_candidate')}")
    print(f"templates.candidate.current={total('curr_candidate')}")
    print(f"templates.residual_constraints.base={total('base_residual_constraints')}")
    print(f"templates.residual_constraints.current={total('curr_residual_constraints')}")
    print(f"routes.ok_specs={ok_routes}")
    for status, count in sorted(base_route_status.items()):
        print(f"routes.status.base.{status}={count}")
    for status, count in sorted(curr_route_status.items()):
        print(f"routes.status.current.{status}={count}")
    print(f"routes.oxidd.same_specs={same_oxidd}")
    print(f"routes.oxidd.more_specs={more_oxidd}")
    print(f"routes.oxidd.less_specs={less_oxidd}")
    print(f"routes.exact_oxidd.same_specs={same_exact}")
    print(f"routes.exact_oxidd.more_specs={more_exact}")
    print(f"routes.exact_oxidd.less_specs={less_exact}")
    print(f"routes.external.fewer_specs={fewer_external}")
    print(f"routes.external.more_specs={more_external}")
    print(f"routes.clusters.base={total('base_clusters')}")
    print(f"routes.clusters.current={total('curr_clusters')}")
    print(f"routes.oxidd_clusters.base={total('base_oxidd_clusters')}")
    print(f"routes.oxidd_clusters.current={total('curr_oxidd_clusters')}")
    print(f"routes.exact_oxidd_clusters.base={total('base_exact_oxidd_clusters')}")
    print(f"routes.exact_oxidd_clusters.current={total('curr_exact_oxidd_clusters')}")
    print(f"routes.external_clusters.base={total('base_external_clusters')}")
    print(f"routes.external_clusters.current={total('curr_external_clusters')}")
    print(f"routes.external_nodes.base={total('base_external_nodes')}")
    print(f"routes.external_nodes.current={total('curr_external_nodes')}")


def parse_args(argv: list[str]):
    parser = argparse.ArgumentParser(
        description=(
            "Compare tlsftemplates and tlsfcompose route-stats over a TLSF "
            "benchmark corpus."
        )
    )
    parser.add_argument("paths", nargs="*", help="TLSF files or directories")
    parser.add_argument("--baseline-build", help="directory containing baseline tools")
    parser.add_argument("--current-build", help="directory containing current tools")
    parser.add_argument("--baseline-compose", help="baseline tlsfcompose path")
    parser.add_argument("--current-compose", help="current tlsfcompose path")
    parser.add_argument("--baseline-templates", help="baseline tlsftemplates path")
    parser.add_argument("--current-templates", help="current tlsftemplates path")
    parser.add_argument("--out", required=True, help="write per-spec TSV to FILE")
    parser.add_argument("--timeout", type=float, default=10.0,
                        help="per-tool per-spec timeout in seconds")
    parser.add_argument("--limit", type=int, help="limit number of specs")
    parser.add_argument("--progress-every", type=int, default=1,
                        help="print progress every N specs; 0 disables")
    parser.add_argument("--fail-on-loss", action="store_true",
                        help="exit 1 if current has fewer solved templates or "
                        "fewer exact OxiDD clusters on any comparable spec")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    paths = args.paths or default_corpus()
    if not paths:
        print(
            "compare_ltl_benchmark: pass a corpus path or create benchmarks/tlsf",
            file=sys.stderr,
        )
        return 2

    base_compose = (
        args.baseline_compose
        or exe_from_build(args.baseline_build, "tlsfcompose")
    )
    curr_compose = (
        args.current_compose
        or exe_from_build(args.current_build, "tlsfcompose")
        or default_current_tool("tlsfcompose")
    )
    base_templates = (
        args.baseline_templates
        or exe_from_build(args.baseline_build, "tlsftemplates")
    )
    curr_templates = (
        args.current_templates
        or exe_from_build(args.current_build, "tlsftemplates")
        or default_current_tool("tlsftemplates")
    )

    missing = [
        name
        for name, value in (
            ("--baseline-compose/--baseline-build", base_compose),
            ("--baseline-templates/--baseline-build", base_templates),
            ("--current-compose/--current-build", curr_compose),
            ("--current-templates/--current-build", curr_templates),
        )
        if not value
    ]
    if missing:
        print("compare_ltl_benchmark: missing " + ", ".join(missing),
              file=sys.stderr)
        return 2

    files = discover(paths)
    if args.limit is not None:
        files = files[: args.limit]
    if not files:
        print("compare_ltl_benchmark: no TLSF files found", file=sys.stderr)
        return 2

    rows: list[dict[str, object]] = []
    with open(args.out, "w", newline="", encoding="utf-8") as fp:
        writer = csv.DictWriter(fp, fieldnames=FIELDS, delimiter="\t",
                                lineterminator="\n")
        writer.writeheader()
        for idx, path in enumerate(files, 1):
            if args.progress_every and (
                idx == 1 or idx == len(files) or idx % args.progress_every == 0
            ):
                print(f"[{idx}/{len(files)}] {path}", file=sys.stderr)
            bt = run_templates(base_templates, path, args.timeout)
            ct = run_templates(curr_templates, path, args.timeout)
            br = run_routes(base_compose, path, args.timeout)
            cr = run_routes(curr_compose, path, args.timeout)
            row = row_for(path, bt, ct, br, cr)
            rows.append(row)
            writer.writerow(row)
            fp.flush()

    print_summary(rows)

    if args.fail_on_loss:
        for row in rows:
            if int(row["delta_solved"]) < 0:
                return 1
            if int(row["delta_exact_oxidd_clusters"]) < 0:
                return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
