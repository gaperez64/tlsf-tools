#!/usr/bin/env python3
"""Offline issue-78 inventory. Scratch and logs stay under build-scratch-m/."""
import argparse
import collections
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import statistics
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "build-scratch-m"
LAZY = SCRATCH / "build/test/unit/dpa_admission"
OWL = SCRATCH / "owl-linux-musl-amd64-21.0/bin/owl"
JAR = OWL.parents[1] / "jar/owl-21.0.jar"
LIMIT = 120
TOOLS = ("default", "research", "owl", "owl_lookahead0")
OWL_TOOLS = ("owl", "owl_lookahead0")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def check_exports(row, prefix):
    assert digest(str(prefix) + ".ltl") == row["formula_sha256"]
    assert digest(str(prefix) + ".aps") == row["aps_sha256"]
    body = Path(str(prefix) + ".ltl").read_text()
    aps = Path(str(prefix) + ".aps").read_text().splitlines()
    expected = "(false" + "".join(f' & "{ap}"' for ap in aps) + ") | " + body
    assert Path(str(prefix) + ".owl.ltl").read_text() == expected


def prepare(args):
    if any((SCRATCH / "runs").glob("*/*/started.json")):
        raise SystemExit("Scratch contains measured runs; resume with run, or preserve it "
                         "and start a fresh scratch directory before preparing a new campaign.")
    names = (SCRATCH / "evidence/_bm-logs.otfpar/semml-only.list").read_text().splitlines()
    assert len(names) == len(set(names)) == 69
    mapping_path = args.acacia / "tests/suites/benchmarks/syntcomp26/tlsf-sources.tsv"
    with mapping_path.open() as stream:
        pairs = list(csv.DictReader(stream, delimiter="\t"))
    mapping = collections.defaultdict(list)
    for pair in pairs:
        mapping[pair["instance"]].append(pair["tlsf"])
    with (args.acacia / "tests/suites/benchmarks/tlsf-manifest.tsv").open() as stream:
        official = {r["instance"]: r["sha256"] for r in csv.DictReader(stream, delimiter="\t")}
    for directory in ["inputs", "formulas", "runs", "tmp"]:
        (SCRATCH / directory).mkdir(exist_ok=True)
    inventory = []
    for name in names:
        assert len(mapping[name]) == 1, name
        filename = mapping[name][0]
        assert Path(filename).name == filename
        source = args.corpus / filename
        assert digest(source) == official[filename], filename
        target = SCRATCH / "inputs" / filename
        shutil.copyfile(source, target)
        assert digest(source) == digest(target)
        prefix = SCRATCH / "formulas" / name
        subprocess.run([LAZY, "--expand", "--measure", "export", target, prefix], check=True)
        semantics, original, effective, ni, no = Path(str(prefix) + ".meta").read_text().strip().split("\t")
        assert effective == "Mealy" and "Finite" not in semantics
        inventory.append(dict(instance=name, tlsf=filename, source_sha256=digest(target),
                              formula_sha256=digest(str(prefix) + ".ltl"),
                              aps_sha256=digest(str(prefix) + ".aps"), semantics=semantics,
                              original_target=original, inputs=int(ni), outputs=int(no)))
    assert len({r["tlsf"] for r in inventory}) == 69
    subprocess.run(["javac", "-cp", JAR, "-d", SCRATCH, ROOT / "tools/CheckOwlFormula.java"], check=True)
    subprocess.run(["java", "-cp", f"{SCRATCH}:{JAR}:{SCRATCH}/checker-libs/*", "CheckOwlFormula",
                    *[str(SCRATCH / "formulas" / n) for n in names]], check=True)
    save(SCRATCH / "inventory.json", inventory)
    save(SCRATCH / "provenance.json", dict(mapping_sha256=digest(mapping_path),
         evidence_sha256=digest(SCRATCH / "downloads/otfpar-20261027.tar.gz"),
         owl_zip_sha256=digest(SCRATCH / "downloads/owl-linux-amd64-21.0.zip"),
         owl_binary_sha256=digest(OWL), owl_jar_sha256=digest(JAR),
         lazy_binary_sha256=digest(LAZY), seconds=LIMIT, memory_bytes=4 << 30, swap_bytes=0))
    print("Prepared 69 unique, byte-identical TLSF sources; formula/alphabet checks passed.")


def events(cgroup):
    return dict((key, int(value)) for key, value in
                (line.split() for line in (cgroup / "memory.events").read_text().splitlines()))


def worker(args):
    directory = Path(args.directory)
    relative = next(line[3:] for line in Path("/proc/self/cgroup").read_text().splitlines()
                    if line.startswith("0::"))
    cgroup = Path("/sys/fs/cgroup") / relative.lstrip("/")
    memory_max = (cgroup / "memory.max").read_text().strip()
    memory_swap_max = (cgroup / "memory.swap.max").read_text().strip()
    assert memory_max == str(4 << 30)
    assert memory_swap_max == "0"
    before = events(cgroup)
    save(directory / "started.json", dict(cgroup=str(cgroup), before=before,
         memory_max=memory_max, memory_swap_max=memory_swap_max))
    env = dict(os.environ, TMPDIR=str(SCRATCH / "tmp"))
    start = time.monotonic()
    with (directory / "stdout").open("w") as out, (directory / "stderr").open("w") as err:
        process = subprocess.Popen(args.command, stdout=out, stderr=err, env=env,
                                   start_new_session=True)
        timed_out = False
        try:
            process.wait(timeout=LIMIT)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
    save(directory / "finished.json", dict(returncode=process.returncode,
         timed_out=timed_out, wall_s=round(time.monotonic() - start, 3),
         events=events(cgroup), memory_peak=int((cgroup / "memory.peak").read_text())))


def owl_counts(path, aps):
    states, priorities, declared, alphabet = set(), set(), None, None
    complete = deterministic = ended = False
    with path.open() as stream:
        for line in stream:
            if line.startswith("State:"):
                number = int(line.split()[1])
                assert number not in states
                states.add(number)
            elif line.startswith("Acceptance:"):
                declared = int(line.split()[1])
            elif line.startswith("AP:"):
                alphabet = re.findall(r'"([^"\\]*)"', line)
                assert len(alphabet) == int(line.split()[1])
            elif line.startswith("properties:"):
                complete |= "complete" in line.split()
                deterministic |= "deterministic" in line.split()
            elif line.startswith("--END--"):
                ended = True
            if line.startswith("[") or line.startswith("State:"):
                for marks in re.findall(r"\{([0-9 ]*)\}", line):
                    priorities.update(map(int, marks.split()))
    assert ended and complete and deterministic and declared is not None
    # Owl's LabelledFormula truncates trailing unused APs. The remaining
    # alphabet must be an exact prefix of the explicitly supplied order.
    assert alphabet == aps[:len(alphabet)]
    assert all(p < declared for p in priorities)
    return len(states), declared, len(priorities)


def run(args):
    inventory = json.loads((SCRATCH / "inventory.json").read_text())
    provenance = json.loads((SCRATCH / "provenance.json").read_text())
    assert digest(LAZY) == provenance["lazy_binary_sha256"]
    assert digest(OWL) == provenance["owl_binary_sha256"]
    for index, row in enumerate(inventory, 1):
        prefix = SCRATCH / "formulas" / row["instance"]
        source = SCRATCH / "inputs" / row["tlsf"]
        assert digest(source) == row["source_sha256"]
        check_exports(row, prefix)
        for tool in args.tools:
            directory = SCRATCH / "runs" / row["instance"] / tool
            directory.mkdir(parents=True, exist_ok=True)
            if (directory / "result.json").exists():
                continue
            # Refuse to overwrite interrupted evidence; inspect or move it first.
            assert not (directory / "started.json").exists(), directory
            if tool in OWL_TOOLS:
                command = [str(OWL), "ltl2dpa", "--complete"]
                if tool == "owl_lookahead0":
                    command.append("--SLM21-lookahead=0")
                command.extend(["-i", str(prefix) + ".owl.ltl"])
            else:
                command = [str(LAZY), "--expand", "--measure", tool, str(source), str(prefix)]
            save(directory / "command.json", command)
            unit = "dpa-counts-" + uuid.uuid4().hex + ".scope"
            scope = ["systemd-run", "--user", "--scope", "--unit=" + unit,
                     "-p", "MemoryMax=4G", "-p", "MemorySwapMax=0", sys.executable,
                     str(Path(__file__).resolve()), "worker", str(directory), *command]
            start = time.monotonic()
            last_events = {}
            with (directory / "scope.log").open("w") as log:
                process = subprocess.Popen(scope, stdout=log, stderr=log)
                while process.poll() is None:
                    if (directory / "started.json").exists():
                        cgroup = Path(json.loads((directory / "started.json").read_text())["cgroup"])
                        try:
                            last_events = events(cgroup)
                        except FileNotFoundError:
                            pass
                    time.sleep(0.1)
            assert (directory / "started.json").exists(), (directory / "scope.log").read_text()
            # systemd's default OOMPolicy=stop can terminate the observer as
            # well. The failed scope retains its Result after cgroup removal.
            observed = subprocess.run(["systemctl", "--user", "show", unit,
                                       "-p", "Result", "-p", "MemoryPeak"],
                                      capture_output=True, text=True)
            scope_properties = dict(line.split("=", 1) for line in observed.stdout.splitlines()
                                    if "=" in line)
            save(directory / "scope.json", scope_properties)
            if (directory / "finished.json").exists():
                finish = json.loads((directory / "finished.json").read_text())
                last_events = finish["events"]
            else:
                finish = dict(returncode=process.returncode, timed_out=False,
                              wall_s=round(time.monotonic() - start, 3))
            before = json.loads((directory / "started.json").read_text())["before"]
            result = dict(status="error", reason="exit_" + str(finish["returncode"]),
                          states="NA", colours="NA", used="NA", wall_s=finish["wall_s"])
            if (last_events.get("oom_kill", 0) > before.get("oom_kill", 0)
                    or scope_properties.get("Result") == "oom-kill"):
                result.update(status="oom", reason="cgroup_oom_kill")
            elif finish["timed_out"]:
                result.update(status="timeout", reason="deadline")
            elif finish["returncode"] == 0:
                if tool in OWL_TOOLS:
                    states, colours, used = owl_counts(directory / "stdout",
                                                       Path(str(prefix) + ".aps").read_text().splitlines())
                    result.update(status="ok", reason="none", states=states, colours=colours, used=used)
                else:
                    code, reason, states, colours, used = (directory / "stdout").read_text().strip().split("\t")
                    reasons = ["none", "unsupported", "state_limit", "host_limit", "bdd_limit",
                               "deadline", "cancelled", "priority_limit"]
                    result.update(status={"0": "ok", "1": "declined"}.get(code, "error"),
                                  reason=reasons[int(reason)])
                    if code == "0":
                        result.update(states=int(states), colours=int(colours), used=int(used))
            save(directory / "result.json", result)
            check_exports(row, prefix)
            print(f"{index}/69 {row['instance']} {tool}: {result}", flush=True)


def summarize(args):
    inventory = json.loads((SCRATCH / "inventory.json").read_text())
    rows = []
    for item in inventory:
        row = dict(item)
        for tool in TOOLS:
            result = json.loads((SCRATCH / "runs" / row["instance"] / tool / "result.json").read_text())
            row.update({tool + "_" + key: value for key, value in result.items()})
            if tool in OWL_TOOLS:
                row[tool + "_parity"] = "NA"
                if result["status"] == "ok":
                    with (SCRATCH / "runs" / row["instance"] / tool / "stdout").open() as stream:
                        acceptance = next(line.split() for line in stream if line.startswith("acc-name:"))
                    assert acceptance[1] == "parity"
                    row[tool + "_parity"] = "_".join(acceptance[2:4])
        rows.append(row)
    with args.output.open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0].keys(), delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    for tool in TOOLS:
        print(tool, dict(collections.Counter(r[tool + "_status"] for r in rows)))
    for baseline in OWL_TOOLS:
        for tool in ["default", "research"]:
            ratios = sorted((r[tool + "_states"] / r[baseline + "_states"], r["instance"])
                            for r in rows if r[tool + "_status"] == r[baseline + "_status"] == "ok")
            values = [v for v, _ in ratios]
            print(tool, "vs", baseline, "both", len(values))
            if values:
                quartiles = statistics.quantiles(values, method="inclusive") if len(values) > 1 else values * 3
                print("Q1/median/Q3", quartiles, "max", max(values),
                      "<=1/2/10", [sum(v <= k for v in values) for k in [1, 2, 10]])
                print("largest", ratios[-5:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    prep = commands.add_parser("prepare")
    prep.add_argument("--acacia", type=Path, required=True)
    prep.add_argument("--corpus", type=Path, required=True)
    runner = commands.add_parser("run")
    runner.add_argument("--tools", nargs="+", choices=TOOLS, default=TOOLS,
                        help="Configurations to run (default: all four); completed records are skipped.")
    summary = commands.add_parser("summarize")
    summary.add_argument("--output", type=Path, default=ROOT / "docs/lazy-dpa/STATE-COUNTS.tsv")
    work = commands.add_parser("worker")
    work.add_argument("directory")
    work.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    globals()[args.action](args)


if __name__ == "__main__":
    main()
