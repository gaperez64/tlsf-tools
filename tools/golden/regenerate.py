#!/usr/bin/env python3
"""TOOLS ONLY: REQUIRES Spot 2.16; never imported by tests, Meson, or CI.

Run from the repository root, with no build/test running concurrently:
  systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
    python3 tools/golden/regenerate.py --build build --spot ~/spot-2.16-install

Every reference call has a deadline. Timeouts are recorded in skipped.json;
ordinary failures stop regeneration. Review all changes before committing.
"""

import argparse
import json
import os
from pathlib import Path
import random
import runpy
import subprocess
import sys
import tempfile
import types

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "test/fixtures/golden"
SKIPPED = []
OPTIONS = None


def run(argv, **kwargs):
    try:
        return subprocess.run(list(map(str, argv)), text=True, capture_output=True,
                              timeout=kwargs.pop("timeout", 60), **kwargs)
    except subprocess.CalledProcessError as error:
        print(error.stderr, file=sys.stderr)
        raise


def reference(formula, names, words):
    with tempfile.NamedTemporaryFile(mode="w") as stream:
        stream.write("\n".join(" ".join(map(str, prefix)) + ";" +
                               " ".join(map(str, loop)) for prefix, loop in words) + "\n")
        stream.flush()
        result = run([OPTIONS.reference, formula, ",".join(names), stream.name])
    assert result.returncode == 0, result.stderr
    tree, membership = result.stdout.splitlines()
    assert len(membership) == len(words)
    return tree, membership


class Recorder:
    def __init__(self, name):
        self.name, self.records = name, []

    def enabled(self, label):
        return True

    def timeout(self, label):
        SKIPPED.append({"suite": self.name, "case": label, "reason": "60s native generation timeout"})
        print(f"skip {self.name}: {label}: 60s timeout", flush=True)

    def check(self, label, value):
        if self.name.startswith("norm-") and label == "normalized":
            original = next(v for key, v in self.records if key == "original")
            result = run([OPTIONS.spot / "bin/ltlfilt", "--equivalent-to=" + original, "-f", value], check=True)
            assert result.stdout.strip(), (self.name, result.stderr)
        if label == "ast-export":
            lines = value.splitlines()
            for index, line in enumerate(lines):
                if line.startswith("string: "):
                    formula = lines[index - 1].split(": ", 1)[1]
                    run([OPTIONS.spot / "bin/ltlfilt", "--equivalent-to=" + formula,
                         "-f", line.removeprefix("string: ")], check=True)
        self.records.append([label, value])

    def verdict(self, formula, inputs, outputs, finite=False, moore=False):
        solver = OPTIONS.spot / "bin" / ("ltlfsynt" if finite else "ltlsynt")
        # Infinite Moore games are complemented Mealy duals. This avoids
        # relying on a --semantics option absent from ltlsynt 2.16.
        dual = moore and not finite
        objective, ins, outs = (f"!({formula})", outputs, inputs) if dual else (formula, inputs, outputs)
        args = [solver, "--realizability", f"--ins={ins}", f"--outs={outs}", "-f", objective]
        if finite:
            args.append("--semantics=" + ("Moore" if moore else "Mealy"))
        try:
            result = run(args, timeout=60)
        except subprocess.TimeoutExpired:
            SKIPPED.append({"suite": self.name, "formula": formula, "reason": "60s reference timeout"})
            raise
        assert result.returncode in (0, 1), (args, result.stderr)
        expected = (result.returncode == 0) != dual
        self.records.append(["verdict", [formula, inputs, outputs, finite, moore], expected])
        return expected

    def artifacts(self, directory):
        self.check("artifacts", {p.name: p.read_text() for p in sorted(Path(directory).iterdir())
                                  if p.is_file()})

    def language(self, formula, names, words, actual):
        _tree, expected = reference(formula, names, words)
        assert actual == expected, (self.name, formula, actual, expected)
        self.check("language", [formula, names, words, expected])

    def finish(self):
        (DEST / (self.name + ".json")).write_text(json.dumps(self.records, indent=2) + "\n")


def script(name, *args):
    sys.argv = [str(ROOT / "test/oracle" / name), *map(str, args)]
    runpy.run_path(sys.argv[0], run_name="__main__")


def dpa():
    target = DEST / "dpa"
    target.mkdir(exist_ok=True)
    run(["c++", "-std=c++20", ROOT / "tools/golden/dpa_cases.cc", "-o", OPTIONS.build / "golden-cases"], check=True)
    handwritten = run([OPTIONS.build / "golden-cases"], check=True).stdout.splitlines()
    common = "strongX=0,not=0,equiv=0,implies=0,xor=0"
    random_formulas = []
    for seed, priorities, recurrence in (
            (31415, common + ",F=0,U=0,M=0", False),
            (27182, common + ",F=0,G=0,U=0,R=0,W=0,M=0", True)):
        lines = run([OPTIONS.spot / "bin/randltl", "a", "b", "c", f"--seed={seed}",
                     "-n", "18", "--tree-size=4..12", "--ltl-priorities=" + priorities], check=True).stdout.splitlines()
        for line in lines:
            formula = f"G F ({line})" if recurrence else line
            random_formulas.extend((formula, f"!({formula})"))
    raw = run([OPTIONS.spot / "bin/randltl", "a", "b", "c", "--seed=20852", "-n", "1600",
               "--tree-size=6..20", "--ltl-priorities=strongX=0"], check=True).stdout
    filtered = run([OPTIONS.spot / "bin/ltlfilt", "--delta2"], input=raw, check=True).stdout.splitlines()
    assert len(filtered) >= 300
    delta = filtered[:300] + [f"({left}) <-> !({filtered[-1-i]})" for i, left in enumerate(filtered[:60])]
    rng = random.Random(0x97D0A)
    words = [([], [bits]) for bits in range(128)]
    words += [([rng.randrange(128) for _ in range(rng.randrange(5))],
               [rng.randrange(128) for _ in range(rng.randrange(1, 6))]) for _ in range(384)]
    (target / "words.txt").write_text("\n".join(" ".join(map(str, p)) + ";" + " ".join(map(str, q)) for p, q in words) + "\n")
    records, timed_out = [], set()
    for index, formula in enumerate(dict.fromkeys(handwritten + random_formulas + delta)):
        try:
            tree, membership = reference(formula, ["unused_in", "req", "a", "unused_out", "c", "grant", "b"], words)
        except subprocess.TimeoutExpired:
            SKIPPED.append({"suite": "dpa", "formula": formula, "reason": "60s reference timeout"})
            timed_out.add(formula)
            continue
        records.append("\t".join((formula, tree, membership)))
        if index % 50 == 0:
            print(f"DPA reference {index}", flush=True)
    assert not (set(handwritten) & timed_out), "handwritten timeout needs explicit test review"
    (target / "membership.tsv").write_text("\n".join(records) + "\n")
    limits = []
    for formula in (ROOT / "test/unit/dpa_limits.ltl").read_text().splitlines():
        result = run([OPTIONS.reference, formula, "", "/dev/null", "--tree-only"], check=True)
        limits.append(formula + "\t" + result.stdout.strip())
    (target / "limits.tsv").write_text("\n".join(limits) + "\n")
    for name, formulas in (("random.ltl", random_formulas), ("delta2.ltl", delta)):
        (target / name).write_text("\n".join(f for f in formulas if f not in timed_out) + "\n")


def main():
    global OPTIONS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--spot", type=Path, required=True)
    parser.add_argument("--only", choices=("dpa", "exports", "native", "language", "monitor", "lift", "norm", "api", "step1"))
    OPTIONS = parser.parse_args()
    OPTIONS.build = OPTIONS.build.resolve()
    OPTIONS.spot = OPTIONS.spot.expanduser().resolve()
    OPTIONS.reference = OPTIONS.build / "golden-reference"
    flags = run(["pkg-config", "--cflags", "--libs", "libspot"],
                env=dict(os.environ, PKG_CONFIG_PATH=str(OPTIONS.spot / "lib/pkgconfig")), check=True).stdout.split()
    run(["c++", "-std=c++20", ROOT / "tools/golden/reference.cc", "-o", OPTIONS.reference, *flags,
         "-Wl,-rpath," + str(OPTIONS.spot / "lib")], check=True)
    module = types.ModuleType("golden")
    module.Golden, module.ROOT = Recorder, DEST
    module.reference = reference
    sys.modules["golden"] = module
    sys.path.insert(0, str(ROOT / "test/oracle"))
    build, cases = OPTIONS.build, ROOT / "test/fixtures/cases"
    versions = {}
    for tool in ("ltlsynt", "ltlfsynt", "ltlfilt", "ltl2tgba", "autfilt", "randltl"):
        versions[tool] = run([OPTIONS.spot / "bin" / tool, "--version"], check=True).stdout.splitlines()[0]
        assert "2.16" in versions[tool], versions[tool]
    (DEST / "tool-versions.json").write_text(json.dumps(versions, indent=2) + "\n")
    try:
        if OPTIONS.only in (None, "dpa"):
            dpa()
        if OPTIONS.only in (None, "exports"):
            for mode in ("lowercase", "comment", "signals"):
                script("test_review4_exports.py", build / "tlsf2ltl", build / "tlsfresidual", build / "tlsfcompose", mode)
            for mode in ("moore", "finite", "implicit", "wrapper"):
                script("test_compose_driver_semantics.py", build / "tlsfcompose", mode)
            script("test_decomposition_exactness.py", build / "tlsf2ltl", build / "tlsfresidual",
                   build / "tlsfcompose", build / "test/unit/phase_b_probe", cases)
            script("test_disjoint_assumptions.py", build / "tlsf2ltl", build / "tlsfresidual",
                   build / "tlsfcompose", cases / "disjoint_assumptions.tlsf")
        for mode, name in (("native", "test_native_reduction.py"),
                           ("language", "test_native_reduction_language.py"),
                           ("monitor", "test_gr1_monitor_game.py"),
                           ("lift", "test_native_lift_differential.py")):
            if OPTIONS.only in (None, mode):
                script(name, "--builddir", build)
        if OPTIONS.only in (None, "norm"):
            script("test_normalization.py", build / "tlsfnorm", build / "tlsf2ltl", cases)
        if OPTIONS.only in (None, "api"):
            script("test_conversion.py", build / "test/api/ast_golden", cases / "cluster_split.tlsf")
        if OPTIONS.only in (None, "step1"):
            script("native_oracle.py", build)
    finally:
        path = DEST / "skipped.json"
        previous = json.loads(path.read_text()) if OPTIONS.only and path.exists() else []
        path.write_text(json.dumps(previous + SKIPPED, indent=2) + "\n")


if __name__ == "__main__":
    main()
