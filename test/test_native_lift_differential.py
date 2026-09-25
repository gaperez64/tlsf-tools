#!/usr/bin/env python3
"""Bounded Stage C differential against the withdrawn Python implementation.

The oracle is test-only and supplied explicitly with --oracle-root. Every
invocation is serial, uses the source's own PARAMETERS, and has a timeout.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import random
import re
import signal
import subprocess
import sys
import time


def run(argv: list[str], *, timeout: float, env: dict[str, str] | None = None):
    process = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, env=env, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        def descendants(pid: int) -> list[int]:
            try:
                children = pathlib.Path(f"/proc/{pid}/task/{pid}/children").read_text().split()
            except OSError:
                return []
            result = []
            for child in children:
                result.extend(descendants(int(child)))
                result.append(int(child))
            return result
        for pid in [*descendants(process.pid), process.pid]:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        process.communicate()
        return subprocess.CompletedProcess(argv, 124, "HARD_TIMEOUT\n", "")
    return subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)


def generated(directory: pathlib.Path, obfuscator: pathlib.Path
              ) -> tuple[list[pathlib.Path], list[tuple[int, pathlib.Path]]]:
    rng = random.Random(0x42ACAC1A)
    cases = []
    formulas = ("G F {g}[i]", "G ({r}[i] -> F {g}[i])",
                "G ({r}[i] -> {g}[i])", "G F ({g}[i] || {r}[i])")
    for index, formula in enumerate(formulas):
        r = "controllable_" + "".join(rng.choices("abcdef", k=8))
        g = "uncontrollable_" + "".join(rng.choices("uvwxyz", k=8))
        text = (f'INFO {{ TITLE: "unseen" DESCRIPTION: "unseen" '
                f'SEMANTICS: Mealy TARGET: Mealy }}\n'
                f'GLOBAL {{ PARAMETERS {{ span = 5; }} }}\n'
                f'MAIN {{ INPUTS {{ {r}[span]; }} OUTPUTS {{ {g}[span]; }}\n'
                f'GUARANTEES {{ &&[0 <= i < span] '
                f'{formula.format(r=r, g=g)}; }} }}\n')
        path = directory / f"random_{index}.tlsf"
        path.write_text(text)
        cases.append(path)
    twins = []
    for index, seed in ((0, 0x461), (1, 0x77A), (3, 0xB39)):
        output = directory / f"obfuscated-{index}"
        result = run([sys.executable, str(obfuscator), str(cases[index]),
                      str(output), "--seed", str(seed)], timeout=5)
        assert result.returncode == 0, (result.stdout, result.stderr)
        twin, sidecar = map(pathlib.Path, result.stdout.splitlines())
        assert twin.is_file() and sidecar.is_file()
        mapping = json.loads(sidecar.read_text())
        assert len(mapping["signals"]) == 2
        twins.append((index, twin))
    return cases, twins


def bdd_compare(left: pathlib.Path, right: pathlib.Path, bindings_site: pathlib.Path,
                tools_build: pathlib.Path) -> None:
    from acacia_lift.artifact import Aag
    from acacia_lift.lifting.schema import Bdds
    from acacia_lift.tools import ToolConfiguration

    l, r = Aag.read(left), Aag.read(right)
    assert l.input_names == r.input_names, (left, "input names")
    assert set(l.output_names) == set(r.output_names), (left, "output names")
    cfg = ToolConfiguration(tools_build, pathlib.Path(sys.executable), bindings_site)
    bdds = Bdds(cfg, len(l.inputs))
    for name in sorted(l.output_names):
        assert bdds.from_aag(l, l.output(name)) == bdds.from_aag(r, r.output(name)), (
            left, name)


def role_partition(native: dict, oracle_target: pathlib.Path) -> None:
    from acacia_lift.lifting.provenance import role_signatures, target_modes
    from acacia_lift.lifting.source import InstanceFiles

    provenance = oracle_target / "provenance.json"
    game = oracle_target / "game.aag"
    if not provenance.is_file():
        provenance = oracle_target.parent / "target_strict" / "provenance.json"
        game = oracle_target.parent / "target_strict" / "game.aag"
    data = json.loads(provenance.read_text())
    instance = InstanceFiles(game, provenance, data, ())
    target_modes(instance, [])
    native_roles = {row["index"]: row["signature"] for row in native["roles"]}
    reference = role_signatures(instance, tuple(sorted(native_roles)))
    assert set(native_roles) == set(reference)
    for a in reference:
        for b in reference:
            assert (native_roles[a] == native_roles[b]) == (reference[a] == reference[b]), (
                a, b, "role class")


def compare_case(path: pathlib.Path, output: pathlib.Path, args, env: dict[str, str],
                 *, expected_success: bool = False) -> dict | None:
    output.mkdir(parents=True, exist_ok=True)
    prefix = output / "native"
    native = run([str(args.native), str(path), str(prefix), str(args.seconds)],
                 timeout=args.seconds + 3)
    native_first = native.stdout.splitlines()[0] if native.stdout else native.stderr[:200]
    reference_dir = output / "reference"
    evidence_path = output / "reference-evidence.json"
    oracle = run([str(args.bindings_python), "-m", "acacia_lift.runner",
                  "-T", str(path), "--budget", str(args.seconds),
                  "--eligibility-budget-seconds", str(min(5, args.seconds / 2)),
                  "--output-dir", str(reference_dir), "--evidence-out", str(evidence_path),
                  "--tlsf-tools-build", str(args.tools_build),
                  "--bindings-python", str(args.bindings_python),
                  "--bindings-site", str(args.bindings_site)],
                 timeout=args.seconds + 3, env=env)
    reference = json.loads(evidence_path.read_text()) if evidence_path.is_file() else {
        "route": "hard-timeout"}
    failure = reference.get("lifting_failure")
    print(f"{path.name}: native={native_first}; oracle={reference['route']}; "
          f"lifting_failure={failure}", flush=True)
    if native.returncode == 0:
        assert reference["route"] == "lifted-certified", path
        assert reference["result"]["verdict"] == "REALIZABLE"
        result = json.loads((output / "native.evidence.json").read_text())
        assert result["seed_values"] == [list(seed.values())[0] for seed in reference["seeds"]]
        assert result["predicate_arities"] == reference["predicate_arities"]
        assert result["method"] == reference["result"]["proof_method"]
        assert result["verdict"] == reference["target_certificate"]["checker_verdict"]
        role_partition(result, reference_dir / "target")
        bdd_compare(output / "native.cert.aag", reference_dir / "lifted.certificate.aag",
                    args.bindings_site, args.tools_build)
        if result["method"] == "certificate":
            bdd_compare(output / "native.policy.aag", reference_dir / "lifted.policy.aag",
                        args.bindings_site, args.tools_build)
        return result
    if expected_success:
        raise AssertionError(f"expected verified lifting for {path}: {native_first}")
    if native.returncode == 124 or oracle.returncode == 124:
        assert reference["route"] != "lifted-certified", (
            path, "native timed out but oracle lifted")
        return None
    if failure and native_first.startswith("status=2"):
        native_stage = re.search(r"stage=([^ ]+)", native_first).group(1)
        if native_stage != failure["stage"]:
            # Typed relative offsets can admit a stable window that the
            # withdrawn Python role scheme rejects. Both routes must still
            # decline unless their target certificates compare above.
            assert (failure["stage"], native_stage) == ("seed_window", "schema"), (
                path, native_stage, failure)
            print(f"{path.name}: native advanced beyond oracle seed discovery",
                  flush=True)
    return None


def corpus_sample(root: pathlib.Path, limit: int) -> list[pathlib.Path]:
    candidates = []
    for path in root.rglob("*.tlsf"):
        text = path.read_text(errors="ignore")
        match = re.search(r"PARAMETERS\s*\{([^}]*)\}", text, re.S)
        if match and any(int(value) >= 5 for value in
                         re.findall(r"\b\w+\s*=\s*(\d+)\s*;", match.group(1))):
            candidates.append(path)
    return sorted(candidates)[:limit]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--native", required=True, type=pathlib.Path)
    parser.add_argument("--builddir", required=True, type=pathlib.Path)
    parser.add_argument("--oracle-root", required=True, type=pathlib.Path)
    parser.add_argument("--tools-build", required=True, type=pathlib.Path)
    parser.add_argument("--bindings-python", default="/usr/bin/python3.13", type=pathlib.Path)
    parser.add_argument("--bindings-site", default="/usr/local/lib64/python3.13/site-packages",
                        type=pathlib.Path)
    parser.add_argument("--corpus-root", type=pathlib.Path)
    parser.add_argument("--obfuscator", type=pathlib.Path)
    parser.add_argument("--skip-generated", action="store_true")
    parser.add_argument("--corpus-limit", default=8, type=int)
    parser.add_argument("--seconds", default=12, type=float)
    args = parser.parse_args()
    assert 1 <= args.corpus_limit <= 40 and 0 < args.seconds <= 60
    args.native = args.native.resolve()
    args.tools_build = args.tools_build.resolve()
    args.bindings_site = args.bindings_site.resolve()
    args.bindings_python = args.bindings_python.resolve()
    args.obfuscator = (args.obfuscator or args.oracle_root /
                       "benchmarking/gr1-par2-20260923/obfuscate-tlsf.py").resolve()
    oracle_package_root = args.oracle_root.resolve() / "benchmarking/gr1-par2-20260923/oracle"
    if not (oracle_package_root / "acacia_lift/runner.py").is_file():
        oracle_package_root = args.oracle_root.resolve() / "scripts"
    sys.path.insert(0, str(oracle_package_root))
    sys.path.insert(0, str(args.bindings_site))
    output = args.builddir.resolve() / "lift-differential" / f"run-{time.time_ns()}"
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join((str(oracle_package_root),
                                        str(args.bindings_site), env.get("PYTHONPATH", "")))
    env["LD_LIBRARY_PATH"] = os.pathsep.join(("/usr/local/lib", "/usr/local/lib64",
                                              env.get("LD_LIBRARY_PATH", "")))
    if not args.skip_generated:
        cases, twins = generated(output, args.obfuscator)
        results = [compare_case(path, output / f"case-{i}", args, env,
                                expected_success=True) for i, path in enumerate(cases)]
        for index, twin in twins:
            renamed = compare_case(twin, output / f"twin-{index}", args, env,
                                   expected_success=True)
            for field in ("game_sha256", "certificate_sha256", "seed_values", "roles",
                          "predicate_arities", "method", "verdict"):
                assert results[index][field] == renamed[field], (index, field)
    if args.corpus_root:
        sample = corpus_sample(args.corpus_root, args.corpus_limit)
        positives = 0
        for i, path in enumerate(sample):
            positives += compare_case(path, output / f"corpus-{i}", args, env) is not None
        print(f"corpus sample: {len(sample)} inputs, {positives} positive lifts"
              + ("; none found in this bounded sample" if positives == 0 else ""),
              flush=True)


if __name__ == "__main__":
    main()
