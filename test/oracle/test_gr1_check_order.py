#!/usr/bin/env python3
"""Check variable-order controls on existing GR(1) differential fixtures."""

from __future__ import annotations

import argparse
import json
import pathlib
import random
import re
import subprocess
import tempfile

import test_gr1_certcheck as certcheck
import test_gr1_region as region


def stable_output(text: str) -> str:
    return re.sub(r"(time|elapsed)=\d+\.\d+", r"\1=<elapsed>", text)


def stable_json_bytes(text: str) -> str:
    return re.sub(r'("[^"\n]*seconds"\s*:)\s*[-+0-9.eE]+', r"\1<elapsed>", text)


def run(checker, arguments):
    return subprocess.run([str(checker), *map(str, arguments)], text=True,
                          capture_output=True, check=False, timeout=20)


def check_orders(checker, baseline, root, game, policy, cert, method):
    arguments = ["--method", method, "--certificate", cert,
                 "--node-cap", "65536", "--cache-cap", "65536",
                 "--json-out", root / "result.json", game]
    if method != "region":
        arguments.append(policy)
    automatic = run(checker, arguments)
    json_text = (root / "result.json").read_text()
    payload = json.loads(json_text)
    explicit = run(checker, ["--var-order", "auto", *arguments])
    assert explicit.returncode == automatic.returncode
    assert stable_output(explicit.stdout) == stable_output(automatic.stdout), (automatic, explicit)
    assert explicit.stderr == automatic.stderr
    assert stable_json_bytes((root / "result.json").read_text()) == stable_json_bytes(json_text)
    if baseline:
        previous = run(baseline, arguments)
        assert previous.returncode == automatic.returncode
        assert stable_output(previous.stdout) == stable_output(automatic.stdout)
        assert previous.stderr == automatic.stderr
        assert stable_json_bytes((root / "result.json").read_text()) == stable_json_bytes(json_text)
    for order in ("input-first", "state-first"):
        forced = run(checker, ["--var-order", order, *arguments])
        assert certcheck.checker_status(forced) == certcheck.checker_status(automatic), (
            method, order, automatic, forced)
        result = json.loads((root / "result.json").read_text())
        assert result["verdict"] == payload["verdict"]
    return automatic.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--checker", type=pathlib.Path, required=True)
    parser.add_argument("--baseline-checker", type=pathlib.Path)
    args = parser.parse_args()
    checker = args.checker.resolve()
    solver = args.solver.resolve()
    baseline = args.baseline_checker.resolve() if args.baseline_checker else None
    help_result = run(checker, ["--help"])
    assert help_result.returncode == 0
    for text in ("--var-order", "auto|input-first|state-first", "default auto",
                 "4096..262144", "retry state-first", "forced orders"):
        assert text in help_result.stderr, text
    for value in ("", "unknown", "3", "-1", "fanin-dfs"):
        invalid = run(checker, ["--var-order", value])
        assert invalid.returncode == 2 and "unknown variable order" in invalid.stderr
    missing = run(checker, ["--var-order"])
    assert missing.returncode == 2 and "--var-order requires a value" in missing.stderr

    fixtures = [region.one_goal_game(), region.two_goal_game(),
                region.rank_shape_game(), region.fairness_game(),
                region.one_goal_game(bad="true")]
    rng = random.Random(0xC3A7C4E)
    fixtures.extend(certcheck.differential.make_random_game(rng, index)
                    for index in range(8))
    checked = 0
    with tempfile.TemporaryDirectory(prefix="tlsf-check-order-") as directory:
        root = pathlib.Path(directory)
        for index, game_text in enumerate(fixtures):
            game = root / f"game-{index}.aag"
            policy = root / "policy.aag"
            cert = root / "certificate.aag"
            game.write_text(game_text)
            solved = run(solver, ["--semantics", "exact", "--policy", policy,
                                  "--certificate", cert, game])
            assert solved.returncode in (0, 1), solved
            # Both polarities export a certificate and policy.
            assert cert.exists() and policy.exists(), solved
            for method in ("auto", "certificate", "closed-loop", "both"):
                assert check_orders(checker, baseline, root, game, policy, cert, method) == 0
                checked += 1
            if solved.returncode == 0:
                assert check_orders(checker, baseline, root, game, policy, cert, "region") == 0
                checked += 1
            genuine_cert = cert.read_text()
            cert.write_text(certcheck.replace_output(genuine_cert, "inv", replacement=0))
            assert check_orders(checker, baseline, root, game, policy, cert, "certificate") == 6
            checked += 1
            cert.write_text(genuine_cert)
            policy_text = policy.read_text()
            control = next(name for name in certcheck.output_literals(policy_text)
                           if not name.startswith("curr_next_"))
            policy.write_text(certcheck.replace_output(policy_text, control, invert=True))
            for method in ("auto", "certificate", "closed-loop", "both"):
                check_orders(checker, baseline, root, game, policy, cert, method)
                checked += 1
            policy.write_text(policy_text)
            sidecar = pathlib.Path(str(cert) + ".json")
            genuine_json = sidecar.read_text()
            sidecar.write_text("invalid JSON")
            assert check_orders(checker, baseline, root, game, policy, cert, "certificate") == 4
            checked += 1
            sidecar.write_text(genuine_json)

            if index == 1:
                padded = certcheck.wrap_output_in_selectors(policy_text, control, 1400)
                policy.write_text(certcheck.replace_output(padded, control, invert=True))
                assert check_orders(checker, baseline, root, game, policy, cert, "certificate") == 6
                arguments = ["--method", "certificate", "--certificate", cert,
                             "--node-cap", "65536", "--cache-cap", "65536",
                             "--stats", game, policy]
                automatic = run(checker, arguments)
                assert " legacy_order=1 " in automatic.stderr
                for order in ("input-first", "state-first"):
                    forced = run(checker, ["--var-order", order, *arguments])
                    assert certcheck.checker_status(forced) == certcheck.checker_status(automatic)
                    assert " legacy_order=0 " in forced.stderr
                    assert "COUNTEREXAMPLE reason=" in forced.stdout
                checked += 1
    print(f"{checked} checker fixtures agree across automatic and forced orders")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
