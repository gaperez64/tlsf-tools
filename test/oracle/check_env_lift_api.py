#!/usr/bin/env python3
"""Exercise checked environment candidates and refusal boundaries."""

import argparse
import json
import pathlib
import re
import subprocess
import time




def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=pathlib.Path, required=True)
    parser.add_argument("--fixtures", type=pathlib.Path, required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    args = parser.parse_args()
    output = args.out / f"run-{time.time_ns()}"
    output.mkdir(parents=True, exist_ok=False)
    binary = args.binary.resolve()
    fixtures = args.fixtures.resolve()

    def run(name, fixture, mode, expected, checks, expected_error=None):
        prefix = output / name
        process = subprocess.run(
            [str(binary), str(fixtures / fixture), str(prefix), mode],
            capture_output=True, text=True, timeout=120, check=False)
        line = process.stdout.splitlines()[0] if process.stdout else ""
        work = dict(part.split("=", 1) for part in line.split() if "=" in part)
        stage = "verified" if process.returncode == 0 else work.get("stage")
        assert stage == expected, (name, line, process.stderr)
        assert work.get("checks") == str(checks), (name, line)
        if expected_error is not None:
            assert expected_error in process.stderr, (name, process.stderr)
        if expected == "verified" and checks:
            assert work.get("verdict") == "0", (name, line)
        else:
            assert work.get("verdict") != "0", (name, line)
        return prefix, work

    def check():
        for kind, count in (("zero", 0), ("one", 1), ("several", 3)):
            prefix, _ = run(kind, f"env_lift_{kind}.tlsf", "--lift",
                            "verified", 1)
            certificate = json.loads(pathlib.Path(
                str(prefix) + ".cert.aag.json").read_text())
            policy = json.loads(pathlib.Path(
                str(prefix) + ".policy.aag.json").read_text())
            assert certificate["side"] == policy["side"] == "environment"
            assert certificate["counts"]["fairness_assumptions"] == count
            assert certificate["counts"]["fairness_counters"] == max(1, count)
            assert policy["counts"]["fairness_counters"] == max(1, count)
            aig = pathlib.Path(str(prefix) + ".policy.aag").read_text()
            assert not re.search(r"^i\d+ controllable_", aig, re.M), kind

        _, candidate = run("candidate", "env_lift_one.tlsf",
                           "--candidate", "verified", 0)
        assert candidate["verdict"] == "4"
        for fault, fixture in ((8, "zero"), (9, "one"), (10, "one")):
            run(f"fault-{fault}", f"env_lift_{fixture}.tlsf",
                f"--lift-fault={fault}", "checker_rejected", 1)
        run("corrupt", "env_lift_one.tlsf", "--corrupt-game",
            "target_binding", 0)
        swapped = fixtures / "env_lift_several.tlsf"
        run("swapped", "env_lift_one.tlsf",
            f"--swap-source={swapped}", "typed_alignment", 0)
        _, deadline = run("deadline", "env_lift_one.tlsf", "--deadline",
                          "candidate", 0)
        assert deadline["status"] == "4"
        _, allowance = run("allowance", "env_lift_one.tlsf", "--allowance",
                           "candidate_allowance", 0)
        assert allowance["status"] == "3"
        _, rss = run("rss", "env_lift_one.tlsf", "--rss",
                     "budget-memory", 0)
        assert rss["status"] == "3"
        prefix, work = run("capacity", "env_lift_one.tlsf", "--apply-cap=13000",
                           "schema_capacity", 0,
                           "policy_reconstruct/mode_relation")
        assert work["applies"] == "13001", (prefix, work)
        run("real-seed", "env_real_seed.tlsf", "--lift", "seed_check", 0)

    check()


if __name__ == "__main__":
    main()
