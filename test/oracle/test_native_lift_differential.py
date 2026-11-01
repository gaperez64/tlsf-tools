#!/usr/bin/env python3
"""Pinned Stage C lift verdicts and artifacts, including unseen alpha variants."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import tempfile

from golden import Golden
from reduction_golden import game_language


def stable(value):
    if isinstance(value, dict):
        return {key: stable(item) for key, item in value.items()
                if not any(word in key for word in ("elapsed", "seconds", "time_ns", "deadline"))}
    if isinstance(value, list):
        return [stable(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--builddir", type=Path, required=True)
    build = parser.parse_args().builddir.resolve()
    gold = Golden("native-lift")
    rng = random.Random(0x42ACAC1A)
    formulas = ("G F {g}[i]", "G ({r}[i] -> F {g}[i])",
                "G ({r}[i] -> {g}[i])", "G F ({g}[i] || {r}[i])")
    with tempfile.TemporaryDirectory(dir=build) as temp:
        directory = Path(temp)
        cases = []
        for index, formula in enumerate(formulas):
            r = "controllable_" + "".join(rng.choices("abcdef", k=8))
            g = "uncontrollable_" + "".join(rng.choices("uvwxyz", k=8))
            text = (f'INFO {{ TITLE: "unseen" DESCRIPTION: "unseen" SEMANTICS: Mealy TARGET: Mealy }}\n'
                    f'GLOBAL {{ PARAMETERS {{ span = 5; }} }}\n'
                    f'MAIN {{ INPUTS {{ {r}[span]; }} OUTPUTS {{ {g}[span]; }}\n'
                    f'GUARANTEES {{ &&[0 <= i < span] {formula.format(r=r, g=g)}; }} }}\n')
            cases.append((f"generated-{index}", text))
            if index in (0, 1, 3):
                cases.append((f"renamed-{index}", text.replace(r, "request").replace(g, "grant")))
        fixture = Path(__file__).resolve().parents[1] / "fixtures/gr1_monitor_game"
        cases.extend((p.stem, p.read_text()) for p in sorted(fixture.glob("*.tlsf")))
        observed = {}
        for label, text in cases:
            source = directory / (label + ".tlsf")
            source.write_text(text)
            gold.source(source)
            prefix = directory / label
            result = subprocess.run([str(build / "test/api/native_lift"), str(source), str(prefix), "12"],
                                    text=True, capture_output=True, timeout=20)
            assert result.returncode in (0, 3), (label, result.stdout, result.stderr)
            gold.check("lift", [label, result.returncode])
            if result.returncode == 0:
                evidence = json.loads(prefix.with_suffix(".evidence.json").read_text())
                observed[label] = evidence
                label_kind, expected = gold.records[gold.position]
                gold.position += 1
                assert label_kind == "evidence"
                actual = stable(evidence)
                # Monitor encoding changes alter hashes and role signatures;
                # preserve the independently checked role equivalence classes.
                for rows in (expected["roles"], actual["roles"]):
                    classes = {}
                    for role in rows:
                        signature = role["signature"]
                        role["signature"] = classes.setdefault(signature, len(classes))
                for key in ("game_sha256", "certificate_sha256", "policy_sha256"):
                    expected.pop(key)
                    actual.pop(key)
                assert expected == actual, (label, expected, actual)
                for suffix, hash_key in ((".game.aag", "game_sha256"),
                                         (".cert.aag", "certificate_sha256"),
                                         (".policy.aag", "policy_sha256")):
                    kind, frozen = gold.records[gold.position]
                    gold.position += 1
                    assert kind == suffix
                    text = Path(str(prefix) + suffix).read_text()
                    assert hashlib.sha256(text.encode()).hexdigest() == evidence[hash_key]
                    if suffix == ".game.aag":
                        game_language(frozen, text)
                # Successful public API calls already check the target proof.
                # Research builds also recheck the serialized exports through
                # the CLI, which is not built with research_tools=false.
                if (build / "tlsfcertcheck").is_file():
                    checked = subprocess.run([str(build / "tlsfcertcheck"),
                                              "--method", "certificate", "--certificate",
                                              str(prefix) + ".cert.aag", "--certificate-json", str(prefix) + ".cert.json",
                                              "--policy-json", str(prefix) + ".policy.json", str(prefix) + ".game.aag",
                                              str(prefix) + ".policy.aag"],
                                             capture_output=True, text=True, timeout=60)
                    assert checked.returncode == 0 and checked.stdout.strip().endswith("VERIFIED"), (label, checked.stdout, checked.stderr)
            else:
                gold.check("decline", result.stdout.strip())
        for index in (0, 1, 3):
            for field in ("game_sha256", "certificate_sha256", "seed_values", "roles",
                          "predicate_arities", "method", "verdict"):
                assert observed[f"generated-{index}"][field] == observed[f"renamed-{index}"][field]
    gold.finish()
    print(f"native lift golden cases: {len(cases)}")


if __name__ == "__main__":
    main()
