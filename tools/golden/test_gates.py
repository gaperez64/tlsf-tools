#!/usr/bin/env python3
"""Independent evaluator boundaries and external-oracle guard mutation tests."""
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

from reference import evaluate, membership, parse, random_formulas, sample_equivalent
from regenerate import ROOT, fingerprints, verify_native_verdict


def assert_rejected(action, label):
    try:
        action()
    except AssertionError:
        return
    raise AssertionError((label, "guard accepted mutant"))


def check_guard_mutations(guard, root):
    (root / "tools/golden").mkdir(parents=True)
    (root / "tools/golden/historical-files.json").write_text("{}")
    data_path = root / guard.DATA_FILE
    data = (ROOT / guard.DATA_FILE).read_bytes()
    data_path.write_bytes(data)
    for name in ("meson.build", "meson.options", "README.md"):
        (root / name).write_text("")
    sources = {}
    for name in ("test/cli/check_no_external_oracles.py", "tools/golden/test_gates.py"):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        sources[path] = (ROOT / name).read_text()
        path.write_text(sources[path])
    guard.check(root)
    cases = 0
    for directory in ("tools", "scripts", "bench", "test"):
        (root / directory).mkdir(exist_ok=True)
        for payload in guard.DATA["text_mutants"]:
            path = root / directory / ("mutant" + payload["suffix"])
            path.write_text(payload["source"])
            assert_rejected(lambda: guard.check(root), path)
            path.unlink()
            cases += 1
    # Test AST detection independently: text matching must not mask an AST gap.
    for payload in guard.DATA["python_mutants"]:
        assert_rejected(lambda: guard.inspect_python(payload["name"], payload["source"]),
                        payload["name"])
    # Both formerly exempt executable files must reject added code AND comments.
    for path, original in sources.items():
        for payload in [*guard.DATA["python_mutants"],
                        *(p for p in guard.DATA["text_mutants"] if p["suffix"] == ".py")]:
            path.write_text(original + "\n" + payload["source"] + "\n")
            assert_rejected(lambda: guard.check(root), (path, payload))
            cases += 1
        path.write_text(original)
    for tool in guard.TOOLS:
        assert guard.FORBIDDEN.search(tool)
    # The data exemption is bound to exact bytes, even for valid JSON changes.
    data_path.write_bytes(data + b"\n")
    assert_rejected(lambda: guard.check(root), "changed guard data")
    data_path.write_bytes(data)
    cases += 1
    valid_path = root / "scripts/legitimate.py"
    valid_path.write_text("\n".join(guard.DATA["valid_python"]))
    guard.inspect_python(valid_path, valid_path.read_text())
    guard.check(root)
    return cases


def main():
    (ROOT / "build-sprint/tmp").mkdir(parents=True, exist_ok=True)
    before = fingerprints()
    cases = 0
    for n in range(1, 5):
        for word in itertools.product(range(4), repeat=n):
            a = [bool(x & 1) for x in word]
            b = [bool(x & 2) for x in word]
            # Quantified direct definitions, independent of fixed-point code.
            until = any(b[j] and all(a[:j]) for j in range(n))
            strong_release = any(a[j] and all(b[:j + 1]) for j in range(n))
            for loop in [None, *range(n)]:
                expected = {"a U b": until, "a W b": until or all(a),
                            "a M b": strong_release, "a R b": strong_release or all(b),
                            "F a": any(a), "G a": all(a),
                            "X a": (a[1] if n > 1 else True) if loop is None else a[1 if n > 1 else loop],
                            "X[!] a": (a[1] if n > 1 else False) if loop is None else a[1 if n > 1 else loop],
                            "G F a": a[-1] if loop is None else any(a[loop:]),
                            "F G a": a[-1] if loop is None else all(a[loop:])}
                for formula, value in expected.items():
                    assert evaluate(parse(formula), ["a", "b"], word, loop) == value, (formula, word, loop)
                    cases += 1
    assert membership('G ("Grant" -> F "@")', ["Grant", "@"], [([], [1, 2])]) == "1"
    assert parse("GXc") == parse("G X c")
    assert parse("!XF!c") == parse("! X F !c")
    assert parse("GX(0)") == parse("G X false")
    sample_equivalent("a xor b", "!(a <-> b)")
    # Implication binds less tightly than equivalence in the reference dialect.
    # The toggle/response golden exercises this distinction in a temporal game.
    sample_equivalent("a -> b <-> c", "a -> (b <-> c)")
    assert evaluate(parse("a -> b <-> c"), ["a", "b", "c"], [0])
    for formula in ("", "a b", "(a", "a &", "a ? b"):
        try:
            parse(formula)
        except ValueError:
            pass
        else:
            raise AssertionError(formula)
    for finite in (False, True):
        sample_equivalent("a W b", "(a U b) | G a", finite=finite)
        sample_equivalent("a M b", "b U (a & b)", finite=finite)
        sample_equivalent("a R b", "!(!a U !b)", finite=finite)
        sample_equivalent("X[!] a", "!X !a", finite=finite)
    assert random_formulas() == random_formulas() and random_formulas(1) != random_formulas(2)
    spec = importlib.util.spec_from_file_location("oracle_guard", ROOT / "test/cli/check_no_external_oracles.py")
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    with tempfile.TemporaryDirectory(dir=ROOT / "build-sprint/tmp") as temp:
        root = Path(temp)
        mutants = check_guard_mutations(guard, root)
        fake = root / "build/test/api/native_reduction"
        fake.parent.mkdir(parents=True)
        fake.write_text('#!/bin/sh\necho "injected erroneous decline" >&2\nexit 3\n')
        fake.chmod(0o755)
        mutant = subprocess.run([sys.executable, ROOT / "test/oracle/test_native_reduction.py",
                                 "--builddir", root / "build"],
                                text=True, capture_output=True, timeout=30)
        assert mutant.returncode != 0 and "AssertionError" in mutant.stderr, mutant
        # Refuting a candidate certificate must never become UNREALIZABLE.
        # This covers both system and dual environment certificate paths.
        for solved_status in (0, 1):
            for failed_check in (1, 6):
                def rejected_certificate(command, **kwargs):
                    name = Path(command[0]).name
                    if name == "native_reduction":
                        status = 0
                    elif name == "tlsfsolve":
                        cert = Path(command[command.index("--certificate") + 1])
                        Path(str(cert) + ".json").write_text(json.dumps({
                            "side": "system" if solved_status == 0 else "environment"}))
                        status = solved_status
                    else:
                        assert name == "tlsfcertcheck"
                        status = failed_check
                    return subprocess.CompletedProcess(command, status, "", "")
                with patch("regenerate.run", side_effect=rejected_certificate):
                    assert verify_native_verdict(root, root, ["G a", "", "a", False, False]) is None
    assert fingerprints() == before
    print(f"offline gates: {cases} direct semantic checks; {mutants} forbidden dependency mutants, "
          f"{len(guard.DATA['python_mutants'])} direct AST rejections, "
          f"{len(guard.DATA['valid_python'])} legitimate snippets accepted; "
          "decline-everything and four failed certificates rejected; historical files untouched")


if __name__ == "__main__":
    main()
