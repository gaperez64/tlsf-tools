#!/usr/bin/env python3
"""Independent evaluator boundaries and external-oracle guard mutation tests."""
import copy
import hashlib
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


def check_frozen_additions(guard, root):
    name = "test/fixtures/golden/provenance.json"
    receipt = json.loads((ROOT / "tools/golden/historical-files.json").read_text())[name]
    reference = receipt["additive_update"]
    ledger = json.loads((ROOT / reference["ledger"]).read_text())
    payload = (ROOT / name).read_bytes()
    # Equality must preserve scalar types even through nested objects/arrays.
    for value in (True, 1.0, 1.0000000000000001):
        before = {"nested": [1]}
        after = {"nested": [value]}
        assert not guard.same_json_value(before, after)
        assert not guard.same_json_value(after, before)
    assert guard.same_json_value({"nested": [1, True, 1.0]}, {"nested": [1, True, 1.0]})
    historical = guard.frozen_payload(ROOT, name, receipt)
    assert hashlib.sha256(historical).hexdigest() == receipt["sha256"]
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    ledger_path = root / reference["ledger"]
    ledger_path.parent.mkdir(parents=True, exist_ok=True)

    def verify(binding):
        restored = guard.frozen_payload(root, name, binding)
        assert hashlib.sha256(restored).hexdigest() == receipt["sha256"]

    def publish(candidate, update, rehash=False):
        binding = copy.deepcopy(receipt)
        if rehash:
            update["manifest_additions"]["current_sha256"] = hashlib.sha256(candidate).hexdigest()
        raw = (json.dumps(update, indent=2) + "\n").encode()
        binding["additive_update"]["sha256"] = hashlib.sha256(raw).hexdigest()
        path.write_bytes(candidate)
        ledger_path.write_bytes(raw)
        return binding

    binding = publish(payload, copy.deepcopy(ledger))
    assert guard.frozen_payload(root, name, binding) == historical
    cases = 0

    def reject(candidate, update, label):
        nonlocal cases
        binding = publish(candidate, update, rehash=True)
        # The restoration boundary itself must reject mutants, even when all
        # mutable hashes are refreshed and the historical freeze is unchanged.
        assert binding["sha256"] == receipt["sha256"]
        assert_rejected(lambda: guard.frozen_payload(root, name, binding), label)
        cases += 1

    def insert(offset, text, record=True):
        update = copy.deepcopy(ledger)
        entries = update["manifest_additions"]["insertions"]
        for entry in entries:
            if entry["offset"] >= offset:
                entry["offset"] += len(text)
        if record:
            entries.append({"offset": offset, "text": text.decode()})
            entries.sort(key=lambda entry: entry["offset"])
        return payload[:offset] + text + payload[offset:], update

    # Reproduce the review attacks with a third recorded insertion. Each
    # removal still recovers the exact historical bytes, so hashes alone
    # cannot reject these changes to the extended manifest.
    index = payload.index(b'"index": 1,') + len(b'"index": 1')
    count = payload.index(b'"cases": 436,') + len(b'"cases": 436')
    for offset, text, label in (
            (index, b', "index": true', "duplicate historical index shadowed by bool"),
            (count, b'.0000000000000001', "historical integer rounded through float"),
            (0, b' ', "recorded leading whitespace"),
            (index, b', "unapproved": true', "third field insertion")):
        candidate, update = insert(offset, text)
        reject(candidate, update, label)
    # An unrecorded whitespace change compares equal as parsed JSON; the
    # restoration boundary must verify the original byte hash as well.
    candidate, update = insert(0, b' ', record=False)
    reject(candidate, update, "unrecorded historical whitespace")
    # Exercise duplicate-key rejection with only the two approved insertions,
    # including an equal-valued duplicate that ordinary dict equality hides.
    for text in (b', "index": 1', b', "index": true'):
        candidate, update = insert(index, text, record=False)
        reject(candidate, update, "duplicate historical key")
    update = copy.deepcopy(ledger)
    offset = update["manifest_additions"]["insertions"][0]["offset"]
    update["manifest_additions"]["insertions"][0]["offset"] = float(offset)
    reject(payload, update, "non-integer insertion offset")
    # A duplicate in the ledger is invalid too, even with a matching hash.
    binding = publish(payload, copy.deepcopy(ledger))
    raw = ledger_path.read_bytes().replace(b'"date":', b'"date": "shadowed", "date":', 1)
    ledger_path.write_bytes(raw)
    binding["additive_update"]["sha256"] = hashlib.sha256(raw).hexdigest()
    assert_rejected(lambda: guard.frozen_payload(root, name, binding), "duplicate ledger key")
    cases += 1
    # Rehashing the current manifest and ledger cannot authorize changes to
    # the original entries, their ordering, or their whitespace.
    for candidate in (payload + b"\n", payload.replace(b'"status":', b'"changed_status":', 1),
                      payload.replace(b'"automata": 112', b'"automata": 113', 1)):
        binding = publish(candidate, copy.deepcopy(ledger), rehash=True)
        assert_rejected(lambda: verify(binding), "historical/addition edit")
        cases += 1
    # Even with freshly recorded insertions, only the two named in-house
    # fields are allowed, and their values cannot introduce a dependency.
    for before, after in ((b'"row_identity": {', b'"unrecorded": true, "row_identity": {'),
                          (b'"row_identity": {', b'"row_identity": { '),
                          (b'"automata": 112', b'"automata": 112.0000000000000001'),
                          (b'"automata": 112', b'"automata": NaN'),
                          (b'"automata": 112', b'"automata": 112, "automata": 112'),
                          (b'"row_identity": {', b'"wrong_path": {'),
                          (b'"dpa_row_identity"', json.dumps(next(iter(guard.MODULES))).encode())):
        candidate = payload.replace(before, after, 1)
        assert candidate != payload
        update = copy.deepcopy(ledger)
        for entry in update["manifest_additions"]["insertions"]:
            entry["text"] = entry["text"].replace(before.decode(), after.decode(), 1)
        binding = publish(candidate, update, rehash=True)
        assert_rejected(lambda: verify(binding), "unapproved addition")
        cases += 1
    binding = publish(payload, copy.deepcopy(ledger))
    ledger_path.write_bytes(ledger_path.read_bytes() + b"\n")
    assert_rejected(lambda: verify(binding), "changed addition ledger")
    return cases + 1


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
        frozen_mutants = check_frozen_additions(guard, root)
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
          f"{frozen_mutants} frozen-provenance mutants rejected; "
          "decline-everything and four failed certificates rejected; historical files untouched")


if __name__ == "__main__":
    main()
