"""Compare native monitor encodings with frozen pre-rewrite game semantics.

Encoding sizes and acceptance timing can change. Ownership, source binding,
monitor roles, lasso language and native verdicts remain regression contracts.
The committed reference circuits are never rewritten by these checks.
"""
import hashlib
import itertools
import json
import random
from functools import lru_cache


def semantic_provenance(data):
    representation = {"game_sha256", "state_count", "latch_literals", "monitor",
                      "justice_index", "violated_latch_literal", "normalized_formula", "conjunct", "template"}

    def stable(value):
        if isinstance(value, dict):
            return {k: stable(v) for k, v in value.items() if k not in representation}
        if isinstance(value, list):
            return [stable(v) for v in value]
        return value

    result = stable(data)
    if "monitors" in result:
        result["monitors"].sort(key=lambda m: (m["side"], m["construction_formula"]))
    return result


@lru_cache(maxsize=512)
def game_language(reference, actual):
    # Import lazily because the language test also imports Golden.
    from test_native_reduction_language import Game
    old, new = Game(reference), Game(actual)
    assert old.input_names == new.input_names
    assert len(old.justice) == len(new.justice)
    assert len(old.fairness) == len(new.fairness)
    width = len(old.inputs)
    alphabet = range(1 << width)
    if width <= 3:
        words = [([], list(loop)) for size in (1, 2, 3)
                 for loop in itertools.product(alphabet, repeat=size)]
    else:
        words = [([], [0]), ([], [(1 << width) - 1])]
    rng = random.Random(0x9702)
    words += [([rng.randrange(1 << width) for _ in range(rng.randrange(5))],
               [rng.randrange(1 << width) for _ in range(rng.randrange(1, 7))])
              for _ in range(128)]
    for prefix, loop in words:
        assert old.accepts(prefix, loop) == new.accepts(prefix, loop), (prefix, loop)


def provenance(reference, actual):
    left, right = semantic_provenance(reference), semantic_provenance(actual)
    def compare(a, b, path="provenance"):
        if isinstance(a, dict) and isinstance(b, dict):
            assert a.keys() == b.keys(), (path, a.keys(), b.keys())
            for key in a:
                compare(a[key], b[key], path + "." + key)
        elif isinstance(a, list) and isinstance(b, list):
            assert len(a) == len(b), (path, len(a), len(b))
            for i, (x, y) in enumerate(zip(a, b)):
                compare(x, y, path + f"[{i}]")
        else:
            assert a == b, (path, a, b)
    compare(left, right)


def symbols(reference, actual, aag):
    old, new = reference.splitlines(), actual.splitlines()
    assert new[1] == hashlib.sha256(aag.encode()).hexdigest()
    assert old[:1] + old[2:] == new[:1] + new[2:]


def native_artifacts(gold, prefix):
    expected = {}
    for suffix in (".aag", ".json", ".symbols", ".metadata.json"):
        label, value = gold.records[gold.position]
        gold.position += 1
        assert label == suffix
        expected[suffix] = value
    aag = prefix.with_suffix(".aag").read_text()
    data = json.loads(prefix.with_suffix(".json").read_text())
    digest = hashlib.sha256(aag.encode()).hexdigest()
    for monitor in data["monitors"]:
        assert len(monitor["latch_literals"]) == monitor["state_count"]
        assert monitor["state_count"] > 0
    provenance(expected[".json"], data)
    game_language(expected[".aag"], aag)
    symbols(expected[".symbols"], prefix.with_suffix(".symbols").read_text(), aag)
    metadata = json.loads(prefix.with_suffix(".metadata.json").read_text())
    assert metadata["fallback_monitor_count"] == 0
    assert metadata["game_sha256"] == digest
    def stable(value):
        return {k: v for k, v in value.items()
                if k not in ("fallback_monitor_count", "game_sha256")}
    assert stable(expected[".metadata.json"]) == stable(metadata)


def monitor_artifacts(gold, data, text):
    label, expected = gold.records[gold.position]
    gold.position += 1
    assert label == "provenance"
    provenance(expected, data)
    label, expected = gold.records[gold.position]
    gold.position += 1
    assert label == "game"
    game_language(expected, text)


def decline(gold, actual):
    label, expected = gold.records[gold.position]
    gold.position += 1
    assert label == "decline"
    if actual == expected:
        return
    if expected.startswith("reduce status 1: mp-class:"):
        assert actual == "reduce status 1: mp-class: outside proved DPA Buchi fragment\n"
    else:
        # The retired parser's caret diagnostic is replaced by AST validation.
        assert expected.startswith("reduce status 7: reduce: >>>")
        assert actual == "reduce status 7: formula: lowered formula has undeclared APs\n"
