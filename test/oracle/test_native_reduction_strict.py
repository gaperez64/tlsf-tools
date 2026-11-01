#!/usr/bin/env python3
"""Strict roles and lasso language from elementary LTL identities, without an oracle.

The frozen reduction goldens do not contain the two review combinations.
Each family member below has the stated elementary meaning. Safety violations
are the first prefixes with no satisfying continuation; strict safety must hold
until (and excluding) the first assumption violation. Liveness assumptions do
not release that obligation. This evaluates the source semantics, not monitor
tags, states or acceptance marks.
"""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import tempfile

from test_native_reduction_language import Game, tiny


# (source template, semantic identity). x is the current letter, X is next,
# F is eventual truth, G is truth at every position, T/0 are constants.
FAMILY = [
    ("x", "x"),
    ("false U x", "x"),
    ("x R true", "T"),
    ("true U x", "F"),
    ("x W false", "G"),
    ("false M x", "0"),
    ("true M x", "x"),
    ("x U false", "0"),
    ("true R x", "x"),
    ("false R x", "G"),
    ("x U true", "T"),
    ("x M true", "F"),
    ("false W x", "x"),
    ("x W true", "T"),
    ("x R false", "0"),
    ("F x", "F"),
    ("X (false U x)", "X"),
    ("false U (X x)", "X"),
    ("G x", "G"),
    ("F (false U x)", "F"),
]


def meaning(kind, bit, prefix, loop):
    """Return (language membership, shortest bad-prefix length or None)."""
    word = prefix + loop
    values = [bool(letter & (1 << bit)) for letter in word]
    if kind == "T":
        return True, None
    if kind == "0":
        return False, 0
    if kind == "F":
        return any(values), None
    if kind == "G":
        first_false = next((i + 1 for i, value in enumerate(values)
                            if not value), None)
        return all(values), first_false
    index = int(kind == "X")
    letter = (word[index] if index < len(word)
              else loop[(index - len(prefix)) % len(loop)])
    holds = bool(letter & (1 << bit))
    return holds, None if holds else index + 1


def strict_accepts(assumption, guarantee, prefix, loop):
    a_holds, a_bad = meaning(assumption, 0, prefix, loop)
    g_holds, g_bad = meaning(guarantee, 1, prefix, loop)
    if g_bad is not None and (a_bad is None or g_bad < a_bad):
        return False
    return a_bad is not None or not a_holds or g_holds


def reduce(native, directory, assumption, guarantee, mode="strict"):
    def tlsf(formula):
        # TLSF has no infix M; negated weak-until lowers to strong release.
        if " M " in formula:
            left, right = formula.split(" M ")
            return f"!((!({left})) W (!({right})))"
        return formula

    source = directory / "case.tlsf"
    source.write_text(tiny("i", "o", tlsf(assumption) + ";",
                           tlsf(guarantee) + ";"))
    output = directory / "result"
    result = subprocess.run([str(native), str(source), mode, str(output)],
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0, (assumption, guarantee, result.stderr)
    return (Game(output.with_suffix(".aag").read_text()),
            json.loads(output.with_suffix(".json").read_text()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--builddir", type=Path, required=True)
    args = parser.parse_args()
    build = args.builddir.resolve()
    native = build / "test/api/native_reduction"
    words = [(list(prefix), list(loop))
             for prefix_size in range(3) for loop_size in (1, 2)
             for prefix in itertools.product(range(4), repeat=prefix_size)
             for loop in itertools.product(range(4), repeat=loop_size)]
    checks = 0
    with tempfile.TemporaryDirectory(prefix="native-strict-", dir=build) as temp:
        directory = Path(temp)
        # Both rows of the phase-2 review table, including exact-mode control.
        for a, g, expected, roles in [
            ("false U i", "o", True, ["violated", "bad"]),
            ("F i", "false U o", False, ["fairness", "bad"]),
        ]:
            game, data = reduce(native, directory, a, g)
            assert [m["role"] for m in data["monitors"]] == roles
            assert game.accepts([], [0]) == expected, (a, g)
            exact, _ = reduce(native, directory, a, g, "exact")
            assert exact.accepts([], [0])
        for (a, ak), (g, gk) in itertools.product(FAMILY, repeat=2):
            game, data = reduce(native, directory, a.replace("x", "i"),
                                g.replace("x", "o"))
            for monitor in data["monitors"]:
                assumption = monitor["side"] == "assumption"
                kind = ak if assumption else gk
                if kind == "F":
                    role = "fairness" if assumption else "justice"
                else:
                    role = "violated" if assumption else "bad"
                assert monitor["role"] == role, (a, g, monitor)
            for prefix, loop in words:
                expected = strict_accepts(ak, gk, prefix, loop)
                assert game.accepts(prefix, loop) == expected, (
                    a, g, prefix, loop, expected)
                checks += 1
    print(f"strict semantics: 2 review regressions, {len(FAMILY) ** 2} formula "
          f"pairs, {checks} direct-semantic lasso comparisons")


if __name__ == "__main__":
    main()
