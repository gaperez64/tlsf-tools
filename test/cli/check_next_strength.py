"""Issue #117: compare emitted objectives with independent finite-word semantics."""
import itertools
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/golden"))
from reference import atoms, evaluate, parse

ltl, norm = sys.argv[1:]


def run(command, text):
    result = subprocess.run(command, input=text, capture_output=True, text=True, timeout=10)
    assert result.returncode == 0, (command, text, result)
    assert "runtime error:" not in result.stderr, (command, text, result)
    return result.stdout


def wrap(form, expression, tree):
    spelling, strong, count = form
    for _ in range(count):
        tree = ("X[!]" if strong else "X", tree)
    return f"{spelling} ({expression})", tree


# Indexed zeroes of either strength are identities. Unary strong next only
# reconstructs; mixed positive chains retain their order and terminal behavior.
forms = [("X", False, 1), ("X[!]", True, 1)] + [
    (f"X[{'!' if strong else ''}{count}]", strong, count)
    for strong in (False, True) for count in (0, 1, 2)
]
cases = []
for body in ("true", "false", "p"):
    for outer, inner in itertools.product(forms, repeat=2):
        expression, tree = wrap(inner, body, parse(body))
        cases.append(wrap(outer, expression, tree))
    # Recursive child changes can expose a merge or require reconstruction.
    for outer in forms:
        expression, tree = wrap(("X[2]", False, 2), body, parse(body))
        expression, tree = wrap(("X[1]", False, 1), expression, tree)
        cases.append(wrap(outer, expression, tree))
        for context, ref in (("!({})", lambda t: ("!", t)),
                             ("G ({})", lambda t: ("G", t)),
                             ("F ({})", lambda t: ("F", t)),
                             ("({}) && p", lambda t: ("&", t, ("ap", "p"))),
                             ("({}) || p", lambda t: ("|", t, ("ap", "p"))),
                             ("({}) -> p", lambda t: ("i", t, ("ap", "p"))),
                             ("({}) <-> p", lambda t: ("e", t, ("ap", "p")))):
            expression, tree = wrap(("X[!0]", True, 0), body, parse(body))
            cases.append(wrap(outer, context.format(expression), ref(tree)))

reproducers = {
    "X[!1] X true": ("X[!] X true", [False, True]),
    "X X[!1] true": ("X X[!] true", [True, False]),
    "X[1] X[!1] true": ("X X[!] true", [True, False]),
}
cases += [(expression, parse(reference)) for expression, (reference, _) in reproducers.items()]

semantic_checks = 0
for expression, expected in cases:
    source = ("INFO { SEMANTICS: Finite,Mealy TARGET: Mealy } "
              f"MAIN {{ INPUTS {{ p; }} GUARANTEES {{ {expression}; }} }}")
    normalized = run([norm, "--pre-passes", "pre-indexed-x", "--passes", "off"], source)
    direct = parse(run([ltl, "--format", "ltl"], source))
    emitted = parse(run([ltl, "--format", "ltl"], normalized))
    # An exact sequence check also detects incorrect counts which sampling
    # might miss. Expected syntax is constructed above without a C converter.
    assert direct == emitted == expected, (expression, direct, emitted, expected)
    names = sorted(atoms(expected))
    if expression in reproducers:
        assert not names
        assert [evaluate(emitted, [], [0] * n) for n in (1, 2)] == reproducers[expression][1]
    for length in (1, 2, 3):
        for word in itertools.product(range(1 << len(names)), repeat=length):
            for j in range(length):
                assert evaluate(emitted, names, word[j:]) == evaluate(expected, names, word[j:]), (
                    expression, word, j, emitted, expected)
                semantic_checks += 1

# The erroneous all-weak output differs from every reproducer on a short word.
assert [evaluate(parse("X X true"), [], [0] * n) for n in (1, 2)] == [True, True]

print(f"next strength: {len(cases)} CLI cases; {semantic_checks} finite position checks passed")
