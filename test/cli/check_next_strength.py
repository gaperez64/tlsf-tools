"""Issues #117/#122: compare objectives with independent finite-word semantics."""
import argparse
import itertools
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/golden"))
from reference import atoms, evaluate, parse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("ltl")
parser.add_argument("norm")
parser.add_argument("--pre-passes", default="pre-indexed-x",
                    choices=("pre-indexed-x", "pre-weak", "pre-spine-split", "pre-safe"))
args = parser.parse_args()
ltl, norm = args.ltl, args.norm


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

if args.pre_passes != "pre-indexed-x":
    cases = []
    # Both operand orders: unlike next on infinite words, these operands
    # differ at a finite word's last position. OR exercises the other unsafe
    # deduplication order as well as AND's issue witness.
    for left, right in (("X[1] p", "X[!1] p"), ("X[!1] p", "X[1] p")):
        for op in ("&&", "||"):
            cases.append((f"({left}) {op} ({right})",
                          parse(f"({'X[!]' if '!' in left else 'X'} p) {op} "
                                f"({'X[!]' if '!' in right else 'X'} p)")))
    for strong in (False, True):
        for count in (0, 1, 2):
            form = (f"X[{'!' if strong else ''}{count}]", strong, count)
            # Changed children force pre-weak reconstruction; conjunctions
            # force pre-spine-split reconstruction, including nested spines.
            for body in ("a && b", "b && a", "p && true", "true && p",
                         "p || false", "false || p", "G (a && b)"):
                cases.append(wrap(form, body, parse(body)))
    cases += [("X[!1] X[1] (a && b)", parse("X[!] X (a && b)")),
              ("X[1] X[!1] (b && a)", parse("X X[!] (b && a)"))]

    def compare_pair(left, right):
        for (lexpr, lref), (rexpr, rref) in ((left, right), (right, left)):
            for op in ("&&", "||"):
                cases.append((f"({lexpr}) {op} ({rexpr})",
                              parse(f"({lref}) {op} ({rref})")))

    # Equality runs before expansion: every wrapper must retain its body.
    # Construct the reference independently of either C frontend.
    for context, reference in (
            ("G[0:0] ({})", "{}"), ("F[0:0] ({})", "{}"),
            ("G[0:1] ({0})", "({0}) && X ({0})"),
            ("F[0:1] ({0})", "({0}) || X ({0})"),
            ("G[0:0] F[0:0] ({})", "{}"),
            ("F[0:0] G[0:0] ({})", "{}"),
            ("G ({})", "G ({})"), ("F ({})", "F ({})"),
            ("!({})", "!({})"), ("X ({})", "X ({})"),
            ("X[!] ({})", "X[!] ({})"), ("X[0] ({})", "{}"),
            ("X[1] ({})", "X ({})"), ("X[!1] ({})", "X[!] ({})"),
            ("&&[i IN {{0}}] ({})", "{}"),
            ("||[i IN {{0}}] ({})", "{}"),
            ("&&[0 <= i <= 0] ({})", "{}"),
            ("||[0 <= i <= 0] ({})", "{}"),
            ("identity({})", "{}")):
        compare_pair((context.format("X[1] p"), reference.format("X p")),
                     (context.format("X[!1] p"), reference.format("X[!] p")))

    for temporal, op in (("G", "&&"), ("F", "||")):
        # Check both bounds, the range's own next strength, and distinct
        # ranges nested inside equal-strength indexed next bodies.
        compare_pair((f"{temporal}[0:0] p", "p"),
                     (f"{temporal}[0:1] p", f"p {op} X p"))
        compare_pair((f"{temporal}[0:1] p", f"p {op} X p"),
                     (f"{temporal}[1:1] p", "X p"))
        compare_pair((f"{temporal}[0:1] p", f"p {op} X p"),
                     (f"{temporal}[!0:1] p", f"p {op} X[!] p"))
        compare_pair((f"X[!1] ({temporal}[0:0] a)", "X[!] a"),
                     (f"X[!1] ({temporal}[0:0] b)", "X[!] b"))
        compare_pair((f"X[1] ({temporal}[0:0] p)", "X p"),
                     (f"X[1] ({temporal}[0:1] p)", f"X (p {op} X p)"))

semantic_checks = 0
mismatches = []
for expression, expected in cases:
    source = ("INFO { SEMANTICS: Finite,Mealy TARGET: Mealy } "
              "GLOBAL { DEFINITIONS { identity(value) = value; } } "
              f"MAIN {{ INPUTS {{ p; a; b; }} GUARANTEES {{ {expression}; }} }}")
    normalized = run([norm, "--pre-passes", args.pre_passes, "--passes", "off"], source)
    direct = parse(run([ltl, "--format", "ltl"], source))
    emitted = parse(run([ltl, "--format", "ltl"], normalized))
    # An exact sequence check also detects incorrect counts which sampling
    # might miss. Expected syntax is constructed above without a C converter.
    if args.pre_passes == "pre-indexed-x":
        assert direct == emitted == expected, (expression, direct, emitted, expected)
    names = sorted(atoms(expected) | atoms(direct) | atoms(emitted))
    if expression in reproducers:
        assert not names
        assert [evaluate(emitted, [], [0] * n) for n in (1, 2)] == reproducers[expression][1]
    for length in (1, 2, 3):
        for word in itertools.product(range(1 << len(names)), repeat=length):
            for j in range(length):
                reference = evaluate(expected, names, word[j:])
                assert evaluate(direct, names, word[j:]) == reference, (expression, direct, expected)
                if evaluate(emitted, names, word[j:]) != reference and (
                        not mismatches or mismatches[-1][0] != expression):
                    mismatches.append((expression, word, j, emitted, expected))
                semantic_checks += 1

# The erroneous all-weak output differs from every reproducer on a short word.
assert [evaluate(parse("X X true"), [], [0] * n) for n in (1, 2)] == [True, True]

assert not mismatches, (args.pre_passes, "finite-word mismatches", mismatches)
print(f"next strength ({args.pre_passes}): {len(cases)} CLI cases; "
      f"{semantic_checks} finite position checks passed")
