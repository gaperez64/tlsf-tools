"""TLSF §4.6 longest match, with Table 1 inside every guard and value.

Use --generated --main-bin DIR for the sequential differential. Every changed
observation is checked against an explicit longest-match control and classified;
main's choices never select the candidate's expected partition. Inputs use stdin
so this test does not change the historical corpus-impact input set.
"""
import argparse
from collections import Counter
import itertools
import json
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("ltl")
parser.add_argument("tlsf")
parser.add_argument("--main-bin", type=Path)
parser.add_argument("--generated", action="store_true")
parser.add_argument("--evidence", type=Path)
args = parser.parse_args()
counts = Counter()
differences = []
excluded_references = []


def source(body, query="true"):
    return ("INFO { SEMANTICS: Finite,Mealy TARGET: Mealy } "
            "GLOBAL { DEFINITIONS { z = 0; id(x) = x; zero(x) = 0; "
            f"f(n) = {body}; }} }} MAIN {{ OUTPUTS {{ o; bus[64]; }} "
            f"GUARANTEE {{ {query}; }} }}")


def run(body, query, mode, baseline=False):
    binary = args.ltl if mode == "ltl" else args.tlsf
    env = dict(os.environ)
    if baseline:
        binary = str(args.main_bin.resolve() / ("tlsf2ltl-main" if mode == "ltl"
                                                else "tlsf2tlsf-main"))
        env["LD_LIBRARY_PATH"] = str(args.main_bin.resolve())
    flags = (["--format", "ltl", "--parenthesize"] if mode == "ltl"
             else ["--basic"] if mode == "basic" else [])
    result = subprocess.run([binary, *flags], input=source(body, query), text=True,
                            capture_output=True, env=env, timeout=17)
    if not baseline:
        assert result.returncode >= 0, (body, query, mode, result.returncode, result.stderr)
    return dict(status=result.returncode, stdout=result.stdout, stderr=result.stderr)


def outcome(result):
    return result["status"], result["stdout"]


def check(raw, explicit, query="true", expected=None, expand=False):
    for mode in ["parse", *(["ltl", "basic"] if expand else [])]:
        actual = run(raw, query, mode)
        control = run(explicit, query, mode)
        assert outcome(actual) == outcome(control), (raw, explicit, mode, actual, control)
        assert actual["status"] == 0, (raw, mode, actual)
        if mode == "ltl" and expected is not None:
            assert actual["stdout"] == expected, (raw, actual, expected)
        counts[mode + " checks"] += 1


# Deliberately explicit oracle: '-' extends the value, and '(' extends a final
# bare identifier as a call. Reduction starts cannot be binary continuations:
# after the operator '[' cannot start its right operand. All other starts end
# the preceding expression. Parenthesized values force an earlier boundary.
guards = [
    "-n < 0", "MINUS n < 0", "(n) == 1", "((n)) == 1", "(-n) < 0",
    "!o ~ !p", "NOT o ~ !p", "|{1}| == 1", "SIZE {1} == 1",
    "MIN {1} == 1", "MAX {1} == 1", "SIZEOF bus == 64",
    "X o ~ X p", "F o ~ F p", "G o ~ G p", "X[1] o ~ X p",
    "X[!] o ~ X[!] p", "X[!1] o ~ p", "X[1!] o ~ p",
    "F[1:2] o ~ p", "G[1:2] o ~ p", "F[!1:2] o ~ p", "G[!1:2] o ~ p",
    "F[1:2!] o ~ p", "G[1:2!] o ~ p", "id(n) == 1", "n == 1",
    "1 == 1", "true ~ p", "false ~ p", "bus[0] ~ p", "{1} ~ p",
    "-z == zero(true)", "-id(n) < zero(true)", "(o) ~ zero(true) == 0",
]
for op in ["&&", "AND", "FORALL", "||", "OR", "EXISTS"]:
    guards.append(f"{op}[k IN {{1}}] o ~ p")
for op in ["+", "PLUS", "SUM", "*", "MUL", "PROD"]:
    guards.append(f"{op}[k IN {{1}}] k == 1")
for op in ["(+)", "CUP", "(*)", "CAP"]:
    guards.append(f"{op}[k IN {{1}}] {{k}} ~ p")
for op in ["&&", "||", "SUM", "PROD"]:
    guards.append(f"{op}[0 <= k < 2] k == 1")

# Whether the last atom can become a call is explicit test data, independent
# of the parser under test (SIZEOF's identifier, for example, is not an atom).
values = [("o", True, "formula"), ("0", False, "number"),
          ("id(n)", False, "number"), ("(o)", False, "formula")]
if args.generated:
    assert args.main_bin, "--generated requires --main-bin"
    values += [(v, call, kind) for kind, vs in {
        "number": [("1", False), ("-1", False), ("z", True), ("(1)", False),
                   ("1 + 2", False), ("1 * 2", False), ("1 - 2", False),
                   ("|{1}|", False), ("SIZEOF bus", False),
                   *[(f"{op}[k IN {{1,2}}] k", True)
                     for op in ["SUM", "PROD", "+", "*", "PLUS", "MUL"]],
                   ("SUM[k IN {1,2}] k + 1", False),
                   ("PROD[k IN {2,3}] k + 1", False),
                   ("SUM[k IN {1,2}] k - z", True),
                   ("SUM[k IN {1,2}] k * 2", False)],
        "formula": [("!o", True), ("X o", True), ("F o", True), ("G o", True),
                    ("o && o", True), ("o || o", True), ("o -> o", True),
                    ("o U o", True), ("&&[k IN {1}] o", True),
                    ("||[k IN {1}] o", True), ("|CUP[k IN {1}] {k}| == 1", False),
                    ("id(o)", False), ("NOT o", True), ("X[1] o", True),
                    ("F[0:1] o", True), ("G[0:1] o", True)],
        "set": [("{1}", False), ("CUP[k IN {1,2}] {k}", False),
                ("CAP[k IN {1}] {k}", False), ("(+)[k IN {1,2}] {k}", False),
                ("(*)[k IN {1}] {k}", False)],
    }.items() for v, call in vs]


def continues(value_can_call, guard):
    return guard.startswith(("-", "MINUS ")) or (value_can_call and guard.startswith("(")
            and not guard.startswith(("(+)", "(*)")))


def generated_check(value, call, kind, next_guards, tail):
    end = "1" if kind == "number" else "!o" if kind == "formula" else "{1}"
    default = "2" if kind == "number" else "o" if kind == "formula" else "{2}"
    suffix = f" otherwise : {default}" if tail else ""
    raw = f"n == 0 : {value}"
    explicit_cases = []
    short_cases = []
    main_short_cases = []
    guard = "n == 0"
    overlaps = []
    for index, next_guard in enumerate(next_guards):
        next_value = end if index == len(next_guards) - 1 else value
        raw += f" {next_guard} : {next_value}"
        overlap = continues(call, next_guard)
        overlaps.append(overlap)
        if overlap:
            guard = f"({guard} : ({value} {next_guard}))"
        else:
            explicit_cases.append(f"({guard}) : ({value})")
            guard = next_guard
        short_cases.append(f"({value}) ({next_guard}) : ")
        main_short_cases.append(f"({value}) {next_guard} : ")
    explicit_cases.append(f"({guard}) : ({end})")
    explicit = " ".join(explicit_cases) + suffix
    raw += suffix
    # Force every boundary, preserving the unparenthesized expressions inside.
    # Main requires a comparison/match at the guard's outer level; wrap only
    # values for its control, leaving the guard's operator outside parentheses.
    short = "n == 0 : " + "".join(short_cases) + f"({end})" + suffix
    main_short = "n == 0 : " + "".join(main_short_cases) + f"({end})" + suffix
    check(raw, explicit)
    counts["generated definitions" if args.generated else "fixed definitions"] += 1
    if args.generated and counts["generated definitions"] % 1000 == 0:
        print("differential progress: " + json.dumps(counts, sort_keys=True), flush=True)
    if not args.main_bin:
        return
    for n in ([0, 1, 2] if args.generated else [1]):
        query = (f"bus[f({n}) + 16]" if kind == "number" else
                 f"f({n})" if kind == "formula" else f"bus[|f({n})|]")
        old = run(raw, query, "ltl", baseline=True)
        new = run(raw, query, "ltl")
        control = run(explicit, query, "ltl")
        assert outcome(new) == outcome(control), (raw, new, control)
        counts["differential observations"] += 1
        if old["status"]:
            counts["outside main-accepted domain"] += 1
            continue
        # Preserve the previous generator's well-typed reference domain. Main
        # also accepts invalid patterns or unused ill-typed cases. Those are
        # existing scoping/typing changes, outside this boundary differential.
        short_control = run(short, query, "ltl")
        if short_control["status"]:
            assert "expand:" in short_control["stderr"], (raw, short, short_control)
            counts["ill-typed explicit reference partition"] += 1
            excluded_references.append(dict(body=raw, reference=short, query=query,
                                            diagnostic=short_control["stderr"]))
            continue
        counts["compared observations"] += 1
        if outcome(old) == outcome(new):
            counts["unchanged observations"] += 1
            continue
        old_control = run(main_short, query, "ltl", baseline=True)
        boundary_changes = (outcome(new) != outcome(short_control) or
                            outcome(old) != outcome(old_control))
        if boundary_changes:
            assert any(overlaps), ("unexplained boundary", raw, old, old_control, new, short_control)
            category = "longest match"
            rule = "§4.6 longest expression; Table 1 row 19 left-associated colon"
        else:
            category = "Table 1"
            # In this generated domain only reductions followed by an operator
            # differ inside fixed guards/values; the 464-row test covers the
            # complete table independently.
            assert any(op in value or any(op in g for g in next_guards)
                       for op in ["SUM[", "PROD[", "+[", "*[", "PLUS[", "MUL[",
                                  "CUP[", "CAP[", "(+)[", "(*)[", "&&[", "||["]), raw
            rule = "Table 1 rows 1/5/11: reduction operand ends at its row"
        counts["differences: " + category] += 1
        differences.append(dict(body=raw, explicit=explicit, reference=short, main_reference_body=main_short,
                                query=query, category=category, rule=rule,
                                main=old, candidate=new, control=control,
                                main_reference=old_control, candidate_reference=short_control))


for (value, call, kind), guard, tail in itertools.product(values, guards, [False, True]):
    generated_check(value, call, kind, [guard], tail)
if args.generated:
    # All pairs of boundary starts exercise two successive uncertain boundaries,
    # including ones after an earlier continuation, without an otherwise tail.
    for first, second in itertools.product(guards, repeat=2):
        for value, call, kind in [("SUM[k IN {1,2}] k + 1", False, "number"),
                                  ("o", True, "formula")]:
            generated_check(value, call, kind, [first, second], False)


# Observable longest-match changes, including unary/binary minus and calls.
check("n == 0 : 0 -n < 0 : 1 otherwise : 2",
      "(n == 0 : (0 - n < 0)) : 1 otherwise : 2",
      "f(1) == 2", "true\n", expand=True)
check("n == 0 : zero (n) == 0 : 1 otherwise : 2",
      "(n == 0 : (zero(n) == 0)) : 1 otherwise : 2",
      "f(1) == 2", "true\n", expand=True)
for op in ["SUM", "PROD", "+", "*", "PLUS", "MUL"]:
    check(f"n == 0 : {op}[k IN {{1}}] k -id(n) < 0 : 1 otherwise : 2",
          f"(n == 0 : (({op}[k IN {{1}}] k) - id(n) < 0)) : 1 otherwise : 2",
          "f(1) == 2", "true\n", expand=True)
check("n == 0 : (0) (-n < 0) : 1 otherwise : 2",
      "n == 0 : (0) ((-n) < 0) : 1 otherwise : 2",
      "f(1) == 1", "true\n", expand=True)
# Later boundaries, comments, newlines, and chained ':' inside a case list.
check("n == 0 : (0) (n) == 2 :\n SUM[k IN {1}] k /*continue*/ -id\n (n) < 0 : 1 otherwise : 2",
      "n == 0 : (0) ((n) == 2 : ((SUM[k IN {1}] k) - id(n) < 0)) : 1 otherwise : 2")
for value in ["!o", "X o", "o && o", "o || o", "o -> o", "o U o"]:
    check(f"n == 0 : {value} (n) == 1 : !o otherwise : o",
          f"(n == 0 : ({value} (n) == 1)) : !o otherwise : o")
check("n - 1 - 1 < 0 : 10 - 3 - 2 otherwise : 9 - 4 - 2",
      "((n - 1) - 1) < 0 : ((10 - 3) - 2) otherwise : ((9 - 4) - 2)",
      "f(0) == 5", "true\n", expand=True)
# Prefixes at different Table 1 levels still compose without parentheses.
# In particular row 1 MIN/MAX/SIZE accept a row 5 set reduction as operand.
for reduction, literal, expected in [
        ("CUP", "{k}", {"MIN": 1, "MAX": 2, "SIZE": 2}),
        ("(+)", "{k}", {"MIN": 1, "MAX": 2, "SIZE": 2}),
        ("CAP", "{k,3}", {"MIN": 3, "MAX": 3, "SIZE": 1}),
        ("(*)", "{k,3}", {"MIN": 3, "MAX": 3, "SIZE": 1})]:
    operand = f"{reduction}[k IN {{1,2}}] {literal}"
    for operator, value in expected.items():
        check(f"{operator} {operand}", f"{operator} ({operand})",
              f"f(1) == {value}", "true\n", expand=True)
for operator in ["SUM", "PROD"]:
    check(f"{operator}[i IN {{1,2}}] SIZE CUP[k IN {{1,2}}] {{k}}",
          f"{operator}[i IN {{1,2}}] SIZE (CUP[k IN {{1,2}}] {{k}})",
          "f(1) == 4", "true\n", expand=True)
check("MIN CUP[k IN {1,2}] {k} == 1 : o otherwise : !o",
      "(MIN (CUP[k IN {1,2}] {k})) == 1 : o otherwise : !o",
      "f(1)", "o\n", expand=True)
check("X[SIZE CUP[k IN {1,2}] {k}] o", "X[SIZE (CUP[k IN {1,2}] {k})] o",
      "f(1)", expand=True)

# §4.7 range bounds are numerical expressions; §4.6 guards belong only to
# function cases. Check both bounds for every reduction, even in unused f.
# Plain ranges retain their re-emission, basic TLSF and exact LTL output.
for op, operand, query, expected in [
        ("SUM", "i", "bus[f(1)]", "bus_1\n"),
        ("PROD", "(i + 1)", "bus[f(1)]", "bus_2\n"),
        ("&&", "X[i] o", "f(1)", "(o && (X o))\n"),
        ("||", "X[i] o", "f(1)", "(o || (X o))\n"),
        ("CUP", "{i,2}", "bus[SIZE f(1)]", "bus_3\n"),
        ("CAP", "{i,2}", "bus[SIZE f(1)]", "bus_1\n")]:
    for bound in ["true : 0 <= i < 2", "0 <= i < true : 2"]:
        body = f"{op}[{bound}] {operand}"
        for mode in ["parse", "ltl", "basic"]:
            rejected = run(body, "true", mode)
            assert rejected["status"] > 0, (body, mode, rejected)
            assert "parse error:" in rejected["stderr"], (body, mode, rejected)
            counts["guarded range bound rejections"] += 1
    check(f"{op}[0 <= i < 2] {operand}",
          f"{op}[(0) <= i < (2)] ({operand})",
          query, expected, expand=True)
for temporal, operator in [("F", "||"), ("G", "&&")]:
    check(f"{temporal}[0:2] o", f"{temporal}[(0):(2)] (o)", "f(1)",
          f"((o {operator} (X o)) {operator} (X (X o)))\n", expand=True)

# Two possible range-binder identifiers have identical outer case boundaries;
# longest match cannot choose one. Preserve the explicit ambiguity diagnostic.
ambiguous = run("true : SUM[0 < i < 2 < j < 4] i otherwise : 0", "true", "parse")
assert ambiguous["status"] != 0 and "ambiguous function case boundary" in ambiguous["stderr"], ambiguous
counts["ambiguity rejections"] += 1
if args.evidence:
    args.evidence.write_text(json.dumps(dict(counts=counts, differences=differences,
                                             excluded_references=excluded_references,
                                             unexplained=[]), indent=2) + "\n")
print("case boundaries110: " + json.dumps(counts, sort_keys=True))
