"""Jacobs/Klein/Schirmer, TLSF v1.1 Table 1 (paper p.118).

Compare fully printed parse trees with explicit correct AND incorrect readings.
Some adjacent levels have incompatible operand types; those use unexpanded
TLSF, while well-typed witnesses also run through both expansion CLIs.
"""
import os
import re
import subprocess
import sys

ltl, tlsf = sys.argv[1:]
checks = 0
failures = []
ALIASES = {
    "MUL": "*", "DIV": "/", "MOD": "%", "PLUS": "+", "MINUS": "-",
    "CAP": "(*)", "CUP": "(+)", "SETMINUS": "(-)", "(\\)": "(-)",
    "EQ": "==", "NEQ": "!=", "/=": "!=", "LE": "<", "LEQ": "<=",
    "GE": ">", "GEG": ">=", "ELEM": "IN", "<-": "IN", "NOT": "!",
    "AND": "&&", "OR": "||", "FORALL": "&&", "EXISTS": "||",
    "IMPLIES": "->", "EQUIV": "<->", "SUM": "+", "PROD": "*",
}


def canonical(expression):
    return re.sub(r"[A-Z]+|/\=|<-(?!>)|\(\\\)",
                  lambda match: ALIASES.get(match[0], match[0]), expression)


def source(body, definitions=""):
    return ("INFO { SEMANTICS: Finite,Mealy TARGET: Mealy } "
            f"GLOBAL {{ DEFINITIONS {{ {definitions} }} }} "
            f"MAIN {{ OUTPUTS {{ a; b; c; o; bus[3]; }} GUARANTEE {{ {body}; }} }}")


def run(text, mode):
    command = ([ltl, "--format", "ltl", "--parenthesize"] if mode == "ltl"
               else [tlsf, *(["--basic"] if mode == "basic" else [])])
    return subprocess.run(command, input=text, capture_output=True, text=True,
                          timeout=17, env=os.environ)


def check(label, expression, correct, wrong, expand=False, definitions="", parse=True):
    global checks
    for mode in ((["parse"] if parse else []) + (["ltl", "basic"] if expand else [])):
        checks += 1
        actual, expected, other = [run(source(e, definitions), mode)
                                   for e in (expression, canonical(correct), canonical(wrong))]
        if (actual.returncode or expected.returncode or
                actual.stdout != expected.stdout or
                (other.returncode == 0 and other.stdout == expected.stdout)):
            failures.append((label, mode, expression, actual.returncode,
                             actual.stdout, actual.stderr, expected.stdout,
                             other.returncode, other.stdout, other.stderr))


# Every binary row, including mixed operators within shared rows. Associative
# operators still need tree checks: expansion may preserve equivalent trees.
for row, operators, right in [
        (2, ["*", "MUL"], False),
        (3, ["/", "DIV", "%", "MOD"], True),
        (4, ["+", "PLUS", "-", "MINUS"], False),
        (6, ["(\\)", "(-)", "SETMINUS"], True),
        (7, ["(*)", "CAP"], False), (8, ["(+)", "CUP"], False),
        (9, ["==", "EQ", "!=", "/=", "NEQ", "<", "LE", "<=", "LEQ",
             ">", "GE", ">=", "GEG"], False),
        (10, ["IN", "ELEM", "<-"], False),
        (12, ["&&", "AND"], False), (13, ["||", "OR"], False),
        (14, ["->", "IMPLIES", "<->", "EQUIV"], True),
        (15, ["W"], True), (16, ["U"], True), (17, ["R"], False),
        (18, ["~"], False), (19, [":"], False)]:
    for first in operators:
        for second in operators:
            left = f"(a {first} b) {second} c"
            rhs = f"a {first} (b {second} c)"
            check(f"row {row} associativity {first}/{second}",
                  f"a {first} b {second} c", rhs if right else left,
                  left if right else rhs, expand=12 <= row <= 17)

# Unary rows 1, 5, 11: the operand ends before the next weaker operator.
for op in ["+[k IN {1,2}]", "SUM[k IN {1,2}]",
           "*[k IN {1,2}]", "PROD[k IN {1,2}]"]:
    check("row 1 reduction", f"{op} k * 3", f"({op} k) * 3",
          f"{op} (k * 3)")
for op in ["SIZE", "MIN", "MAX"]:
    check("row 1 " + op, f"{op} a * b", f"({op} a) * b", f"{op} (a * b)")
check("row 1 bars", "|a| * b", "(|a|) * b", "SIZE (a * b)")
check("row 1 SIZEOF", "SIZEOF bus * 2 == 6", "(SIZEOF bus) * 2 == 6",
      "SIZEOF bus * 2 == 3", True)
for op in ["(*)", "CAP", "(+)", "CUP"]:
    check("row 5 " + op, f"{op}[k IN {{1}}] a (-) b",
          f"({op}[k IN {{1}}] a) (-) b", f"{op}[k IN {{1}}] (a (-) b)")
for op in ["!", "NOT", "X", "F", "G", "&&[k IN {1}]",
           "AND[k IN {1}]", "FORALL[k IN {1}]", "||[k IN {1}]",
           "OR[k IN {1}]", "EXISTS[k IN {1}]"]:
    check("row 11 " + op, f"{op} a && b", f"({op} a) && b", f"{op} (a && b)", expand=op in ("!", "NOT", "X", "F", "G"))

# Every adjacent pair, both operand orders where both rows are binary.
boundaries = [
    (1, "SUM[k IN {1}] a * b", "(SUM[k IN {1}] a) * b", "SUM[k IN {1}] (a * b)"),
    (2, "a / b * c", "a / (b * c)", "(a / b) * c"),
    (3, "a + b / c", "a + (b / c)", "(a + b) / c"),
    (4, "CAP[k IN {1}] a + b", "CAP[k IN {1}] (a + b)", "(CAP[k IN {1}] a) + b"),
    (5, "CAP[k IN {1}] a (-) b", "(CAP[k IN {1}] a) (-) b", "CAP[k IN {1}] (a (-) b)"),
    (6, "a (*) b (-) c", "a (*) (b (-) c)", "(a (*) b) (-) c"),
    (7, "a (+) b (*) c", "a (+) (b (*) c)", "(a (+) b) (*) c"),
    (8, "a == b (+) c", "a == (b (+) c)", "(a == b) (+) c"),
    (9, "a IN b == c", "a IN (b == c)", "(a IN b) == c"),
    (10, "!a IN b", "!(a IN b)", "(!a) IN b"),
    (11, "!a && b", "(!a) && b", "!(a && b)"),
    (12, "a || b && c", "a || (b && c)", "(a || b) && c"),
    (13, "a -> b || c", "a -> (b || c)", "(a -> b) || c"),
    (14, "a W b -> c", "a W (b -> c)", "(a W b) -> c"),
    (15, "a U b W c", "a U (b W c)", "(a U b) W c"),
    (16, "a R b U c", "a R (b U c)", "(a R b) U c"),
    (17, "a ~ b R c", "a ~ (b R c)", "(a ~ b) R c"),
    (18, "a ~ b : c", "(a ~ b) : c", "a ~ (b : c)"),
]
for row, expression, correct, wrong in boundaries:
    check(f"boundary {row}/{row + 1}", expression, correct, wrong,
          expand=11 <= row <= 16)
for row, tight, loose in [(2, "*", "/"), (3, "/", "+"), (6, "(-)", "(*)"),
                          (7, "(*)", "(+)"), (8, "(+)", "=="), (9, "==", "IN"),
                          (12, "&&", "||"), (13, "||", "->"), (14, "->", "W"),
                          (15, "W", "U"), (16, "U", "R"), (17, "R", "~")]:
    check(f"boundary {row}/{row + 1} reverse", f"a {tight} b {loose} c",
          f"(a {tight} b) {loose} c", f"a {tight} (b {loose} c)")

# Observable numeric witnesses and the original guard regression.
for expression, correct, wrong in [
        ("24 / 2 * 3 == 4", "24 / (2 * 3) == 4", "(24 / 2) * 3 == 4"),
        ("24 / 6 / 2 == 8", "24 / (6 / 2) == 8", "(24 / 6) / 2 == 8"),
        ("20 % 6 % 4 == 0", "20 % (6 % 4) == 0", "(20 % 6) % 4 == 0"),
        ("10 - 3 - 2 == 5", "(10 - 3) - 2 == 5", "10 - (3 - 2) == 5"),
        ("SIZE ({1,2} (-) {2} (-) {2}) == 1", "SIZE ({1,2} (-) ({2} (-) {2})) == 1",
         "SIZE (({1,2} (-) {2}) (-) {2}) == 1"),
        ("SUM[k IN {1,2}] k + 3 == 6", "(SUM[k IN {1,2}] k) + 3 == 6",
         "SUM[k IN {1,2}] (k + 3) == 6")]:
    check("numeric expansion", expression, correct, wrong, True)
for n, expected in [(0, "o"), (1, "!o"), (2, "o")]:
    check(f"guard f({n})", f"f({n})", expected,
          "!o" if expected == "o" else "o", True,
          "f(n) = n == 0 || n == 2 : o otherwise : !o;", parse=False)

for expression, correct, wrong in [
        ("SIZE ({1,2} (-) {1} (*) {1}) == 0",
         "SIZE (({1,2} (-) {1}) (*) {1}) == 0",
         "SIZE ({1,2} (-) ({1} (*) {1})) == 0"),
        ("SIZE ({1} (+) {2} (*) {2}) == 2",
         "SIZE ({1} (+) ({2} (*) {2})) == 2",
         "SIZE (({1} (+) {2}) (*) {2}) == 2"),
        ("true IN {true} IN {true}", "(true IN {true}) IN {true}",
         "true IN ({true} IN {true})")]:
    check("set expansion", expression, correct, wrong, True)
check("pattern/release boundary", "pick(a R b)", "a", "false", True,
      "pick(x) = x ~ p R q : p otherwise : false;", parse=False)

# Case-list boundaries must not split a function call into a final bare value.
check("guard chain with call", "f(1)", "o && true", "o || true", True,
      "f(n) = n == 0 : true otherwise : o && f(n - 1);", parse=False)
check("guard chain first match", "f(1)", "X o", "!o", True,
      "delay(n) = X[n] o; f(n) = n == 0 || n == 1 : delay(n) "
      "n == 1 : !o otherwise : o;", parse=False)
check("extension unary minus", "-3 * 2 == -6", "(-3) * 2 == (-6)",
      "-(3 * 2) == 6", True)

# Extensions retain row-11 binding. M is an LTL-text operator, not TLSF syntax.
for op in ["X[2]", "X[!2]", "X[2!]", "X[!]", "F[1:2]", "G[1:2]",
           "F[!1:2]", "G[!1:2]", "F[1:2!]", "G[1:2!]"]:
    check("extension " + op, f"{op} a && b", f"({op} a) && b", f"{op} (a && b)", True)

for failure in failures:
    print(repr(failure), file=sys.stderr)
print(f"precedence110: {checks} checks, {len(failures)} failures")
assert not failures
