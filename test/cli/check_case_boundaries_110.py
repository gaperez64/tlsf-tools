"""Pin main's reading of TLSF §4.6's unseparated function cases.

The normal test compares against explicit boundaries and observable results.
Pass --main-bin to also compare every regression with the frozen main CLIs.
All inputs use stdin so the impact measurement's TLSF input set stays fixed.
"""
import argparse
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("ltl")
parser.add_argument("tlsf")
parser.add_argument("--main-bin", type=Path)
args = parser.parse_args()
checks = 0
comparisons = 0


def source(definitions, body):
    return ("INFO { SEMANTICS: Finite,Mealy TARGET: Mealy } "
            f"GLOBAL {{ DEFINITIONS {{ {definitions} }} }} "
            f"MAIN {{ OUTPUTS {{ o; bus[3]; }} GUARANTEE {{ {body}; }} }}")


def run(text, mode, baseline=False):
    binary = args.ltl if mode == "ltl" else args.tlsf
    env = dict(os.environ)
    if baseline:
        binary = str(args.main_bin / ("tlsf2ltl-main" if mode == "ltl"
                                     else "tlsf2tlsf-main"))
        env["LD_LIBRARY_PATH"] = str(args.main_bin.resolve())
    flags = (["--format", "ltl", "--parenthesize"] if mode == "ltl"
             else ["--basic"] if mode == "basic" else [])
    result = subprocess.run([binary, *flags], input=text, text=True,
                            capture_output=True, env=env, timeout=17)
    assert result.returncode == 0, (mode, text, result.stderr)
    return result.stdout


def check(label, definitions, explicit, body="f(1)", expected="(!o)\n",
          expand=True, compare_main=True, control_body=None):
    global checks, comparisons
    for mode in ["parse", *(["ltl", "basic"] if expand else [])]:
        actual = run(source(definitions, body), mode)
        control = run(source(explicit, control_body or body), mode)
        assert actual == control, (label, mode, actual, control)
        if mode == "ltl":
            assert actual == expected, (label, actual, expected)
        checks += 1
        if args.main_bin and compare_main:
            baseline = run(source(definitions, body), mode, baseline=True)
            assert actual == baseline, (label, mode, actual, baseline)
            comparisons += 1


# Every expression-start token in tlsf.y, with aliases and bounded extensions.
# Only -, +[, *[, &&[, ||[, CUP[ and CAP[ also continue expressions;
# '(' additionally continues a bare identifier as a call. The others check
# that finishing a value still starts the next case without swallowing it.
guards = [
    "-n < 0", "MINUS n < 0", "(n) == 1", "(-n) < 0", "(n + 0) == 1",
    "!o ~ !p", "NOT o ~ !p", "|{1}| == 1",
    "SIZE {1} == 1", "MIN {1} == 1", "MAX {1} == 1", "SIZEOF bus == 3",
    "X o ~ X p", "F o ~ F p", "G o ~ G p", "X[1] o ~ X p",
    "X[!] o ~ X[!] p", "X[!1] o ~ p", "X[1!] o ~ p",
    "F[1:2] o ~ p", "G[1:2] o ~ p", "F[!1:2] o ~ p", "G[!1:2] o ~ p",
    "F[1:2!] o ~ p", "G[1:2!] o ~ p", "id(n) == 1", "n == 1",
    "1 == 1", "true ~ p", "false ~ p", "bus[0] ~ p",
]
for op in ["&&", "AND", "FORALL", "||", "OR", "EXISTS"]:
    guards.append(f"{op}[k IN {{1}}] o ~ p")
for op in ["&&", "||"]:
    guards.append(f"{op}[0 <= k < 2] o ~ p")
for guard in guards:
    for tail in ["otherwise : o", ""]:
        check(guard + " tail=" + tail,
              f"id(x) = x; f(n) = n == 0 : o {guard} : !o {tail};",
              f"id(x) = x; f(n) = n == 0 : (o) ({guard}) : !o {tail};")

# Main's sets and numeric/set reductions are syntactically valid pattern operands,
# but its expander cannot match them as formulas. Raw trees distinguish the
# case boundary without depending on those unrelated expansion limitations.
raw_guards = ["{1} ~ p"]
for op, operand in [(op, "k") for op in ["+", "PLUS", "SUM", "*", "MUL", "PROD"]] + [
        (op, "{k}") for op in ["(+)", "CUP", "(*)", "CAP"]]:
    raw_guards.append(f"{op}[k IN {{1}}] {operand} ~ p")
for guard in raw_guards:
    for tail in ["otherwise : o", ""]:
        check(guard + " tail=" + tail,
              f"f(n) = n == 0 : o {guard} : !o {tail};",
              f"f(n) = n == 0 : (o) ({guard}) : !o {tail};", expand=False)

check("review minus", "f(n) = n == 0 : 0 -n < 0 : 1 otherwise : 2;",
      "f(n) = n == 0 : (0) (-n < 0) : 1 otherwise : 2;",
      body="f(1) == 1", expected="true\n")
check("constant minus", "f = 1 == 0 : 0 -1 < 0 : 1;",
      "f = 1 == 0 : (0) (-1 < 0) : 1;", body="f == 1", expected="true\n")
check("constant call boundary", "f = 1 == 0 : o (1) == 1 : !o;",
      "f = 1 == 0 : (o) ((1) == 1) : !o;", body="f")

# Review110k: two complete partitions survive Table 1's tighter reduction.
# Main shifts '-' into the value and leaves '(n) < 0' as the next guard.
# Its raw reduction tree differs *inside* that value, so compare the boundary
# to an explicit Table 1 tree and expanded outputs to main independently.
for op in ["SUM", "PROD", "+", "*", "PLUS", "MUL"]:
    definitions = (f"id = 0; f(n) = n == 0 : {op}[k IN {{1}}] k "
                   "-id(n) < 0 : 1 otherwise : 2;")
    explicit = (f"id = 0; f(n) = n == 0 : ({op}[k IN {{1}}] k - id) "
                "((n) < 0) : 1 otherwise : 2;")
    check("reduction/minus/call " + op, definitions, explicit,
          body="f(1) == 2", expected="true\n", compare_main=False)
    if args.main_bin:
        for mode in ["ltl", "basic"]:
            text = source(definitions, "f(1) == 2")
            assert run(text, mode) == run(text, mode, baseline=True), op
            comparisons += 1

# The pre-pass records later boundaries too, using token positions across
# lines/comments. Delimit the first boundary so only the second is ambiguous.
check("later reduction boundary across lines",
      "id = 0; f(n) = n == 0 : (0) (n) == 2 :\n"
      " SUM[k IN {1}] k /* boundary alternatives */ -id\n"
      " (n) < 0 : 1 otherwise : 2;",
      "id = 0; f(n) = n == 0 : (0) (n) == 2 :\n"
      " (SUM[k IN {1}] k - id) ((n) < 0) : 1 otherwise : 2;",
      body="f(1) == 2", expected="true\n", compare_main=False)

# Boundary selection must not restore main's low reduction precedence inside
# the selected value: (1 + 2) - 2 = 1, whereas SUM[k IN {1,2}] (k - 2) = -1.
check("selected value keeps Table 1",
      "id = 2; f(n) = n == 0 : SUM[k IN {1,2}] k -id(n) < 0 : 1 otherwise : 2;",
      "id = 2; f(n) = n == 0 : ((SUM[k IN {1,2}] k) - id) "
      "((n) < 0) : 1 otherwise : 2;",
      body="f(0) == 1", expected="true\n", compare_main=False)

# Length alone could swallow the comparison and callee into the value, leaving
# the call's argument as a general boolean guard. Main's cond cannot do that.
# Comparisons inside any delimiters also cannot supply main's outer cmp_op.
for argument in ["true", "(true)", "1 == 1", "|{1}| == 1", "id(true)"]:
    check("comparison before call " + argument,
          "z = 0; zero(x) = 0; id(x) = x; "
          f"f(n) = n == 0 : 0 -z == zero({argument}) : 1 otherwise : 2;",
          "z = 0; zero(x) = 0; id(x) = x; "
          f"f(n) = n == 0 : (0) (-z == zero({argument})) : 1 otherwise : 2;",
          body="f(1) == 1", expected="true\n")

# Main's value grammar also excludes an outer pattern match. Pin its partition
# as raw syntax; conformance typing rejects this pattern before expansion.
check("outer match remains in the guard",
      "zero(x) = 0; f(n) = n == 0 : o (o) ~ zero(true) == 0 : !o otherwise : o;",
      "zero(x) = 0; f(n) = n == 0 : (o) ((o) ~ zero(true) == 0) : !o otherwise : o;",
      expand=False)

# The reference pass handles each definition independently: an earlier general
# boolean guard unsupported by main must not disable selection for later f.
check("reference rejection is local to one definition",
      "id = 0; g(n) = true : 1 otherwise : 2; "
      "f(n) = n == 0 : SUM[k IN {1}] k -id(n) < 0 : 1 otherwise : 2;",
      "id = 0; g(n) = true : 1 otherwise : 2; "
      "f(n) = n == 0 : (SUM[k IN {1}] k - id) ((n) < 0) : 1 otherwise : 2;",
      body="f(1) == 2", expected="true\n", compare_main=False)

# Repeated boundaries must work beyond the two/three-case examples too.
check("four cases", "f(n) = n == 0 : o (n) == 2 : o -n < 0 : !o otherwise : o;",
      "f(n) = n == 0 : (o) ((n) == 2) : (o) (-n < 0) : !o otherwise : o;")
check("repeated calls", "f(n) = n == 0 : o (n) == 2 : o (n) == 1 : !o otherwise : o;",
      "f(n) = n == 0 : (o) ((n) == 2) : (o) ((n) == 1) : !o otherwise : o;")
check("repeated calls without otherwise",
      "f(n) = n == 0 : o (n) == 2 : o (n) == 1 : !o;",
      "f(n) = n == 0 : (o) ((n) == 2) : (o) ((n) == 1) : !o;")
for value in ["!o", "X o", "o && o", "o || o", "o -> o", "o U o"]:
    check("compound value " + value,
          f"f(n) = n == 0 : {value} (n) == 1 : !o otherwise : o;",
          f"f(n) = n == 0 : ({value}) ((n) == 1) : !o otherwise : o;")
for value in ["1 + 2", "1 * 2"]:
    check("compound numeric value " + value,
          f"f(n) = n == 0 : {value} -n < 0 : 1 otherwise : 2;",
          f"f(n) = n == 0 : ({value}) (-n < 0) : 1 otherwise : 2;",
          body="f(1) == 1", expected="true\n")

# A continuation which cannot form another guarded case stays in the value.
# Binary minus in guards and values keeps Table 1 level 4 and left association.
for body, expected in [("f(0) == 5", "true\n"), ("f(2) == 3", "true\n")]:
    check("binary minus " + body,
          "f(n) = n - 1 - 1 < 0 : 10 - 3 - 2 otherwise : 9 - 4 - 2;",
          "f(n) = ((n - 1) - 1) < 0 : ((10 - 3) - 2) otherwise : ((9 - 4) - 2);",
          body=body, expected=expected)
check("call in value", "id(x) = x; f(n) = n == 0 : id(o) otherwise : id(!o);",
      "id(x) = x; f(n) = n == 0 : (id(o)) otherwise : (id(!o));")

# The case/colon separation must also preserve Table 1's nested guard bounds.
# Main lacks general ':' expressions, so these compare explicit Table 1 trees.
for op in ["F", "G"]:
    for opening, closing in [("[", "]"), ("[!", "]"), ("[", "!]")]:
        next_op = "X" if opening == "[" and closing == "]" else "X[!]"
        connective = "||" if op == "F" else "&&"
        check("nested range " + op + opening + closing, "", "",
              body=f"{op}{opening}true:1:2{closing} o",
              control_body=f"{op}{opening}(true:1):2{closing} o",
              expected=f"(({next_op} o) {connective} ({next_op} ({next_op} o)))\n",
              compare_main=False)

print(f"case boundaries110: {checks} checks, {comparisons} comparisons with main")
