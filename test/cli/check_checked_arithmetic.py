"""Issue #115: exact computed domains, six reductions and failure publication."""
import itertools
import subprocess
import sys

ltl, tlsf, norm = sys.argv[1:]
checks = 0
minimum, maximum = -(1 << 63), (1 << 63) - 1


def source(expression, finite):
    # Retain the original input-assumption/output-guarantee orientation.
    return (f"INFO {{ SEMANTICS: {'Finite,' if finite else ''}Mealy TARGET: Mealy }} "
            f"MAIN {{ INPUTS {{ i; }} OUTPUTS {{ o; }} "
            f"ASSUMPTIONS {{ i; }} GUARANTEES {{ {expression}; }} }}")


def run(command, expression, finite, diagnostic=None):
    global checks
    result = subprocess.run(command, input=source(expression, finite),
                            capture_output=True, text=True, timeout=10)
    assert "runtime error:" not in result.stderr, (expression, result)
    if diagnostic:
        assert result.returncode != 0 and diagnostic in result.stderr, (expression, result)
        assert not result.stdout, (expression, result)
    else:
        assert result.returncode == 0 and not result.stderr, (expression, result)
    checks += 1
    return result.stdout


def check(expression, expected, finite, diagnostic=None):
    for command in ([ltl, "--format", "ltl"], [tlsf, "--basic"],
                    [norm, "--pre-passes", "pre-bounded-bool", "--passes", "off"]):
        actual = run(command, expression, finite, diagnostic)
        if not diagnostic:
            assert actual == run(command, expected, finite), (expression, actual)


for finite in (False, True):
    # The issue's exact three small-final-endpoint reproducers, plus div/mod UB
    # and overflowing sum/product prefixes whose final values could otherwise fit.
    for expression, diagnostic in (
            ("&&[0 <= k <= ((9223372036854775807 + 1) / 9223372036854775807)] false",
             "integer addition overflow"),
            ("&&[1 <= k <= ((9223372036854775807 * 2) / 9223372036854775807)] false",
             "integer multiplication overflow"),
            ("&&[0 <= k <= (-(-9223372036854775807 - 1) / 9223372036854775807)] false",
             "integer negation overflow"),
            ("&&[0 <= k <= (-9223372036854775808 / (-1))] false", "integer division overflow"),
            ("&&[0 <= k <= (-9223372036854775808 % (-1))] false", "integer remainder overflow"),
            ("&&[0 <= k <= (1 / 0)] false", "division by zero"),
            ("&&[0 <= k <= (1 % 0)] false", "division by zero"),
            ("&&[0 <= k <= (-9223372036854775808 - 1)] false", "integer subtraction overflow"),
            ("&&[0 <= k <= (+[j IN {9223372036854775807, 1, -1}] j)] false", "integer sum overflow"),
            ("&&[0 <= k <= (*[j IN {9223372036854775807, 2, 0}] j)] false", "integer product overflow"),
            ("&&[(9223372036854775807 + 1) <= k <= 0] false", "integer addition overflow"),
            ("&&[9223372036854775807 < k <= (9223372036854775807 + 1)] false",
             "integer addition overflow")):
        check(expression, None, finite, diagnostic)

    # All four strictness combinations over computed endpoints, reversed bounds,
    # and both extremes. Python integers supply the independent domain oracle.
    for lo, hi, lo_value, hi_value in (
            ("(+[0 <= j <= 1] j)", "(*[1 <= j <= 2] j)", 1, 2),
            ("(*[1 <= j <= 2] j)", "(+[0 <= j <= 1] j)", 2, 1),
            ("(-9223372036854775807 - 1)", "(-9223372036854775808 + 2)", minimum, minimum + 2),
            ("(9223372036854775807 - 2)", "(9223372036854775807 * 1)", maximum - 2, maximum),
            ("(+[0 <= j <= 0] -9223372036854775808)", "(-9223372036854775808 * 1)", minimum, minimum),
            ("(9223372036854775807 + 0)", "(*[0 <= j <= 0] 9223372036854775807)", maximum, maximum)):
        for ls, us in itertools.product((False, True), repeat=2):
            bound = f"{lo} {'<' if ls else '<='} k {'<' if us else '<='} {hi}"
            values = list(range(lo_value + ls, hi_value - us + 1))
            count = len(values)
            intersection = set.intersection(*(set((k, 0)) for k in values)) if values else None
            for expression, expected, diagnostic in (
                    (f"&&[{bound}] o", " && ".join(["o"] * count) or "true", None),
                    (f"||[{bound}] o", " || ".join(["o"] * count) or "false", None),
                    (f"(+[{bound}] 1) == {count}", "true", None),
                    (f"(*[{bound}] 2) == {2 ** count}", "true", None),
                    (f"SIZE ((+)[{bound}] {{k}}) == {count}", "true", None),
                    (f"SIZE ((*)[{bound}] {{k, 0}}) == {len(intersection or ())}", "true",
                     None if count else "intersection over an empty domain")):
                check(expression, expected, finite, diagnostic)

print(f"checked arithmetic CLI: {checks} checks passed")
