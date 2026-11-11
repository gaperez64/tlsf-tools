"""Issue #114: compare every reduction with the mathematical range domain."""
import itertools
import json
from pathlib import Path
import subprocess
import sys

ltl, tlsf, norm, fixture = sys.argv[1:]
minimum, maximum = -(1 << 63), (1 << 63) - 1
checks = 0


def integer(value):
    return "(-9223372036854775807 - 1)" if value == minimum else str(value)


def source(expression, finite, declarations=""):
    return (f"INFO {{ SEMANTICS: {'Finite,' if finite else ''}Mealy TARGET: Mealy }} "
            f"MAIN {{ OUTPUTS {{ {declarations} }} GUARANTEES {{ {expression}; }} }}")


def run(command, text):
    return subprocess.run(command, input=text, capture_output=True, text=True, timeout=10)


def check(expression, expected, finite, diagnostic=None, declarations=""):
    global checks
    text = source(expression, finite, declarations)
    for command in ([ltl, "--format", "ltl"], [tlsf, "--basic"]):
        result = run(command, text)
        if diagnostic:
            assert result.returncode != 0 and diagnostic in result.stderr, (expression, result)
            assert not result.stdout, (expression, result)
        else:
            control = run(command, source(expected, finite))
            assert result.returncode == control.returncode == 0, (expression, result, control)
            assert result.stdout == control.stdout, (expression, result, control)
        checks += 1


for lo, hi in json.loads(Path(fixture).read_text()):
    for lower_strict, upper_strict, finite in itertools.product((False, True), repeat=3):
        bound = (f"{integer(lo)} {'<' if lower_strict else '<='} k "
                 f"{'<' if upper_strict else '<='} {integer(hi)}")
        # Python integers do not overflow at the machine endpoints.
        values = list(range(lo + lower_strict, hi - upper_strict + 1))
        count = len(values)
        conjunction = " && ".join(["false"] * count) or "true"
        disjunction = " || ".join(["true"] * count) or "false"
        intersection = set.intersection(*(set((value, 0)) for value in values)) if values else None
        for expression, expected, diagnostic in [
                (f"&&[{bound}] false", conjunction, None),
                (f"||[{bound}] true", disjunction, None),
                (f"(+[{bound}] 1) == {count}", "true", None),
                (f"(*[{bound}] 2) == {2 ** count}", "true", None),
                (f"SIZE ((+)[{bound}] {{k}}) == {count}", "true", None),
                (f"SIZE ((*)[{bound}] {{k, 0}}) == {len(intersection or ())}", "true",
                 None if count else "intersection over an empty domain")]:
            check(expression, expected, finite, diagnostic)

        # Exercise the other strict-bound conversion in the pre-expansion pass.
        for operator, expected in (("&&", conjunction), ("||", disjunction)):
            body = "false" if operator == "&&" else "true"
            result = run([norm, "--pre-passes", "pre-bounded-bool", "--passes", "off"],
                         source(f"{operator}[{bound}] {body}", finite))
            assert result.returncode == 0, result
            lowered = run([ltl, "--format", "ltl"], result.stdout)
            assert lowered.returncode == 0 and lowered.stdout == expected + "\n", lowered
            checks += 1

# Stepped set ranges: safe increments at both endpoints, and an unrepresentable
# stride must fail before subtraction instead of wrapping its direction.
for finite in (False, True):
    for expression in (
            "SIZE {9223372036854775806, 9223372036854775807 .. 9223372036854775807} == 2",
            "SIZE {(-9223372036854775807), (-9223372036854775807 - 1) .. (-9223372036854775807 - 1)} == 2",
            "SIZE {0, (-9223372036854775807 - 1) .. (-9223372036854775807 - 1)} == 2"):
        check(expression, "true", finite)
    for first, second in ((minimum, maximum), (maximum, minimum)):
        check(f"SIZE {{{integer(first)}, {integer(second)} .. {integer(second)}}} == 2",
              "true", finite, "step overflow in set range")
    for operator, expected in (("G", "true"), ("F", "false")):
        check(f"{operator}[1:0] false", expected, finite)
        check(f"{operator}[0:1] true", "true && X true" if operator == "G" else "true || X true", finite)
        check(f"{operator}[-1:0] true", "true", finite, "negative bound")
    check("X[0] true", "true", finite)
    check("X[-1] true", "true", finite, "negative count")
    for lo, hi in ((minimum, minimum), (maximum, maximum), (1, 0)):
        check("true", "true", finite, "bus", f"b[{integer(lo)}..{integer(hi)}];")
    for width in (minimum, maximum, -1, 0):
        check("true", "true", finite,
              "subtraction overflow" if width == minimum else "bus",
              f"b[{integer(width)}];")

print(f"strict bounds: {checks} converter/normalizer checks passed")
