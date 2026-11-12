"""Issue #116: source literal boundaries and range formula denotations."""
import subprocess
import sys

ltl, tlsf, norm = sys.argv[1:]
checks = 0


def source(expression, finite):
    return (f"INFO {{ SEMANTICS: {'Finite,' if finite else ''}Mealy TARGET: Mealy }} "
            f"MAIN {{ GUARANTEES {{ {expression}; }} }}")


def run(command, text, diagnostic=None):
    global checks
    result = subprocess.run(command, input=text, capture_output=True, text=True, timeout=10)
    if diagnostic:
        assert result.returncode != 0 and diagnostic in result.stderr, (text, result)
        assert not result.stdout, (text, result)
    else:
        assert result.returncode == 0 and not result.stderr, (text, result)
    checks += 1
    return result.stdout


for finite in (False, True):
    for minimum in ("-9223372036854775808", "-0009223372036854775808",
                    "- /* gap */ 9223372036854775808", "(-9223372036854775807 - 1)"):
        for bound in (f"{minimum} < k <= -9223372036854775807",
                      f"{minimum} <= k < -9223372036854775807",
                      f"{minimum} <= k <= {minimum}"):
            for reduction, body, expected in (("&&", "false", "false"),
                                               ("||", "true", "true")):
                text = source(f"{reduction}[{bound}] {body}", finite)
                assert run([ltl, "--format", "ltl"], text) == expected + "\n"
                for command in ([tlsf, "--basic"],
                                [norm, "--pre-passes", "pre-bounded-bool", "--passes", "off"]):
                    lowered = run(command, text)
                    assert run([ltl, "--format", "ltl"], lowered) == expected + "\n"
                printed = run([tlsf], text)
                assert run([ltl, "--format", "ltl"], printed) == expected + "\n"

    for spelling, diagnostic in (
            ("9223372036854775808", "integer literal out of range"),
            ("0009223372036854775808", "integer literal out of range"),
            ("-(9223372036854775808)", "integer literal out of range"),
            ("9223372036854775809", "integer literal out of range"),
            ("-9223372036854775809", "integer literal out of range"),
            ("18446744073709551616", "integer literal out of range"),
            ("-18446744073709551616", "integer literal out of range"),
            ("-(-9223372036854775808)", "integer negation overflow")):
        text = source(f"&&[{spelling} <= k <= 0] false", finite)
        for command in ([ltl, "--format", "ltl"], [tlsf, "--basic"],
                        [norm, "--pre-passes", "pre-bounded-bool", "--passes", "off"]):
            run(command, text, diagnostic)

print(f"integer literal CLI: {checks} checks passed")
