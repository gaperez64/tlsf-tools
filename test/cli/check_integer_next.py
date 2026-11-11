"""Issues #115-117: checked integers and strength-preserving next chains."""
import json
from pathlib import Path
import subprocess
import sys

ltl, tlsf, norm, fixtures = sys.argv[1:]
fixtures = Path(fixtures)
checks = 0


def source(expression, finite):
    return (f"INFO {{ SEMANTICS: {'Finite,' if finite else ''}Mealy TARGET: Mealy }} "
            f"MAIN {{ GUARANTEES {{ {expression}; }} }}")


def run(command, text, diagnostic=None):
    global checks
    result = subprocess.run(command, input=text, capture_output=True, text=True, timeout=10)
    assert "runtime error:" not in result.stderr, (command, text, result)
    if diagnostic:
        assert result.returncode != 0 and diagnostic in result.stderr, (command, text, result)
        assert not result.stdout, (command, text, result)
    else:
        assert result.returncode == 0, (command, text, result)
    checks += 1
    return result.stdout


for expression, expected, diagnostic in json.loads((fixtures / "checked_integer.json").read_text()):
    for finite in (False, True):
        text = source(expression, finite)
        for command in ([ltl, "--format", "ltl"], [tlsf, "--basic"],
                        [norm, "--pre-passes", "pre-indexed-x", "--passes", "off"]):
            output = run(command, text, diagnostic)
            if not diagnostic:
                assert output == run(command, source(expected, finite)), (expression, output)
        if diagnostic == "integer literal out of range":
            run([tlsf], text, diagnostic)
        elif not diagnostic:
            # Reprinting INT64_MIN must also produce parseable TLSF.
            output = run([tlsf], text)
            assert run([ltl, "--format", "ltl"], output) == expected + "\n", expression

for expression, golden in json.loads((fixtures / "indexed_next.json").read_text()):
    for finite in (False, True):
        for body in ("true", "false"):
            text = source(expression.replace("true", body), finite)
            diagnostic = "only valid under finite semantics" if "!" in expression and not finite else None
            direct = run([ltl, "--format", "ltl"], text, diagnostic)
            basic = run([tlsf, "--basic"], text, diagnostic)
            normalized = run([norm, "--pre-passes", "pre-indexed-x", "--passes", "off"],
                             text, diagnostic)
            if not diagnostic:
                expected = golden.replace("true", body) + "\n"
                assert direct == expected, (expression, direct, expected)
                assert run([ltl, "--format", "ltl"], basic) == expected, expression
                assert run([ltl, "--format", "ltl"], normalized) == expected, expression

print(f"checked integers and next strengths: {checks} converter/normalizer checks passed")
