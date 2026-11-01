"""Golden verdicts and exported objectives for exact decomposition."""
from pathlib import Path
import subprocess
import sys
import tempfile
import re

from golden import Golden

convert, residual, compose, phase_b_probe, cases = sys.argv[1:]
gold = Golden("decomposition")
INFINITE, FINITE = False, True


def output(tool, fixture):
    return subprocess.check_output([tool, str(fixture)], text=True, timeout=5)


def realizable(solver, formula, outputs, expected, inputs="q"):
    assert gold.verdict(formula.strip(), inputs, outputs, finite=solver) == expected
    if not solver:
        # Supported infinite objectives also exercise the native reduction
        # and solver against the independently pinned winner.
        build = Path(compose).resolve().parent
        conjunctions = re.sub(r"(?<!&)&(?!&)", "&&", formula)
        body = re.sub(r"(?<!\|)\|(?!\|)", "||", conjunctions)
        declarations = lambda names: ";".join(filter(None, names.split(","))) + (";" if names else "")
        source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { " +
                  declarations(inputs) + " } OUTPUTS { " + declarations(outputs) +
                  " } GUARANTEES { " + body + "; } }")
        with tempfile.TemporaryDirectory(dir=build) as temp:
            path = Path(temp) / "spec.tlsf"
            path.write_text(source)
            prefix = Path(temp) / "game"
            reduced = subprocess.run([str(build / "test/api/native_reduction"), str(path), "exact", str(prefix)],
                                     text=True, capture_output=True, timeout=60)
            assert reduced.returncode in (0, 2, 3), reduced.stderr
            gold.check("native-admission", reduced.returncode)
            if reduced.returncode == 0:
                result = subprocess.run([str(build / "tlsfsolve"), "--game-profile=gr1", str(prefix) + ".aag"],
                                        text=True, capture_output=True, timeout=60)
                assert result.returncode == (0 if expected else 1), result.stderr



for name, outputs, expected in (("definition-future", "p", False),
                                ("definition-preset", "p", True),
                                ("definition-strict-assert", "p", True),
                                ("finite-cluster-end", "p,r", False)):
    fixture = Path(cases) / (name + ".tlsf")
    solver = FINITE if name == "finite-cluster-end" else INFINITE
    realizable(solver, output(convert, fixture), outputs, expected)
    for tool in (residual, compose):
        text = output(tool, fixture)
        formulas = [line for line in text.splitlines()
                    if not line.startswith(("c ", "ctl "))]
        assert len(formulas) == 1, text
        realizable(solver, formulas[0], outputs, expected)

# Review findings 1–4 used to change the winner. Check the actual emitted
# residual with its reduced output alphabet, as well as the expanded original.
for name, original_outputs, residual_outputs, inputs, expected, finite in (
        ("definition-register-use", "p,r", "r", "q", False, False),
        ("invariant-assumption", "p", "p", "", True, False),
        ("delayed-definition-finite", "p", "p", "", False, True),
        ("target-moore-mealy", "p", "p", "q", False, False)):
    fixture = Path(cases) / (name + ".tlsf")
    solver = FINITE if finite else INFINITE
    realizable(solver, output(convert, fixture), original_outputs, expected, inputs)
    for tool in (residual, compose):
        text = output(tool, fixture)
        formulas = [line for line in text.splitlines()
                    if not line.startswith(("c ", "ctl "))]
        assert len(formulas) == 1, text
        realizable(solver, formulas[0], residual_outputs, expected, inputs)

# Each controller can choose a suitable ending alone. No shared ending can
# satisfy both: the first requires length one, the second length at least two.
realizable(FINITE, "p & !X[!]1", "p", True)
realizable(FINITE, "r & X[!]1", "r", True)
realizable(FINITE, "p & !X[!]1 & r & X[!]1", "p,r", False)

# Review 2: the infinite-word delay transform changes finite winners in both
# directions. The tools now refuse these timing changes (CLI guard tests).
for formula, outputs, inputs, expected in (
        ("G !p", "p", "", True), ("G !X p", "p", "", False),
        ("G q", "p", "q", False), ("G X q", "p", "q", True)):
    realizable(FINITE, formula, outputs, expected, inputs)

# A winning reaction need not equal its guard; assigning a future guard is
# noncausal even though holding p true satisfies the implication.
realizable(INFINITE, "G(F q -> p)", "p", True)
realizable(INFINITE, "G(p <-> F q)", "p", False)
# The same unbounded-future guard cannot be implemented merely by inserting
# one or two registers. The implication-only originals below can hold p true.
realizable(INFINITE, "G(X p <-> F q)", "p", False)
realizable(INFINITE, "G(X X p <-> F q)", "p", False)

for finite, inputs, outputs, block, expected in (
        (True, "q", "p,r", "G F p; G F r; G !(p && r);", False),
        (True, "q", "p,r", "G(q -> F p); G(q -> F r); G !(p && r);", False),
        (False, "q", "p,r,s", "G F p; G F r; G(!(p && s) && !(r && s)); G s;", False),
        (False, "q", "p,r,s", "G(q -> F p); G(q -> F r); G(!(p && s) && !(r && s)); G s;", False),
        (False, "q,s", "p,r", "G F p; G F r; G(!(p && s) && !(r && s));", False),
        (False, "q,s,t", "p", "G(q -> F s); G(q -> F t); G !(s && t);", False),
        (False, "q", "p,r", "G F p; G F r; G(!(p && p) && !(r && r));", False),
        (False, "q", "p,r", "G(q -> F p); G(q -> F r); G(!(p && p) && !(r && r));", False),
        (False, "q,r", "p", "G(F q -> p);", True),
        (False, "q,r", "p", "G(F q -> !p);", True),
        (False, "q,r", "p", "G(F q -> X p);", True),
        (False, "q,r", "p", "G((r && F q) -> X p); G((!r && F q) -> X !p);", True),
        (False, "q,r", "p", "G(F q -> (X p <-> !p));", True),
        (False, "q,r", "p", "G(F q -> X X p);", True),
        (False, "q,r", "p", "G(F q -> F p);", True),
        (False, "q,r", "p", "G(!p -> p);", True)):
    source = (f"INFO {{ SEMANTICS: Mealy{',Finite' if finite else ''} TARGET: Mealy }} "
              "MAIN { INPUTS { " + inputs.replace(",", ";") + "; } OUTPUTS { "
              + outputs.replace(",", ";") + "; } GUARANTEES { " + block + " } }")
    solver = FINITE if finite else INFINITE
    original = subprocess.check_output([convert], input=source, text=True, timeout=5)
    realizable(solver, original, outputs, expected, inputs)
    for tool in (residual, compose):
        result = subprocess.run([tool], input=source, text=True,
                                capture_output=True, timeout=5)
        if tool == compose and result.returncode == 1:
            assert not expected and "spec is UNREALIZABLE" in result.stderr, result
            continue
        assert result.returncode == 0, result
        lines = [line for line in result.stdout.splitlines()
                 if not line.startswith(("c ", "ctl "))]
        assert len(lines) == 1, result.stdout
        realizable(solver, lines[0], outputs, expected, inputs)

# These enter composition with a locally solved register, bypassing the local
# free-output guard that masks the CLI fixtures. Both residuals must lose.
for chain in ("direct", "chain"):
    text = subprocess.check_output([phase_b_probe, chain], text=True, timeout=5)
    assert "register after Phase B: rejected" in text, text
    realizable(INFINITE, text.splitlines()[-1], "r", False)

# Unflagged atoms are emitted as environment inputs. The invariant certifier
# must not silently evaluate them as false, with or without Skolem outputs.
for body in ("!u", "!u && p"):
    source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
              f"OUTPUTS {{ p; }} GUARANTEES {{ G({body}); }} }}")
    for tool in (convert, residual, compose):
        text = subprocess.check_output([tool], input=source, text=True, timeout=5)
        lines = [line for line in text.splitlines()
                 if not line.startswith(("c ", "ctl "))]
        assert len(lines) == 1, text
        realizable(INFINITE, lines[0], "p", False, "u")

gold.finish()
