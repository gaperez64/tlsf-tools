"""Round 4: exact alphabets, unambiguous metadata, and Spot partitions."""
from pathlib import Path
import os
import re
import shlex
import subprocess
import sys
import tempfile

convert, residual, compose, ltlsynt, ltlfsynt, mode = sys.argv[1:]
wrapper = Path(__file__).resolve().parents[2] / "scripts/solve.sh"
solver_env = dict(os.environ, PATH=os.pathsep.join(
    [str(Path(ltlsynt).parent), str(Path(ltlfsynt).parent), os.environ["PATH"]]))


def run(*args, source=None):
    return subprocess.run(args, input=source, capture_output=True, text=True,
                          timeout=15, env=solver_env)


def spec(semantics, target, body):
    return f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} MAIN {{ {body} }}"


def partition(name):
    # Spot lowercases partition option text, including regexes.
    return "/^" + "".join(f"\\x{byte:02x}" for byte in name.encode()) + "$/"


def quoted(formula, inputs, outputs, delay_inputs=False):
    def atom(match):
        name = match[0]
        if name not in (inputs, outputs):
            return name
        return ("X " if delay_inputs and name == inputs else "") + f'"{name}"'
    return re.sub(r"[A-Za-z_][A-Za-z0-9_@']*", atom, formula)


def spot(solver, formula, inputs, outputs, semantics="Mealy"):
    args = [solver, "--realizability", f"--ins={inputs}", f"--outs={outputs}"]
    if solver == ltlfsynt:
        args.append(f"--semantics={semantics}")
    result = run(*args, "-f", formula)
    assert result.returncode in (0, 1), result
    status = "REALIZABLE" if result.returncode == 0 else "UNREALIZABLE"
    assert result.stdout.strip() == status, result
    return status


if mode == "lowercase":
    # This renaming used to change the winner while claiming exactness.
    original = "G(q <-> !Q) -> false"
    assert spot(ltlsynt, original, "/./", "") == "UNREALIZABLE"
    assert spot(ltlsynt, "G(q <-> !q) -> false", "q", "") == "REALIZABLE"
    for semantics, target in (("Mealy", "Mealy"), ("Moore", "Moore"),
                               ("Mealy,Strict", "Mealy"), ("Moore,Strict", "Moore"),
                               ("Mealy,Finite", "Mealy"), ("Moore,Finite", "Moore")):
        source = spec(semantics, target, "OUTPUTS { p; } "
                      "ASSUMPTIONS { G(q <-> !Q); } GUARANTEES { false; }")
        for tool in (residual, compose):
            kept = run(tool, source=source)
            assert kept.returncode == 0, kept
            assert "c cluster 0 outs= ins=q,Q\nG (q <-> !Q) -> false\n" in kept.stdout, kept
        # Both undeclared atoms, one declared input, and an implicit-input /
        # declared-output pair, in every formula section (including unused APs).
        for declaration in ("", "INPUTS { q; }", "OUTPUTS { q; }"):
            for role in ("INITIALLY", "PRESET", "REQUIRE", "ASSERT",
                         "ASSUMPTIONS", "GUARANTEES"):
                source = spec(semantics, target,
                              f"{declaration} {role} {{ q <-> Q; }}")
                for args in ((convert,), (residual, "--lowercase"),
                             (compose, "--lowercase")):
                    result = run(*args, source=source)
                    assert result.returncode != 0, (args, source, result)
                    assert result.stdout == "", result
                    assert "lowercasing would merge distinct signals" in result.stderr, result
                    assert "'q'" in result.stderr and "'Q'" in result.stderr, result
    source = spec("Mealy", "Mealy", "OUTPUTS { p; } "
                  "ASSUMPTIONS { G(q <-> !Q); } GUARANTEES { false; }")
    for backend in ("ltlsynt", "acacia"):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)
            (path / "spec.tlsf").write_text(source)
            controller = path / "strategy.aag"
            result = run(str(wrapper), "--tlsfcompose", compose, "--backend", backend,
                         "--solver", "/must-not-run", "--output", str(controller),
                         str(path / "spec.tlsf"))
            assert result.returncode != 0, result
            assert "lowercasing would merge distinct signals" in result.stderr, result
            assert not controller.exists(), result
    print("original: UNREALIZABLE; merged: REALIZABLE; lowercase exports: refused")
elif mode in ("comment", "signals"):
    for semantics, target in (("Mealy", "Mealy"), ("Moore", "Moore"),
                               ("Mealy,Finite", "Mealy"), ("Moore,Finite", "Moore")):
        if mode == "signals" and semantics == "Mealy":
            continue  # The Moore/finite fallback owns these residual games.
        finite = "Finite" in semantics
        solver = ltlfsynt if finite else ltlsynt
        cases = (("c", "p", "c -> p", True), ("c", "p", "c <-> X c", False)) if mode == "comment" else (
            ("q", "P", "G P", True), ("P", "p", "F (P && p)", False),
            ("P1", "P10", "F (P1 && P10)", False),
            ("GATE", "Grant", "G (GATE -> Grant)", True))
        for inputs, outputs, formula, winning in cases:
            if semantics == "Mealy,Finite" and mode == "signals":
                # Keep winning outputs residual instead of certifying a free
                # invariant/reaction before the fallback can be exercised.
                formula = {"G P": "G X P", "G (GATE -> Grant)":
                           "G (GATE -> X Grant)"}.get(formula, formula)
            expected = "REALIZABLE" if winning else "UNREALIZABLE"
            # These witnesses have the same verdict for both move orders.
            assert spot(solver, quoted(formula, inputs, outputs),
                        partition(inputs), partition(outputs), target) == expected
            source = spec(semantics, target,
                          f"INPUTS {{ {inputs}; }} OUTPUTS {{ {outputs}; }} "
                          f"GUARANTEES {{ {formula}; }}")
            for fmt in ("ltl", "ltlxba"):
                with tempfile.TemporaryDirectory() as tmp:
                    out = Path(tmp)
                    result = run(compose, "--output-dir", tmp, "--preprocess-policy", "off",
                                 "--format", fmt, source=source)
                    assert result.returncode == 0, result
                    assert "realizable iff every cluster is realizable" in result.stdout, result
                    text = (out / "cluster.0.ltl").read_text()
                    used_inputs = "" if formula in ("G P", "G X P") else inputs
                    used_outputs = "" if formula == "c <-> X c" else outputs
                    assert text == f"c outs={used_outputs}\nc ins={used_inputs}\n{formula}\n", text
                    script = (out / "compose.sh").read_text()
                    encode_moore = not finite and target == "Moore"
                    solver_file = out / ("cluster.0.mealy" if encode_moore else "cluster.0.spot")
                    assert solver_file.read_text() == quoted(formula, inputs, outputs, encode_moore) + "\n"
                    if mode == "signals":
                        invocation = next(line for line in script.splitlines() if line.startswith("run "))
                        fields = shlex.split(invocation)
                        assert fields[2] == (partition(used_inputs) if used_inputs else ""), invocation
                        assert fields[3] == (partition(used_outputs) if used_outputs else ""), invocation
                    result = run("sh", str(out / "compose.sh"))
                    assert result.returncode == (0 if winning else 1), result
                    assert result.stdout.splitlines()[-1] == f"SPEC {expected}", result
                    print(f"{semantics}: {formula}: {result.stdout.strip()}")
            if mode == "comment" and not finite and target == "Mealy":
                with tempfile.TemporaryDirectory() as tmp:
                    out = Path(tmp)
                    (out / "spec.tlsf").write_text(source)
                    result = run(str(wrapper), "--tlsfcompose", compose,
                                 "--solver", ltlsynt, "--work-dir", str(out / "work"),
                                 "--output", str(out / "strategy.aag"), str(out / "spec.tlsf"))
                    assert result.returncode == (0 if winning else 1), result
                    assert (out / "work/cluster.0.formula").read_text() == formula + "\n"
                    if winning:
                        aig = (out / "strategy.aag").read_text()
                        assert aig.startswith("aag ") and "i0 c\n" in aig and "o0 p\n" in aig, aig
                    else:
                        assert not (out / "strategy.aag").exists(), result
else:
    raise AssertionError(mode)
