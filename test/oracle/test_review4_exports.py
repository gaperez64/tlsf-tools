"""Round 4: exact alphabets, unambiguous metadata, and golden exports."""
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile

from golden import Golden

convert, residual, compose, mode = sys.argv[1:]
gold = Golden("review4-" + mode)
wrapper = Path(__file__).resolve().parents[2] / "scripts/solve.sh"


def run(*args, source=None):
    return subprocess.run(args, input=source, capture_output=True, text=True,
                          timeout=15)


def spec(semantics, target, body):
    return f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} MAIN {{ {body} }}"


def partition(name):
    # The emitted backend protocol lowercases partition text, including regexes.
    return "/^" + "".join(f"\\x{byte:02x}" for byte in name.encode()) + "$/"


def quoted(formula, inputs, outputs, delay_inputs=False):
    def atom(match):
        name = match[0]
        if name not in (inputs, outputs):
            return name
        return ("X " if delay_inputs and name == inputs else "") + f'"{name}"'
    return re.sub(r"[A-Za-z_][A-Za-z0-9_@']*", atom, formula)


def verdict(formula, inputs, outputs, finite=False, semantics="Mealy"):
    return "REALIZABLE" if gold.verdict(formula, inputs, outputs, finite,
                                         semantics == "Moore") else "UNREALIZABLE"


if mode == "lowercase":
    # This renaming used to change the winner while claiming exactness.
    original = "G(q <-> !Q) -> false"
    assert verdict(original, "/./", "") == "UNREALIZABLE"
    assert verdict("G(q <-> !q) -> false", "q", "") == "REALIZABLE"
    for semantics, target in (("Mealy", "Mealy"), ("Moore", "Moore"),
                               ("Mealy,Strict", "Mealy"), ("Moore,Strict", "Moore"),
                               ("Mealy,Finite", "Mealy"), ("Moore,Finite", "Moore")):
        # Keep the case pair in the cluster's core so the satisfiable disjoint
        # environment pruning rule cannot remove the alphabet under test.
        source = spec(semantics, target, "OUTPUTS { p; } PRESET { q <-> Q; } "
                      "ASSUMPTIONS { G(q <-> !Q); } GUARANTEES { false; }")
        for tool in (residual, compose):
            kept = run(tool, source=source)
            assert kept.returncode == 0, kept
            assert "c cluster 0 outs= ins=q,Q\n" in kept.stdout, kept
            assert "G (q <-> !Q) -> false" in kept.stdout, kept
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
            assert verdict(quoted(formula, inputs, outputs),
                           partition(inputs), partition(outputs), finite, target) == expected
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
                    gold.artifacts(out)
            if mode == "comment" and not finite and target == "Mealy":
                # Keep the wrapper's AP-named-c/comment disambiguation check.
                # The protocol stub exercises export/merge without executing
                # the emitted compose driver or invoking a synthesis tool.
                with tempfile.TemporaryDirectory() as tmp:
                    out = Path(tmp)
                    source_path = out / "spec.tlsf"
                    source_path.write_text(source)
                    solver = Path(__file__).resolve().parents[1] / "fixtures/fake_backend.sh"
                    if not winning:
                        solver = out / "fake-backend"
                        solver.write_text("#!/bin/sh\necho UNREALIZABLE\nexit 1\n")
                        solver.chmod(0o755)
                    controller = out / "strategy.aag"
                    result = run(str(wrapper), "--tlsfcompose", compose,
                                 "--solver", str(solver), "--work-dir", str(out / "work"),
                                 "--output", str(controller), str(source_path))
                    assert result.returncode == (0 if winning else 1), result
                    assert (out / "work/cluster.0.formula").read_text() == formula + "\n"
                    if winning:
                        text = controller.read_text()
                        assert text.startswith("aag ") and "i0 c\n" in text and "o0 p\n" in text
                    else:
                        assert not controller.exists()

else:
    raise AssertionError(mode)

gold.finish()
