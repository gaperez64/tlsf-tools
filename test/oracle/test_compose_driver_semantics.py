"""Execute generated drivers and compare against Spot on the original game."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

compose, ltlsynt, ltlfsynt, mode = sys.argv[1:]
ltlsynt_has_semantics = "--semantics=" in subprocess.check_output(
    [ltlsynt, "--help"], text=True)


def verdict(solver, formula, inputs, outputs, moore=False):
    args = [solver, "--realizability"]
    dual = moore and solver == ltlsynt and not ltlsynt_has_semantics
    if dual:
        # Independent oracle: determinacy makes a Moore game the complement
        # of its Mealy dual (negate the ORIGINAL formula and exchange players).
        formula, inputs, outputs = f"!({formula})", outputs, inputs
    elif moore or solver == ltlfsynt:
        args.append("--semantics=" + ("Moore" if moore else "Mealy"))
    result = subprocess.run(args + [f"--ins={inputs}", f"--outs={outputs}",
                                   "-f", formula],
                            capture_output=True, text=True, timeout=5)
    assert result.returncode in (0, 1), result
    assert result.stdout.strip() == ("REALIZABLE" if result.returncode == 0
                                      else "UNREALIZABLE"), result
    return (result.returncode == 0) != dual


def check(semantics, target, formula, expected_formula, expected_solver_formula,
          expected, policy, inputs="q", implicit=False, extra_args=()):
    finite = "Finite" in semantics
    original_moore = semantics.startswith("Moore")
    solver = ltlfsynt if finite else ltlsynt
    assert verdict(solver, formula, inputs, "p", original_moore) == expected
    declaration = "" if implicit or not inputs else f"INPUTS {{ {inputs}; }}"
    source = (f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} MAIN {{ "
              f"{declaration} OUTPUTS {{ p; }} GUARANTEES {{ {formula}; }} }}")
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        result = subprocess.run([compose, "--output-dir", tmp,
                                 "--preprocess-policy", policy, *extra_args],
                                input=source, text=True, capture_output=True,
                                timeout=10)
        assert result.returncode == 0, result
        print(f"{semantics} -> {target} ({policy}): {result.stdout.strip()}", flush=True)
        assert "realizable iff every cluster is realizable" in result.stdout
        assert "backend=OxiDD" not in result.stdout, result.stdout
        assert "aiger=cluster.0.aag" not in result.stdout, result.stdout
        text = (out / "cluster.0.ltl").read_text()
        residual_outputs = "p" if "p" in expected_formula else ""
        assert text == f"c outs={residual_outputs}\nc ins={inputs}\n{expected_formula}\n", text
        driver = out / "compose.sh"
        script = driver.read_text()
        if finite:
            assert "ltlfsynt --semantics=" + target in script, script
            assert "  ltlsynt " not in script, script
        else:
            assert "ltlsynt --ins=" in script, script
            if expected_solver_formula is not None:
                encoded = out / "cluster.0.mealy"
                names = "|".join(re.escape(n) for n in ("p", inputs) if n)
                quoted = re.sub(r"\b(?:" + names + r")\b",
                                lambda m: '"' + m[0] + '"', expected_solver_formula)
                assert encoded.read_text().strip() == quoted
                assert 'run cluster.0.ltl' in script and 'cluster.0.mealy' in script
        # An old controller in a reused output directory must not override the
        # selected solver, including for finite and Moore fallback routes.
        (out / "cluster.0.aag").write_text("stale controller\n")
        env = dict(os.environ, PATH=os.pathsep.join(
            [str(Path(ltlsynt).parent), str(Path(ltlfsynt).parent), os.environ["PATH"]]))
        run = subprocess.run(["sh", str(driver)], capture_output=True,
                             text=True, timeout=10, env=env)
        print(run.stdout.strip(), flush=True)
        status = "REALIZABLE" if expected else "UNREALIZABLE"
        assert run.stdout.splitlines() == [f"cluster.0.ltl: {status}", f"SPEC {status}"], run
        assert run.returncode == (0 if expected else 1), run
        # Unsupported options, missing solvers, and other solver errors must
        # never be turned into an exact UNREALIZABLE verdict.
        failing_solver = out / ("ltlfsynt" if finite else "ltlsynt")
        failing_solver.write_text("#!/bin/sh\nexit 2\n")
        failing_solver.chmod(0o755)
        env["PATH"] = str(out) + os.pathsep + env["PATH"]
        run = subprocess.run(["sh", str(driver)], capture_output=True,
                             text=True, timeout=5, env=env)
        assert run.returncode == 2 and run.stdout.splitlines()[-1] == "SPEC UNKNOWN", run
        assert "UNREALIZABLE" not in run.stdout, run


if mode == "moore":
    for policy in ("always", "off"):
        for semantics in ("Mealy", "Mealy,Strict"):
            check(semantics, "Moore", "G(p <-> X q)", "G (X p <-> X q)",
                  "G (X p <-> X X q)", False, policy)
        for semantics in ("Moore", "Moore,Strict"):
            check(semantics, "Moore", "G(p <-> q)", "G (p <-> q)",
                  "G (p <-> X q)", False, policy)
        check("Moore", "Moore", "G(p <-> u)", "G (p <-> u)",
              "G (p <-> X u)", False, policy, inputs="u", implicit=True)
        # A winning adaptation checks the other verdict as well.
        check("Mealy", "Moore", "G(p <-> q) || F p", "G (X p <-> q) || F X p",
              "G (X p <-> X q) || F X p", True, policy)
    # Route decisions use the effective target, including CLI overrides.
    check("Mealy", "Mealy", "G(p <-> X q)", "G (X p <-> X q)",
          "G (X p <-> X X q)", False, "always",
          extra_args=("--overwrite-target", "Moore"))
elif mode == "finite":
    for policy in ("always", "off"):
        check("Mealy,Finite", "Mealy", "X false", "X false", None,
              True, policy, inputs="")
        check("Mealy,Finite", "Mealy", "X[!] false", "false", None,
              False, policy, inputs="")
        check("Moore,Finite", "Moore", "G(p <-> q)", "G (p <-> q)", None,
              False, policy)
        check("Moore,Finite", "Moore", "G(p <-> X q)", "G (p <-> X q)", None,
              True, policy)
elif mode == "implicit":
    for semantics in ("Moore", "Moore,Strict"):
        check(semantics, "Mealy", "G(p <-> u)", "G (p <-> X u)",
              None, False, "off", inputs="u", implicit=True)
elif mode == "wrapper":
    wrapper = Path(__file__).resolve().parents[2] / "scripts/solve.sh"
    for semantics, target, formula in (("Mealy,Finite", "Mealy", "X false"),
                                        ("Moore,Finite", "Moore", "G(p <-> q)"),
                                        ("Moore", "Moore", "G(p <-> q)"),
                                        ("Mealy", "Moore", "G(p <-> q)")):
        for backend in ("ltlsynt", "acacia"):
            with tempfile.TemporaryDirectory() as tmp:
                source = Path(tmp) / "spec.tlsf"
                source.write_text(f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} "
                                  f"MAIN {{ INPUTS {{ q; }} OUTPUTS {{ p; }} GUARANTEES {{ {formula}; }} }}")
                controller = Path(tmp) / "strategy.aag"
                run = subprocess.run([str(wrapper), "--tlsfcompose", compose,
                                      "--backend", backend, "--solver", "/must-not-run",
                                      "--output", str(controller), str(source)],
                                     text=True, capture_output=True, timeout=10)
                assert run.returncode == 2, run
                assert "controller export supports only infinite-word Mealy targets" in run.stderr, run
                assert not controller.exists(), run
                print(f"{semantics} -> {target} ({backend}): {run.stderr.strip()}")
else:
    raise AssertionError(mode)
