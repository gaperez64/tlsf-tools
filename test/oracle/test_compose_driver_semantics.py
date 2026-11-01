"""Check complete compose driver/cluster exports against committed goldens."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from golden import Golden

compose, mode = sys.argv[1:]
gold = Golden("compose-" + mode)


def check(semantics, target, formula, expected_formula, expected_solver_formula,
          expected, policy, inputs="q", implicit=False, extra_args=()):
    finite = "Finite" in semantics
    original_moore = semantics.startswith("Moore")
    assert gold.verdict(formula, inputs, "p", finite, original_moore) == expected
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
        gold.artifacts(out)
        # The generated driver must derive status from the selected command,
        # preserve solver errors as UNKNOWN, and never trust stale controllers.
        assert 'SPEC UNKNOWN' in script and 'exit 2' in script, script



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

gold.finish()
