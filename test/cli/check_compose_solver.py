"""Run generated drivers with a stub executable instead of a synthesis tool."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile


compose = sys.argv[1]
env = os.environ.copy()
env.pop("TLSFCOMPOSE_SOLVER", None)
help_result = subprocess.run([compose, "--help"], env=env, text=True,
                             capture_output=True, check=True)
for text in ("--solver COMMAND", "TLSFCOMPOSE_SOLVER", "ltlsynt", "ltlfsynt",
             "wrapper script"):
    assert text in help_result.stderr, help_result
for args in (["--solver"], ["--solver", ""]):
    result = subprocess.run([compose, *args], env=env, text=True,
                            capture_output=True)
    assert result.returncode != 0 and "requires" in result.stderr, result

with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    # Shell metacharacters, spaces and an apostrophe must stay in one word.
    stub = root / "solver ' $(touch injected);"
    stub.write_text('''#!/bin/sh
printf '%s\\n' "$@" > "$SOLVER_ARGS"
while [ "$#" -gt 0 ]; do
  if [ "$1" = -F ]; then
    cat "$2" > "$SOLVER_FORMULA"
    break
  fi
  shift
done
exit "$SOLVER_STATUS"
''')
    stub.chmod(0o755)
    for finite, target in ((False, "Mealy"), (False, "Moore"),
                           (True, "Mealy"), (True, "Moore")):
        semantics = target + (",Finite" if finite else "")
        source = (f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} "
                  "MAIN { INPUTS { q; } OUTPUTS { p; } "
                  "GUARANTEES { G(p <-> X q); } }")
        out = root / "output"
        out.mkdir(exist_ok=True)
        base = [compose, "--output-dir", str(out),
                "--preprocess-policy", "off"]
        # An empty environment setting has the same default as an unset one.
        for setting in ({}, {"TLSFCOMPOSE_SOLVER": ""}):
            subprocess.run(base, input=source, env={**env, **setting},
                           text=True, capture_output=True, check=True)
            driver = (out / "compose.sh").read_text()
            expected = "  ltlfsynt --semantics=" + target if finite else "  ltlsynt --ins="
            assert expected in driver, driver
        for selection in ("env", "cli"):
            generation_env = {**env, "TLSFCOMPOSE_SOLVER": str(stub)
                              if selection == "env" else "/must-not-run"}
            args = base + (["--solver", str(stub)] if selection == "cli" else [])
            subprocess.run(args, input=source, env=generation_env, text=True,
                           capture_output=True, check=True)
            for status, verdict, code in ((0, "REALIZABLE", 0),
                                           (1, "UNREALIZABLE", 1),
                                           (7, "UNKNOWN", 2)):
                run_env = {**env, "SOLVER_ARGS": str(root / "args"),
                           "SOLVER_FORMULA": str(root / "formula"),
                           "SOLVER_STATUS": str(status)}
                result = subprocess.run(["sh", str(out / "compose.sh")],
                                        cwd=root, env=run_env, text=True,
                                        capture_output=True, timeout=10)
                assert result.returncode == code, result
                assert "SPEC " + verdict in result.stdout, result
                argv = (root / "args").read_text().splitlines()
                expected = (["--semantics=" + target] if finite else [])
                expected += [r"--ins=/^\x71$/", r"--outs=/^\x70$/"]
                assert argv[:len(expected)] == expected, argv
                assert argv[-3] == "-F" and argv[-1] == "--realizability", argv
                assert not Path(argv[-2]).exists(), "temporary formula leaked"
                formula = (root / "formula").read_text()
                assert '"p"' in formula and '"q"' in formula, formula
                assert "c ins=" not in formula and "c outs=" not in formula, formula
                if not finite and target == "Moore":
                    assert 'X X "q"' in formula, formula
                assert not (root / "injected").exists(), "solver command was evaluated"
    stub.unlink()
    result = subprocess.run(["sh", str(out / "compose.sh")], cwd=root,
                            env=env, text=True, capture_output=True, timeout=10)
    assert result.returncode == 2 and "SPEC UNKNOWN" in result.stdout, result
