"""Replay all 360 committed Boolean Pi_2/Sigma_2 formulas individually."""
from pathlib import Path
import subprocess
import sys
import tempfile

executable, corpus = sys.argv[1:]
formulas = Path(corpus).read_text().splitlines()
assert len(formulas) == 360
with tempfile.TemporaryDirectory() as directory:
    path = Path(directory) / "formula.ltl"
    for index, formula in enumerate(formulas):
        path.write_text(formula + "\n")
        result = subprocess.run([executable, str(path), "--allow-unproved"],
                                capture_output=True, text=True, timeout=30)
        assert result.returncode == 0, (index, formula, result.stderr)
print(f"{len(formulas)} golden Delta_2 language checks passed")
