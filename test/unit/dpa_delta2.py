"""Spot-generated Boolean Pi_2/Sigma_2 formulas, checked one at a time."""
import pathlib
import subprocess
import sys
import tempfile

exe, randltl, ltlfilt = sys.argv[1:]
raw = subprocess.check_output(
    [randltl, "a", "b", "c", "--seed=20852", "-n", "1600",
     "--tree-size=6..20", "--ltl-priorities=strongX=0"], text=True, timeout=15
)
filtered = subprocess.check_output(
    [ltlfilt, "--delta2"], input=raw, text=True, timeout=15
).splitlines()
assert len(filtered) >= 300
formulas = filtered[:300]
# Independent mixed skeletons as well as the unmodified random distribution.
for i, left in enumerate(filtered[:60]):
    right = filtered[-1 - i]
    # Boolean closure stays in the fragment, including complements/sharing.
    formulas.append(f"({left}) <-> !({right})")
with tempfile.TemporaryDirectory() as directory:
    path = pathlib.Path(directory) / "formula.ltl"
    for index, formula in enumerate(formulas):
        path.write_text(formula + "\n")
        try:
            subprocess.run([exe, str(path), "--allow-unproved"], check=True, timeout=5,
                           stdout=subprocess.PIPE)
        except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
            print(f"formula {index}: {formula}", file=sys.stderr)
            raise
print(f"{len(formulas)} random Delta_2 language equivalences passed")
