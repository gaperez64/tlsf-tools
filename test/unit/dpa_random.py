"""Fixed-seed Spot-generated formulas, stratified within the admitted slice."""
import pathlib
import subprocess
import sys
import tempfile

exe, randltl = sys.argv[1:]
common = "strongX=0,not=0,equiv=0,implies=0,xor=0"
formulas = []
for seed, priorities, recurrence in [
    (31415, common + ",F=0,U=0,M=0", False),
    (27182, common + ",F=0,G=0,U=0,R=0,W=0,M=0", True),
]:
    lines = subprocess.check_output(
        [randltl, "a", "b", "c", "--seed=" + str(seed), "-n", "18",
         "--tree-size=4..12", "--ltl-priorities=" + priorities], text=True
    ).splitlines()
    for line in lines:
        formula = f"G F ({line})" if recurrence else line
        formulas.extend([formula, f"!({formula})"])
with tempfile.TemporaryDirectory() as directory:
    path = pathlib.Path(directory) / "formulas.ltl"
    path.write_text("\n".join(formulas) + "\n")
    subprocess.run([exe, str(path)], check=True)
print(f"{len(formulas)} random fragment equivalences passed")
