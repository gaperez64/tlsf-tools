"""Fixed-seed Spot-generated formulas, stratified within the admitted slice."""
import argparse
import pathlib
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("executable")
parser.add_argument("randltl")
parser.add_argument("--allow-unproved", action="store_true")
args = parser.parse_args()
exe, randltl = args.executable, args.randltl
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
    subprocess.run([exe, str(path)] +
                   (["--allow-unproved"] if args.allow_unproved else []), check=True)
print(f"{len(formulas)} random fragment equivalences passed")
