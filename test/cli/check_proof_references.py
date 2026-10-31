"""Keep the proof correspondence's source locations in the current tree."""
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
readme = (root / "proofs/README.md").read_text()
references = re.findall(
    r"`((?:(?:src|proofs)/[\w/]+|print_ltlxba)\.(?:c|cc|h|lean)):([\d,–-]+)`",
    readme)
assert references, "no proof source references found"
covered = {}
for name, locations in references:
    path = root / (name if name.startswith(("src/", "proofs/")) else "src/lib/" + name)
    lines = path.read_text().splitlines()
    for part in locations.split(","):
        bounds = [int(n) for n in re.split("[–-]", part)]
        assert 1 <= bounds[0] <= bounds[-1] <= len(lines), (name, locations)
        covered.setdefault(name, set()).update(range(bounds[0] - 1, bounds[-1]))
    if name == "src/tools/tlsfcompose/main.c":
        line = int(locations)
        assert 'fputs("ctl ", dst);' in lines[line - 1], (
            f"{name}:{line} refers to {lines[line - 1]!r}, not controller emission")
# The native certificate and its Lean bridge must actually be covered by the
# documented ranges, rather than merely referring to existing line numbers.
anchors = {
    "src/lib/env_witness.c": (
        "static int compile_node(",
        "static EnvWitnessResult evaluate(",
        "EnvWitnessResult env_witness_search(",
    ),
    "proofs/TlsfProofs/Pruning.lean": (
        "def environmentFormula ",
        "theorem environment_sat_iff ",
        "theorem envSat_of_word ",
    ),
}
for name, declarations in anchors.items():
    lines = (root / name).read_text().splitlines()
    for declaration in declarations:
        assert any(declaration in lines[i] for i in covered.get(name, ())), (
            name, declaration, "missing from correspondence ranges")
print(f"checked {len(references)} proof source references; "
      "controller emission and native witness bridge found")
