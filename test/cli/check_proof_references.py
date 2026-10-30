"""Keep the proof correspondence's source locations in the current tree."""
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
readme = (root / "proofs/README.md").read_text()
references = re.findall(r"`((?:src/[\w/]+|print_ltlxba)\.[ch]):([\d,–-]+)`", readme)
assert references, "no proof source references found"
for name, locations in references:
    path = root / (name if name.startswith("src/") else "src/lib/" + name)
    lines = path.read_text().splitlines()
    for part in locations.split(","):
        bounds = [int(n) for n in re.split("[–-]", part)]
        assert 1 <= bounds[0] <= bounds[-1] <= len(lines), (name, locations)
    if name == "src/tools/tlsfcompose/main.c":
        line = int(locations)
        assert 'fputs("ctl ", dst);' in lines[line - 1], (
            f"{name}:{line} refers to {lines[line - 1]!r}, not controller emission")
print(f"checked {len(references)} proof source references; controller emission found")
