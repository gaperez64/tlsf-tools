"""A repeated correspondence anchor must survive at every documented location."""
import contextlib
import io
from pathlib import Path
import runpy
import sys
from unittest.mock import patch

root = Path(__file__).resolve().parents[2]
checker = root / "test/cli/check_proof_references.py"
source = root / "src/lib/dpa_formula.c"
original = source.read_text()
anchor = "static uint32_t map_impl(TlsfDpa *c, uint32_t f, unsigned mode, uint64_t epoch,"
lines = original.splitlines()
locations = [i for i, line in enumerate(lines, 1) if line.strip() == anchor]
assert len(locations) == 2
read_text = Path.read_text

for removed, retained in (locations, locations[::-1]):
    mutant = lines.copy()
    mutant[removed - 1] = "/* removed correspondence target */"

    def changed_text(path, *args, **kwargs):
        if path == source:
            return "\n".join(mutant) + "\n"
        text = read_text(path, *args, **kwargs)
        # Redirect docs to the surviving identical occurrence, reproducing the
        # set-based check's blind spot without relying on stale line numbers.
        return text.replace(f"dpa_formula.c:{removed}", f"dpa_formula.c:{retained}")

    with patch.object(Path, "read_text", changed_text), \
            patch.object(sys, "argv", [str(checker), str(root)]), \
            contextlib.redirect_stdout(io.StringIO()):
        try:
            runpy.run_path(str(checker), run_name="__main__")
        except AssertionError as error:
            assert "anchor occurrence counts changed" in str(error), str(error)
        else:
            raise AssertionError(f"accepted removal of anchor at {removed}")

print("Both repeated correspondence anchor removals rejected")
