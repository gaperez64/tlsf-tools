"""Prevent reintroducing external oracle imports, discovery or includes."""

import ast
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
for path in sorted((root / "test").rglob("*.py")):
    tree = ast.parse(path.read_text(), filename=str(path))
    for node in ast.walk(tree):
        modules = ([alias.name for alias in node.names] if isinstance(node, ast.Import)
                   else [node.module] if isinstance(node, ast.ImportFrom) else [])
        assert not any(name and name.split(".")[0] in ("spot", "buddy", "acacia_lift")
                       for name in modules), path
for pattern in ("*.c", "*.cc", "*.cpp", "*.h", "*.hh"):
    for directory in (root / "src", root / "test"):
        for path in directory.rglob(pattern):
            assert not re.search(r"#\s*include\s*[<\"]spot/", path.read_text()), path
for path in [root / "meson.build", *(root / "src").rglob("meson.build"),
             *(root / "test").rglob("meson.build"), *(root / "examples").rglob("meson.build")]:
    text = path.read_text()
    assert not re.search(r"find_program\(['\"](?:ltl(?:f?synt|2tgba|filt)|autfilt|randltl)['\"]", text), path
    assert "import spot" not in text, path
    assert "spot_dep" not in text and "libspot" not in text, path
    assert not re.search(r"files\((?:scripts\s*/\s*)?['\"](?:gr1_monitor_game|verify_strategy_explicit|verify_aiger_ltl|check_norm_equiv)\.", text), path
