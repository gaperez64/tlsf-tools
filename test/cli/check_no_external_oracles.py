"""Prevent reintroducing external oracle imports, discovery or includes."""

import ast
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
external_tools = {"ltlsynt", "ltlfsynt", "autfilt", "ltl2tgba", "ltlfilt", "randltl"}
external_modules = {"spot", "buddy", "acacia_lift"}
command_calls = {"run", "call", "check_call", "check_output", "Popen", "system", "popen", "which"}


def external_command(node):
    if isinstance(node, (ast.List, ast.Tuple)):
        return bool(node.elts) and external_command(node.elts[0])
    if isinstance(node, ast.Name):
        return node.id in external_tools
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        # Include absolute paths and shell commands, while allowing backend
        # names to remain ordinary product data elsewhere in the tests.
        return bool(re.search(r"(?:^|[/\s])(?:" + "|".join(sorted(external_tools)) + r")(?:$|\s)", node.value))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return external_command(node.right)  # pathlib command construction
    return False


for path in sorted((root / "test").rglob("*.py")):
    tree = ast.parse(path.read_text(), filename=str(path))
    for node in ast.walk(tree):
        modules = ([alias.name for alias in node.names] if isinstance(node, ast.Import)
                   else [node.module] if isinstance(node, ast.ImportFrom) else [])
        assert not any(name and name.split(".")[0] in external_modules
                       for name in modules), path
        if isinstance(node, ast.Call):
            function = node.func
            name = function.attr if isinstance(function, ast.Attribute) else (
                function.id if isinstance(function, ast.Name) else None)
            if name in command_calls:
                command = node.args[0] if node.args else next(
                    (kw.value for kw in node.keywords if kw.arg in ("args", "cmd")), None)
                assert not external_command(command), (path, node.lineno, "external oracle command")
            if name in ("import_module", "__import__") and node.args:
                module = node.args[0]
                assert not (isinstance(module, ast.Constant) and isinstance(module.value, str)
                            and module.value.split(".")[0] in external_modules), (path, node.lineno)
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
