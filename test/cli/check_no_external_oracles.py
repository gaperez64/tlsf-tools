"""Reject external oracle dependencies throughout executable repository content."""
import ast
import hashlib
import json
from pathlib import Path
import re
import sys

TOOLS = {"ltlsynt", "ltlfsynt", "autfilt", "ltl2tgba", "ltlfilt", "randltl"}
MODULES = {"spot", "buddy", "acacia_lift"}
FORBIDDEN = re.compile(r"(?i)(?<![a-z0-9_])(?:spot|buddy|libspot|" +
                       "|".join(sorted(TOOLS)) + r")(?![a-z0-9_])|"
                       r"--spot(?:-source)?\b|--bindings-site\b|spot::|\bspot_[a-z_]+|-lspot\b")
CALLS = {"run", "call", "check_call", "check_output", "Popen", "system", "popen", "which"}


def external_command(node):
    if isinstance(node, (ast.List, ast.Tuple)):
        return bool(node.elts) and external_command(node.elts[0])
    if isinstance(node, ast.Name):
        return node.id in TOOLS
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return bool(FORBIDDEN.search(node.value))
    if isinstance(node, ast.BinOp):
        return external_command(node.left) or external_command(node.right)
    if isinstance(node, ast.JoinedStr):
        return any(external_command(part) for part in node.values)
    return False


def inspect_python(path, text):
    tree = ast.parse(text, filename=str(path))
    for node in ast.walk(tree):
        modules = ([alias.name for alias in node.names] if isinstance(node, ast.Import)
                   else [node.module] if isinstance(node, ast.ImportFrom) else [])
        assert not any(name and name.split(".")[0] in MODULES for name in modules), (path, node.lineno)
        if not isinstance(node, ast.Call):
            continue
        function = node.func
        name = function.attr if isinstance(function, ast.Attribute) else (
            function.id if isinstance(function, ast.Name) else None)
        if name in CALLS:
            command = node.args[0] if node.args else next(
                (kw.value for kw in node.keywords if kw.arg in ("args", "cmd")), None)
            assert not external_command(command), (path, node.lineno, "external oracle command")
        if name in ("import_module", "__import__") and node.args:
            module = node.args[0]
            assert not (isinstance(module, ast.Constant) and isinstance(module.value, str)
                        and module.value.split(".")[0] in MODULES), (path, node.lineno)


def check(root):
    frozen = json.loads((root / "tools/golden/historical-files.json").read_text())
    for name, receipt in frozen.items():
        path = root / name
        assert path.suffix in (".json", ".md", ".tlsf") and receipt["reason"], name
        assert hashlib.sha256(path.read_bytes()).hexdigest() == receipt["sha256"], (name, "frozen documentation/data changed")
    # The scanner and its mutation test contain the policy vocabulary itself.
    vocabulary = {"test/cli/check_no_external_oracles.py", "tools/golden/test_gates.py"}
    count = 0
    for directory in ("tools", "scripts", "bench", "test", "src", "include", "examples", ".github", "docs"):
        for path in sorted((root / directory).rglob("*")):
            if not path.is_file() or "__pycache__" in path.parts or path.suffix in (".pyc", ".png"):
                continue
            try:
                text = path.read_text()
            except UnicodeDecodeError:
                continue
            relative = str(path.relative_to(root))
            if path.suffix == ".py":
                inspect_python(path, text)
            # No executable source can use a historical-data allowlist entry.
            if relative in frozen or relative in vocabulary:
                continue
            assert not FORBIDDEN.search(text), (relative, "external oracle reference", FORBIDDEN.search(text)[0] if FORBIDDEN.search(text) else "")
            count += 1
    for path in (root / "meson.build", root / "meson.options", root / "README.md"):
        assert not FORBIDDEN.search(path.read_text()), path
    print(f"external-oracle guard: {count} files; {len(frozen)} explicit frozen provenance/data entries")


if __name__ == "__main__":
    check(Path(sys.argv[1]).resolve())
