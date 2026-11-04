"""Reject external oracle dependencies throughout executable repository content."""
import ast
import hashlib
import json
from pathlib import Path, PurePath, PureWindowsPath
import re
import sys

DATA_FILE = "tools/golden/oracle-guard-data.json"
DATA_SHA256 = "064eb5ef1d2785f1699eb817d9a27b12e0e9613d9930d97259e6d8871ff802d5"


def read_data(root):
    """Bind the sole vocabulary exemption to inert JSON with these exact bytes."""
    payload = (root / DATA_FILE).read_bytes()
    assert hashlib.sha256(payload).hexdigest() == DATA_SHA256, (DATA_FILE, "guard data changed")
    return json.loads(payload)


DATA = read_data(Path(__file__).resolve().parents[2])
TOOLS = set(DATA["tools"])
MODULES = set(DATA["modules"])
FORBIDDEN = re.compile(DATA["forbidden_pattern"])
CALLS = {"run", "call", "check_call", "check_output", "Popen", "system", "popen", "which"}
EXEC_CALLS = {"execl", "execle", "execlp", "execlpe", "execv", "execve", "execvp", "execvpe",
              "posix_spawn", "posix_spawnp"}
SPAWN_CALLS = {"spawnl", "spawnle", "spawnlp", "spawnlpe", "spawnv", "spawnve", "spawnvp", "spawnvpe"}
PATH_CALLS = {"Path", "PurePath", "PosixPath", "PurePosixPath", "WindowsPath", "PureWindowsPath"}
STRING_CALLS = PATH_CALLS | {"join", "joinpath", "str", "fspath"}


def call_name(function):
    return function.attr if isinstance(function, ast.Attribute) else (
        function.id if isinstance(function, ast.Name) else None)


def call_arguments(node):
    """Include literal argument unpacking as well as ordinary call syntax."""
    args = []
    for arg in node.args:
        if isinstance(arg, ast.Starred) and isinstance(arg.value, (ast.List, ast.Tuple)):
            args.extend(arg.value.elts)
        else:
            args.append(arg)
    keywords = {}
    for kw in node.keywords:
        if kw.arg is None and isinstance(kw.value, ast.Dict):
            keywords.update((key.value, value) for key, value in zip(kw.value.keys, kw.value.values)
                            if isinstance(key, ast.Constant) and isinstance(key.value, str))
        elif kw.arg is not None:
            keywords[kw.arg] = kw.value
    return args, keywords


def static_string(node):
    """Resolve string/path construction without evaluating repository code."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Div)):
        left, right = static_string(node.left), static_string(node.right)
        if left is not None and right is not None:
            return left + right if isinstance(node.op, ast.Add) else str(PurePath(left, right))
    if isinstance(node, ast.JoinedStr):
        parts = [static_string(part) for part in node.values]
        if all(part is not None for part in parts):
            return "".join(parts)
    if isinstance(node, ast.FormattedValue):
        value = static_string(node.value)
        if value is None:
            if not isinstance(node.value, ast.Constant):
                return None
            value = node.value.value
        spec = static_string(node.format_spec) if node.format_spec is not None else ""
        if spec is not None:
            convert = {ord("s"): str, ord("r"): repr, ord("a"): ascii}.get(node.conversion)
            try:
                return format(convert(value) if convert else value, spec)
            except (TypeError, ValueError):
                return None
    if isinstance(node, ast.Call):
        name = call_name(node.func)
        if name in STRING_CALLS:
            args, keywords = call_arguments(node)
            if name == "str" and not args and set(keywords) == {"object"}:
                args, keywords = [keywords["object"]], {}
            if name == "joinpath" and isinstance(node.func, ast.Attribute):
                args = [node.func.value, *args]
            parts = [static_string(arg) for arg in args]
            if keywords or not parts or any(part is None for part in parts):
                return None
            if name in PATH_CALLS | {"join", "joinpath"}:
                path_type = PureWindowsPath if name in {"WindowsPath", "PureWindowsPath"} else PurePath
                return str(path_type(*parts))
            if len(parts) == 1:
                return parts[0]
    return None


def external_command(node):
    if isinstance(node, (ast.List, ast.Tuple)):
        return bool(node.elts) and external_command(node.elts[0])
    if isinstance(node, ast.Name):
        return node.id in TOOLS
    value = static_string(node)
    if value is not None and FORBIDDEN.search(value):
        return True
    if isinstance(node, ast.BinOp):
        return external_command(node.left) or external_command(node.right)
    if isinstance(node, ast.JoinedStr):
        return any(external_command(part) for part in node.values)
    if isinstance(node, ast.FormattedValue):
        return external_command(node.value)
    if isinstance(node, ast.Call) and call_name(node.func) in STRING_CALLS:
        # A dynamic directory does not hide a statically known executable name.
        return any(external_command(arg) for arg in node.args) or any(
            external_command(kw.value) for kw in node.keywords)
    return False


def inspect_python(path, text):
    tree = ast.parse(text, filename=str(path))
    for node in ast.walk(tree):
        modules = ([alias.name for alias in node.names] if isinstance(node, ast.Import)
                   else [node.module] if isinstance(node, ast.ImportFrom) else [])
        assert not any(name and name.split(".")[0] in MODULES for name in modules), (path, node.lineno)
        if not isinstance(node, ast.Call):
            continue
        name = call_name(node.func)
        args, keywords = call_arguments(node)
        if name in CALLS | EXEC_CALLS | SPAWN_CALLS:
            index = 1 if name in SPAWN_CALLS else 0
            commands = args[index:index + 1] + [
                value for key, value in keywords.items()
                if key in {"args", "cmd", "command", "executable", "path", "file"}]
            assert not any(external_command(command) for command in commands), (
                path, node.lineno, "external oracle command")
        if name in ("import_module", "__import__"):
            modules = args[:1] + [value for key, value in keywords.items() if key == "name"]
            for module in modules:
                value = static_string(module)
                assert value is None or value.split(".")[0] not in MODULES, (
                    path, node.lineno, "external oracle import")


def check(root):
    read_data(root)
    frozen = json.loads((root / "tools/golden/historical-files.json").read_text())
    for name, receipt in frozen.items():
        path = root / name
        assert path.suffix in (".json", ".md", ".tlsf") and receipt["reason"], name
        assert hashlib.sha256(path.read_bytes()).hexdigest() == receipt["sha256"], (name, "frozen documentation/data changed")
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
            # Only hash-bound, non-executable data can bypass text scanning.
            if relative in frozen or relative == DATA_FILE:
                continue
            assert not FORBIDDEN.search(text), (relative, "external oracle reference", FORBIDDEN.search(text)[0] if FORBIDDEN.search(text) else "")
            count += 1
    for path in (root / "meson.build", root / "meson.options", root / "README.md"):
        assert not FORBIDDEN.search(path.read_text()), path
    print(f"external-oracle guard: {count} files; {len(frozen)} explicit frozen provenance/data entries")


if __name__ == "__main__":
    check(Path(sys.argv[1]).resolve())
