"""Check Lean CI filtering and shell failure handling without running Lean."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR", Path.cwd())) as tmp:
    work = Path(tmp)
    bin_dir = work / "bin"
    bin_dir.mkdir()
    git = bin_dir / "git"
    git.write_text("""#!/usr/bin/env python3
import json, os, sys
if sys.argv[1] == 'cat-file':
    sys.exit(int(os.environ.get('BASE_MISSING', '0')))
assert sys.argv[1:5] == ['diff', '--name-only', '--no-renames', '-z'], sys.argv
for path in json.loads(os.environ['CHANGED_PATHS']):
    sys.stdout.buffer.write(path.encode() + b'\\0')
sys.exit(int(os.environ.get('DIFF_STATUS', '0')))
""")
    git.chmod(0o755)
    env = {**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}",
           "GITHUB_EVENT_NAME": "pull_request", "BASE_SHA": "a" * 40,
           "CHANGED_PATHS": "[]"}
    detector = ["bash", str(root / ".github/scripts/lean-needed.sh")]

    def filtered(paths=(), expected="false", **overrides):
        result = subprocess.run(detector, env={**env, "CHANGED_PATHS": json.dumps(paths),
                                              **overrides}, capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        assert result.stdout.strip() == expected, (paths, overrides, result.stdout)

    filtered()
    filtered(["src/lib/dpa.c", "README.md", "tools/golden/dag-cases.json"])
    for path in ("proofs/TlsfProofs/Restriction.lean", "proofs/lean-toolchain",
                 "proofs/lakefile.toml", "proofs/check.sh", "proofs/README.md",
                 "proofs/a quoted \"name\"\nwith newline.lean",
                 "tools/golden/restriction_audit.lean", ".github/workflows/lean.yml",
                 ".github/scripts/lean-needed.sh"):
        filtered(["README.md", path], "true")
    filtered(["proofs/deleted.lean", "archive/moved.lean"], "true")
    filtered(["proofs/new.lean"], "true", GITHUB_EVENT_NAME="push")
    filtered(["src/lib/dpa.c"], GITHUB_EVENT_NAME="push")
    for before in ("", "0" * 40):
        filtered(expected="true", GITHUB_EVENT_NAME="push", BASE_SHA=before)
    filtered(expected="true", BASE_MISSING="1")
    for event in ("workflow_dispatch", "schedule"):
        filtered(expected="true", GITHUB_EVENT_NAME=event)
    result = subprocess.run(detector, env={**env, "DIFF_STATUS": "42"},
                            capture_output=True)
    assert result.returncode == 42, "git diff errors must fail the job"

    # Replace timeout, not Lean: no command inside the build script can run Lean.
    log = work / "commands.jsonl"
    timeout = bin_dir / "timeout"
    timeout.write_text("""#!/usr/bin/env python3
import json, os, sys
with open(os.environ['COMMAND_LOG'], 'a') as log:
    log.write(json.dumps([sys.argv[1:], os.environ['LEAN_NUM_THREADS']]) + '\\n')
sys.exit(73 if os.environ.get('FAIL_STEP') in sys.argv[1:] else 0)
""")
    timeout.chmod(0o755)
    proofs = work / "proofs"
    (proofs / "TlsfProofs").mkdir(parents=True)
    (proofs / "TlsfProofs.lean").write_text("import Init\n")
    goldens = work / "tools/golden"
    goldens.mkdir(parents=True)
    for name in (root / "tools/golden").glob("*_audit.lean"):
        (goldens / name.name).write_text("import Init\n")
    shutil.copy(root / "proofs/check.sh", proofs / "check.sh")
    # A restored cache must not suppress either builds or direct elaborations.
    (proofs / ".lake").mkdir()
    (proofs / ".lake/Cached.lean").write_text("sorry\n")
    build_env = {**env, "COMMAND_LOG": str(log)}
    build_env.pop("LEAN_NUM_THREADS", None)

    def check(**overrides):
        log.write_text("")
        result = subprocess.run(["bash", str(proofs / "check.sh")],
                                env={**build_env, **overrides}, capture_output=True)
        commands = [json.loads(line) for line in log.read_text().splitlines()]
        return result.returncode, commands

    for threads in ("1", "4"):
        status, commands = check(**({} if threads == "1" else {"LEAN_NUM_THREADS": threads}))
        assert status == 0
        assert all(actual == threads for _, actual in commands)
        builds = [args for args, _ in commands if "build" in args]
        assert builds and all(args[2:4] == ["--rehash", "build"] for args in builds)
        assert sum("TlsfProofs/Restriction.lean" in args for args, _ in commands) == 1
        assert sum(any(arg.endswith("_audit.lean") for arg in args)
                   for args, _ in commands) == len(list(goldens.glob("*_audit.lean")))
    status, commands = check(FAIL_STEP="TlsfProofs.Restriction")
    assert status == 73 and commands[-1][0][-1] == "TlsfProofs.Restriction"
    status, commands = check(FAIL_STEP="build")
    assert status == 73 and len(commands) == 1
    status, commands = check(FAIL_STEP="../tools/golden/restriction_audit.lean")
    assert status == 73
    for placeholder in ("sorry", "admit", "axiom unchecked : True"):
        (proofs / "Bad.lean").write_text(placeholder + "\n")
        status, commands = check()
        assert status == 1 and not commands, placeholder

print("Lean CI event/path filters, cache-independent checks, placeholders and failures passed")
