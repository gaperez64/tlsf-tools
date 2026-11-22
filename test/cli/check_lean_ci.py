"""Check Lean CI filtering and shell failure handling without running Lean."""
import itertools
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
real_git = shutil.which("git")
with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR", Path.cwd())) as tmp:
    work = Path(tmp)
    bin_dir = work / "bin"
    bin_dir.mkdir()
    git = bin_dir / "git"
    git.write_text("""#!/usr/bin/env python3
import json, os, sys
if sys.argv[1] == 'cat-file':
    sys.exit(int(os.environ.get('BASE_MISSING', '0')))
assert sys.argv[1:5] == ['diff', '--name-only', '--find-renames', '-z'], sys.argv
reverse = sys.argv[5] == 'HEAD'
assert sys.argv[5:] == (['HEAD', 'a' * 40] if reverse else ['a' * 40, 'HEAD'])
for path in json.loads(os.environ.get('REVERSE_PATHS' if reverse else 'CHANGED_PATHS', '[]')):
    sys.stdout.buffer.write(path.encode() + b'\\0')
sys.exit(int(os.environ.get('REVERSE_STATUS' if reverse else 'DIFF_STATUS', '0')))
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
                 "proofs/TlsfProofs/Δ.lean", "proofs/a name with spaces.lean",
                 "proofs/a quoted \"name\"\nwith newline.lean",
                 "tools/golden/restriction_audit.lean", ".github/workflows/lean.yml",
                 ".github/scripts/lean-needed.sh", ".github/scripts/lean-gate.sh",
                 "test/cli/check_axiom_audit.py", "test/cli/check_lean_ci.py"):
        filtered(["README.md", path], "true")
    filtered(["proofs/deleted.lean", "archive/moved.lean"], "true")
    filtered(["archive/moved.lean"], "true", REVERSE_PATHS='["proofs/deleted.lean"]')
    filtered(["proofs/new.lean"], "true", GITHUB_EVENT_NAME="push")
    filtered(["src/lib/dpa.c"], GITHUB_EVENT_NAME="push")
    for before in ("", "0" * 40):
        filtered(expected="true", GITHUB_EVENT_NAME="push", BASE_SHA=before)
    filtered(expected="true", BASE_MISSING="1")
    for event in ("workflow_dispatch", "schedule"):
        filtered(expected="true", GITHUB_EVENT_NAME=event)
    for failure in ("DIFF_STATUS", "REVERSE_STATUS"):
        result = subprocess.run(detector, env={**env, failure: "42",
                                              "CHANGED_PATHS": '["proofs/test.lean"]'},
                                capture_output=True)
        assert result.returncode == 42, "either git diff error must fail the job"

    # Real Git quotes unusual paths without -z and reports only rename destinations.
    unusual = ("Δ.lean", "with spaces.lean", 'quoted"name.lean', "with\nnewline.lean")
    moves = [(f"proofs/{name}", f"archive/{name}") for name in unusual]
    moves += [(after, before) for before, after in moves.copy()]
    moves += [("tools/golden/Δ\n audit.lean", "archive/audit.lean"),
              ("archive/audit.lean", "tools/golden/Δ\n audit.lean")]
    for index, (before, after) in enumerate(moves):
        repo = work / f"rename-{index}"
        repo.mkdir()

        def git_command(*args):
            return subprocess.check_output([real_git, *args], cwd=repo)

        git_command("init", "--quiet")
        git_command("config", "user.email", "test@example.invalid")
        git_command("config", "user.name", "Lean CI regression")
        git_command("config", "commit.gpgsign", "false")
        git_command("config", "core.quotePath", "true")
        git_command("config", "diff.renames", "false")
        old, new = repo / before, repo / after
        old.parent.mkdir(parents=True, exist_ok=True)
        new.parent.mkdir(parents=True, exist_ok=True)
        old.write_text("identical contents for rename detection\n")
        git_command("add", ".")
        git_command("commit", "--quiet", "-m", "Base")
        base = git_command("rev-parse", "HEAD").decode().strip()
        old.rename(new)
        git_command("add", "-A")
        git_command("commit", "--quiet", "-m", "Rename")
        assert git_command("diff", "--name-status", "--find-renames", base, "HEAD").startswith(b"R100")
        result = subprocess.run(detector, cwd=repo, env={**os.environ,
                                "GITHUB_EVENT_NAME": "pull_request", "BASE_SHA": base},
                                capture_output=True, text=True)
        assert result.returncode == 0 and result.stdout.strip() == "true", (
            before, after, result.stdout, result.stderr)

    # Branch protection depends on this result, including failed/empty detector outputs.
    for detected, needed, lean in itertools.product(
            ("success", "failure", "cancelled", "skipped"),
            ("true", "false", "", "invalid"),
            ("success", "failure", "cancelled", "skipped")):
        expected = detected == "success" and (
            (needed == "true" and lean == "success") or
            (needed == "false" and lean in ("success", "skipped")))
        result = subprocess.run(["bash", str(root / ".github/scripts/lean-gate.sh")],
                                env={**os.environ, "DETECTOR_RESULT": detected,
                                     "LEAN_NEEDED": needed, "LEAN_RESULT": lean},
                                capture_output=True)
        assert (result.returncode == 0) == expected, (detected, needed, lean)

    # Replace timeout, not Lean: no command inside the build script can run Lean.
    log = work / "commands.jsonl"
    timeout = bin_dir / "timeout"
    timeout.write_text("""#!/usr/bin/env python3
import json, os, sys
with open(os.environ['COMMAND_LOG'], 'a') as log:
    log.write(json.dumps([sys.argv[1:], os.environ['LEAN_NUM_THREADS']]) + '\\n')
if 'build' in sys.argv:
    from pathlib import Path
    for target in sys.argv[sys.argv.index('build') + 1:]:
        source = Path(target.replace('.', '/') + '.lean')
        if source.exists() and 'INVALID_LEAN' in source.read_text():
            sys.exit(9)
if '--run' in sys.argv and sys.argv[-1] == os.environ.get('FAIL_AUDIT_MODULE'):
    sys.exit(73)
sys.exit(73 if os.environ.get('FAIL_STEP') in sys.argv[1:] else 0)
""")
    timeout.chmod(0o755)
    proofs = work / "proofs"
    (proofs / "TlsfProofs").mkdir(parents=True)
    (proofs / "TlsfProofs.lean").write_text("import Init\n")
    nested = proofs / "TlsfProofs/Nested"
    nested.mkdir()
    unimported = nested / "Unused.lean"
    unimported.write_text("import Init\n")
    for name in ("First", "Second"):
        (proofs / f"TlsfProofs/{name}.lean").write_text("def main : IO Unit := pure ()\n")
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
        audit = next(i for i, (args, _) in enumerate(commands) if "audit-axioms.lean" in args)
        assert audit > max(i for i, (args, _) in enumerate(commands) if "build" in args)
        modules = {"TlsfProofs", "TlsfProofs.First", "TlsfProofs.Second", "TlsfProofs.Nested.Unused"}
        assert set(builds[-1][4:]) == modules
        partitions = [args[args.index("--run") + 2:] for args, _ in commands if "--run" in args]
        assert len(partitions) == len(modules)
        assert {tuple(partition) for partition in partitions} == {(module,) for module in modules}
        assert all(not arg.endswith("_audit.lean")
                   for args, _ in commands[:audit] for arg in args)
    status, commands = check(FAIL_STEP="TlsfProofs.Restriction")
    assert status == 73 and commands[-1][0][-1] == "TlsfProofs.Restriction"
    status, commands = check(FAIL_STEP="build")
    assert status == 73 and len(commands) == 1
    status, commands = check(FAIL_STEP="../tools/golden/restriction_audit.lean")
    assert status == 73
    status, commands = check(FAIL_STEP="audit-axioms.lean")
    assert status == 73 and commands[-1][0][-1] == "TlsfProofs"
    status, commands = check(FAIL_AUDIT_MODULE="TlsfProofs.Second")
    assert status == 73 and "--run" in commands[-1][0]
    assert commands[-1][0][-1] == "TlsfProofs.Second"
    assert any("--run" in args and args[-1] == "TlsfProofs.First" for args, _ in commands)
    unimported.write_text("INVALID_LEAN\n")
    status, commands = check()
    assert status == 9 and "build" in commands[-1][0]
    assert not any("--run" in args for args, _ in commands)
    unimported.write_text("import Init\n")
    for placeholder in ("sorry", "admit", "axiom unchecked : True"):
        (proofs / "Bad.lean").write_text(placeholder + "\n")
        status, commands = check()
        assert status == 1 and not commands, placeholder

print("Lean CI paths/renames, 64 gate outcomes, cache-independent checks and failures passed")
