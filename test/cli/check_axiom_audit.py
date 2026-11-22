"""Exercise the real semantic audit using only tiny core Lean modules."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR", Path.cwd())) as tmp:
    work = Path(tmp)
    shutil.copy(root / "proofs/audit-axioms.lean", work)
    env = {**os.environ, "LEAN_PATH": str(work), "LEAN_NUM_THREADS": "1",
           "ELAN_TOOLCHAIN": (root / "proofs/lean-toolchain").read_text().strip()}

    def lean(*args):
        return subprocess.run(["lean", "-j1", "-DElab.async=false", *args],
                              cwd=work, env=env, capture_output=True, text=True,
                              timeout=120)

    def compile_module(module):
        result = lean("-o", module + ".olean", module + ".lean")
        assert result.returncode == 0, (module, result.stdout, result.stderr)

    # Put declarations outside the library namespace; membership comes from modules.
    # Include an unreferenced child module, a private proof, and a non-theorem axiom.
    for source, forbidden in (
        ("import Init\ntheorem ordinary : 2 + 2 = 4 := by decide\n", None),
        ("import Init\nnoncomputable def classical (p : Prop) : Decidable p := Classical.propDecidable p\n", None),
        ("import Init\nprivate theorem native : 2 + 2 = 4 := by native_decide\n", "_native"),
        ("import Init\nprivate theorem unfinished : False := by sorry\n", "sorryAx"),
        ("import Init\naxiom unchecked : Nat\n", "unchecked"),
    ):
        (work / "AuditFixture.lean").write_text("import Init\n")
        (work / "AuditFixture").mkdir(exist_ok=True)
        (work / "AuditFixture/Unused.lean").write_text(source)
        for module in ("AuditFixture", "AuditFixture/Unused"):
            compile_module(module)
        result = lean("--run", "audit-axioms.lean", "AuditFixture.Unused")
        output = result.stdout + result.stderr
        if forbidden is None:
            assert result.returncode == 0 and "1 library modules" in output, output
        else:
            assert result.returncode != 0 and "forbidden axioms" in output, output
            assert forbidden in output, output

    # Executables collide in one import environment but pass in separate processes.
    for module in ("First", "Second"):
        (work / f"AuditFixture/{module}.lean").write_text(
            "import Init\ndef main : IO Unit := pure ()\n")
        compile_module(f"AuditFixture/{module}")
    result = lean("--run", "audit-axioms.lean", "AuditFixture.First", "AuditFixture.Second")
    assert result.returncode != 0 and "already contains 'main'" in result.stderr, result
    for module in ("AuditFixture", "AuditFixture.First", "AuditFixture.Second"):
        result = lean("--run", "audit-axioms.lean", module)
        assert result.returncode == 0 and "Audited" in result.stdout, result
    (work / "AuditFixture/Second.olean").unlink()
    result = lean("--run", "audit-axioms.lean", "AuditFixture.Second")
    assert result.returncode != 0, "missing executable artifact must fail its partition"

    # A root-only build accepts a stale orphan; explicit targets must reject it.
    (work / "lakefile.toml").write_text(
        'name = "auditFixture"\ndefaultTargets = ["AuditFixture"]\n'
        '[[lean_lib]]\nname = "AuditFixture"\n')
    unused = work / "AuditFixture/Unused.lean"
    unused.write_text("import Init\ntheorem unused : True := True.intro\n")

    def build(*modules):
        return subprocess.run(["lake", "--rehash", "build", *modules],
                              cwd=work, env=env, capture_output=True, text=True, timeout=120)

    result = build("AuditFixture", "AuditFixture.Unused")
    assert result.returncode == 0, (result.stdout, result.stderr)
    stamp = unused.stat()
    unused.write_text("INVALID_LEAN\n")
    os.utime(unused, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
    result = build()
    assert result.returncode == 0, (result.stdout, result.stderr)
    result = build("AuditFixture", "AuditFixture.Unused")
    assert result.returncode != 0 and "Unused.lean" in result.stdout + result.stderr, result

print("Semantic audit fixtures pass: pinned toolchain, isolated executables, import errors and stale sources")
