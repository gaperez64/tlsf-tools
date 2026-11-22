"""Exercise the real semantic audit using only tiny core Lean modules."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR", Path.cwd())) as tmp:
    work = Path(tmp)
    shutil.copy(root / "proofs/lean-toolchain", work)
    shutil.copy(root / "proofs/audit-axioms.lean", work)
    env = {**os.environ, "LEAN_PATH": str(work), "LEAN_NUM_THREADS": "1"}

    def lean(*args):
        return subprocess.run(["lean", "-j1", "-DElab.async=false", *args],
                              cwd=work, env=env, capture_output=True, text=True,
                              timeout=120)

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
            result = lean("-o", module + ".olean", module + ".lean")
            assert result.returncode == 0, (source, result.stdout, result.stderr)
        result = lean("--run", "audit-axioms.lean", "AuditFixture")
        output = result.stdout + result.stderr
        if forbidden is None:
            assert result.returncode == 0 and "2 library modules" in output, output
        else:
            assert result.returncode != 0 and "forbidden axioms" in output, output
            assert forbidden in output, output

print("Semantic axiom audit accepts core proofs and rejects native_decide, sorry and new axioms")
