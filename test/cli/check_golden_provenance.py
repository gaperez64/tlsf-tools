"""Pin every golden file and enforce the owner's 4.4 MB directory cap."""
import hashlib
from pathlib import Path
import sys

root = Path(sys.argv[1]) / "test/fixtures/golden"
manifest = root / "MANIFEST.sha256"
expected = {}
for line in manifest.read_text().splitlines():
    digest, name = line.split("  ", 1)
    if len(digest) != 64 or set(digest) - set("0123456789abcdef"):
        sys.exit(f"invalid SHA-256 for {name}")
    if name in expected:
        sys.exit(f"duplicate golden manifest entry: {name}")
    expected[name] = digest

files = {str(p.relative_to(root)): p for p in root.rglob("*")
         if p.is_file() and p != manifest}
if files.keys() != expected.keys():
    sys.exit(f"golden file set differs: missing={sorted(expected.keys() - files.keys())}, "
             f"unlisted={sorted(files.keys() - expected.keys())}")
for name, path in files.items():
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected[name]:
        sys.exit(f"golden SHA-256 mismatch: {name}")

size = manifest.stat().st_size + sum(p.stat().st_size for p in files.values())
if size > 4_400_000:
    sys.exit(f"golden directory exceeds 4.4 MB: {size} bytes")
print(f"golden provenance checked; {len(files)} files; {size} bytes <= 4400000-byte cap")
