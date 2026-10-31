"""Check reference provenance, content binding, and the owner's golden size cap."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1]) / "test/fixtures/golden"
manifest = json.loads((root / "provenance.json").read_text())
for path in root.glob("*.json"):
    if path.name in ("tool-versions.json", "skipped.json", "provenance.json"):
        continue
    suite = manifest[path.stem]
    assert "independent_checks" in suite and "native_snapshot" in suite, path
    if path.stem in ("native-reduction", "native-lift"):
        assert suite["status"] == "independently confirmed", path
        assert suite["cases"] == (436 if path.stem == "native-reduction" else 13)
        assert suite["native_status_counts"]["0"] > 0
    records = json.loads(path.read_text())
    digest = hashlib.sha256(json.dumps(records, separators=(",", ":")).encode()).hexdigest()
    assert suite["sha256"] == digest, (path, "unconfirmed payload")
    if path.stem in ("native-reduction", "native-lift"):
        label = "status" if path.stem == "native-reduction" else "lift"
        cases = [row[1] for row in records if row[0] == label]
        assert len(cases) == suite["cases"], path
        assert dict(Counter(str(row[-1]) for row in cases)) == suite["native_status_counts"], path
for name, digest in manifest["dpa"]["files_sha256"].items():
    assert hashlib.sha256((root / "dpa" / name).read_bytes()).hexdigest() == digest, name
size = sum(p.stat().st_size for p in root.rglob("*") if p.is_file())
assert size <= 4_629_524, ("golden directory exceeds its original size", size)
print(f"golden provenance checked; {size} bytes <= 4629524-byte cap")
