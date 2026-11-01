#!/usr/bin/env python3
"""Restore independently confirmed accepted rows after the bounded Lean audit.

This does not record native output as a new oracle. It restores the exact
pre-narrowing artifacts already archived in provenance, verifies every source
monitor has a passing Buchi translation receipt, and preserves the phase-1
content hashes. Run offline in the task's memory-limited scope, after building
the reduction with general admission enabled.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
GOLD = ROOT / "test/fixtures/golden"
SCRATCH = ROOT / "build-scratch-t/translation"


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest()


def write_records(path, rows):
    path.write_text("[\n" + ",\n".join(json.dumps(r, separators=(",", ":")) for r in rows) + "\n]\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    args = parser.parse_args()
    build = args.build.resolve()
    report = json.loads((GOLD / "translation/report.json").read_text())
    proof = json.loads((GOLD / "translation/provenance.json").read_text())
    assert report["zero_failures"] and not report["failures"] and report["partial_set"] is None
    assert report["timeout_seconds"] == 17 and report["fresh_run"]
    payload = (GOLD / "translation/hashes.tsv").read_bytes()
    assert hashlib.sha256(payload).hexdigest() == proof["hashes_sha256"]
    receipts = {line.split("\t", 2)[2]: line.split("\t", 2)[1]
                for line in payload.decode().splitlines()}
    inventory = json.loads((SCRATCH / "inventory.json").read_text())
    manifest = json.loads((GOLD / "provenance.json").read_text())
    native = manifest["native-reduction"]
    candidates = native["phase2_declines"]
    assert len(candidates) == 14, "this recovery is for the fourteen archived phase-2 declines"
    patches, retained = [], []
    general = {r["path"]: r for r in inventory["coverage"]["general"]}
    for patch in candidates:
        name, mode = patch["case"].rsplit(":", 1)
        source = "test/fixtures/cases/" + name
        assert hashlib.sha256((ROOT / source).read_bytes()).hexdigest() == proof["corpus_sources"][source]
        result = subprocess.run([str(build / "test/api/native_reduction"), str(ROOT / source),
                                 mode, str(SCRATCH / "recovered-game")],
                                capture_output=True, text=True, timeout=60)
        if result.returncode == 3:
            assert general[source]["status"] == 3, (patch["case"], result.stderr)
            retained.append(patch)
            continue
        assert result.returncode == 0, (patch["case"], result.stderr)
        patches.append(patch)
        reached = [c for c in inventory["cases"] if source in c["sets"].get("corpus", [])]
        assert reached, (source, "no inventoried constructors")
        for case in reached:
            def request(admission):
                return " ".join(["TV1", "buchi", admission, str(len(case["names"])),
                                 *case["names"], case["prefix"]])
            assert any(receipts.get(request(a)) == "pass" for a in ("default", "general")), case

    rows = json.loads((GOLD / "native-reduction.json").read_text())
    by_case = {p["case"]: p for p in patches}
    restored, indices = [], {}
    i = 0
    while i < len(rows):
        label, value = rows[i]
        case = value[0] + ":" + value[1] if label == "status" else None
        indices[i] = len(restored)
        if case in by_case:
            patch = by_case[case]
            assert rows[i:i + 2] == patch["after"]
            restored.extend(copy.deepcopy(patch["before"]))
            i += 2
        else:
            restored.append(rows[i])
            i += 1
    for update in native.get("pruning_source_updates", []):
        update["records"] = [[indices[index], label] for index, label in update["records"]]
    historical = copy.deepcopy(restored)
    for update in native.get("pruning_source_updates", []):
        for index, label in update["records"]:
            field = historical[index][1]
            if label == ".json":
                field = field["source_origin_metadata"]
            assert field["source_sha256"] == update["after_sha256"]
            field["source_sha256"] = update["before_sha256"]
    phase1, i = [], 0
    remaining = {p["case"]: p for p in retained}
    while i < len(historical):
        label, value = historical[i]
        case = value[0] + ":" + value[1] if label == "status" else None
        if case in remaining:
            patch = remaining[case]
            assert historical[i:i + 2] == patch["after"]
            phase1.extend(patch["before"])
            i += 2
        else:
            phase1.append(historical[i])
            i += 1
    assert digest(phase1) == native["phase1_sha256"], "historical accepted artifacts changed"
    native["pre_pruning_sources_sha256"] = digest(historical)
    native["phase2_declines"] = retained
    native["general_admission_recoveries"] = {
        "translation_hashes_sha256": proof["hashes_sha256"], "cases": patches}
    native["sha256"] = digest(restored)
    native["native_status_counts"] = dict(Counter(str(r[1][-1]) for r in restored if r[0] == "status"))

    decomposition = json.loads((GOLD / "decomposition.json").read_text())
    suite = manifest["decomposition"]
    changes = suite["phase2_changes"]
    for patch in changes:
        assert decomposition[patch["index"]] == patch["after"]
        decomposition[patch["index"]] = patch["before"]
    assert digest(decomposition) == suite["phase1_sha256"]
    suite["phase2_changes"] = []
    suite["general_admission_recoveries"] = {
        "translation_hashes_sha256": proof["hashes_sha256"], "cases": changes}
    suite["sha256"] = digest(decomposition)
    write_records(GOLD / "native-reduction.json", restored)
    write_records(GOLD / "decomposition.json", decomposition)
    (GOLD / "provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"restored {len(patches)} native cases and {len(changes)} admission verdicts; "
          f"{len(retained)} native declines retained; phase-1 hashes preserved")


if __name__ == "__main__":
    main()
