"""Offline-only source-hash refresh for PR #95's description-only changes."""
import copy
import hashlib
import json
import re


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest()


def refresh(root, destination, options, run):
    path = destination / "native-reduction.json"
    records = json.loads(path.read_text())
    manifest_path = destination / "provenance.json"
    manifest = json.loads(manifest_path.read_text())
    suite = manifest["native-reduction"]
    if "pruning_source_updates" in suite:
        # This migration is deliberately one-time; ordinary regeneration of
        # the new pruning corpus must leave the frozen reduction data alone.
        assert suite["sha256"] == digest(records)
        return
    original = copy.deepcopy(records)
    assert suite["sha256"] == digest(original)
    updates = []
    for name in ("cluster_assume", "cluster_prune"):
        relative = "test/fixtures/cases/" + name + ".tlsf"
        before = run(["git", "show", "16cb10f9c620085fe655da0831bf52bccba638f2:" + relative], check=True).stdout
        after = (root / relative).read_text()
        description = r'DESCRIPTION:\s*"[^"\n]*"'
        assert before != after
        assert re.sub(description, "", before) == re.sub(description, "", after), relative
        old_hash = hashlib.sha256(before.encode()).hexdigest()
        new_hash = hashlib.sha256(after.encode()).hexdigest()
        for semantics in ("Mealy", "Mealy,Strict"):
            formulas = [run([options.build / "tlsf2ltl"], check=True,
                            input=text.replace("SEMANTICS: Mealy", "SEMANTICS: " + semantics)).stdout.strip()
                        for text in (before, after)]
            result = run([options.spot / "bin/ltlfilt", "--equivalent-to=" + formulas[0],
                          "-f", formulas[1]], check=True)
            assert result.stdout.strip(), (relative, semantics, result.stderr)
        locations = []
        for index, (label, value) in enumerate(records):
            if label not in (".json", ".metadata.json"):
                continue
            field = value.get("source_origin_metadata") if label == ".json" else value
            if field and field.get("source_sha256") == old_hash:
                field["source_sha256"] = new_hash
                locations.append([index, label])
        assert len(locations) == 4, (relative, locations)
        updates.append({"source": relative, "before_source": before,
                        "before_sha256": old_hash, "after_sha256": new_hash,
                        "records": locations})
    suite["pre_pruning_sources_sha256"] = digest(original)
    suite["pruning_source_updates"] = updates
    suite["pruning_source_confirmation"] = "Spot 2.16 ltlfilt equivalence, ordinary and strict; only DESCRIPTION text differs"
    suite["sha256"] = digest(records)
    # Every comparison above completes before either file is changed.
    path.write_text("[\n" + ",\n".join(json.dumps(row, separators=(",", ":"))
                                      for row in records) + "\n]\n")
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print("PR #95 source hashes: 8 fields refreshed; 4 reference equivalences confirmed", flush=True)


if __name__ == "__main__":
    import argparse
    from pathlib import Path
    from regenerate import ROOT, DEST, run

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--spot", type=Path, required=True)
    options = parser.parse_args()
    options.build = options.build.resolve()
    options.spot = options.spot.expanduser().resolve()
    version = run([options.spot / "bin/ltlfilt", "--version"], check=True).stdout.splitlines()[0]
    assert version.endswith("ltlfilt (spot) 2.16"), version
    refresh(ROOT, DEST, options, run)
