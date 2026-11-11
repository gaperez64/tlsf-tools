"""Read-only golden assertions. Regeneration lives exclusively in tools/golden."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "fixtures" / "golden"
SCOPING = ROOT.parents[2] / "tools/analysis/tlsf-scoping-110.json"


class Golden:
    def __init__(self, name):
        self.name = name
        self.records = json.loads((ROOT / (name + ".json")).read_text())
        ledger = json.loads(SCOPING.read_text())
        # Apply receipts to a private copy; historical payloads stay byte-exact.
        patches = (ledger["record_replacements"].get(name, []) +
                   ledger["precedence110j"]["record_replacements"].get(name, []))
        for patch in sorted(patches, key=lambda patch: patch["index"], reverse=True):
            index = patch["index"]
            assert self.records[index:index + len(patch["before"])] == patch["before"]
            self.records[index:index + len(patch["before"])] = patch["after"]
        self.position = 0

    def source(self, path):
        """Source hook retained by read-only verification harnesses."""

    def enabled(self, label):
        skipped = json.loads((ROOT / "skipped.json").read_text())
        return not any(row.get("suite") == self.name and row.get("case") == label for row in skipped)

    def timeout(self, label):
        raise AssertionError(f"{self.name}: unexpected timeout: {label}")

    def check(self, label, value):
        expected = self.records[self.position]
        self.position += 1
        value = json.loads(json.dumps(value))
        assert expected == [label, value], (self.name, self.position - 1, label)

    def verdict(self, formula, inputs, outputs, finite=False, moore=False):
        record = self.records[self.position]
        self.position += 1
        assert record[:2] == ["verdict", [formula, inputs, outputs, finite, moore]], record
        return record[2]

    def artifacts(self, directory):
        directory = Path(directory)
        actual = {p.name: p.read_text() for p in sorted(directory.iterdir()) if p.is_file()}
        label, historical = self.records[self.position]
        assert label == "artifacts"
        # Frozen driver programs are historical data, bound by the provenance
        # hash. Current drivers are exercised by check_compose_solver.py.
        # Formula bytes and controller exports still compare exactly. Match a
        # renamed formula artifact by cluster stem, never by backend name.
        expected = {}
        for name, value in historical.items():
            if name == "compose.sh":
                continue
            if name not in actual and name.startswith("cluster."):
                name = name.rsplit(".", 1)[0] + ".formula"
                assert name in actual, (self.name, "missing formula artifact", name)
            assert name not in expected, (self.name, "ambiguous historical artifact", name)
            expected[name] = value
        actual.pop("compose.sh", None)
        assert actual == expected, (self.name, self.position, "stable exported artifacts")
        self.position += 1

    def language(self, formula, names, words, actual):
        self.check("language", [formula, names, words, actual])

    def finish(self):
        assert self.position == len(self.records), (self.name, self.position, len(self.records))
