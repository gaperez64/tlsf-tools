"""Read-only golden assertions. Regeneration lives exclusively in tools/golden."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "fixtures" / "golden"


class Golden:
    def __init__(self, name):
        self.name = name
        self.records = json.loads((ROOT / (name + ".json")).read_text())
        self.position = 0

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
        self.check("artifacts", {p.name: p.read_text() for p in sorted(directory.iterdir())
                                  if p.is_file()})

    def language(self, formula, names, words, actual):
        self.check("language", [formula, names, words, actual])

    def finish(self):
        assert self.position == len(self.records), (self.name, self.position, len(self.records))
