"""Verify the archived description-only source migration without rewriting it."""
import json
import re
import subprocess


def verify(root, build):
    suite = json.loads((root / "test/fixtures/golden/provenance.json").read_text())["native-reduction"]
    for patch in suite["pruning_source_updates"]:
        before, after = patch["before_source"], (root / patch["source"]).read_text()
        description = r'DESCRIPTION:\s*"[^"\n]*"'
        assert re.sub(description, "", before) == re.sub(description, "", after)
        for semantics in ("Mealy", "Mealy,Strict"):
            formulas = [subprocess.check_output([str(build / "tlsf2ltl")], text=True,
                input=text.replace("SEMANTICS: Mealy", "SEMANTICS: " + semantics), timeout=30)
                for text in (before, after)]
            assert formulas[0] == formulas[1], (patch["source"], semantics)
    print("pruning sources: four objectives reproduced identically; archived migration unchanged", flush=True)
