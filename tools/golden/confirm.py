"""Offline-only independent gates for reduction/lift recordings.

The legacy comparators and reducer come from tlsf-tools 7b44d9f
(origin/main when phase 1 began); the lift comparator also reports missing
reference evidence. No timeouts count as confirmation.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
import re
from pathlib import Path
import sys
import tempfile

INDEPENDENT = {"native-reduction", "native-lift"}


class Confirmation:
    def __init__(self, name, options):
        self.name, self.options = name, options
        self.cases = []
        if options is None or not options.bindings_site:
            raise RuntimeError(f"{name}: --bindings-site is required for independent confirmation")
        self.directory = Path(tempfile.mkdtemp(prefix="golden-confirm-", dir=options.build))
        sys.path.insert(0, str(options.bindings_site))
        import spot
        assert spot.version() == "2.16", spot.version()
        import buddy
        self.buddy = buddy
        if not buddy.bdd_isrunning():
            buddy.bdd_init(2_000_000, 100_000)
        self.runtime = {"spot_version": spot.version(),
                        "libspot_sha256": hashlib.sha256((options.spot / "lib/libspot.so").read_bytes()).hexdigest(),
                        "libbddx_sha256": hashlib.sha256((options.spot / "lib/libbddx.so").read_bytes()).hexdigest()}
        if name == "native-reduction":
            import legacy_reduction
            self.legacy = legacy_reduction
            self.sources = {p.name: p for p in [
                *sorted((Path(__file__).resolve().parents[2] / "test/fixtures/cases").glob("*.tlsf")),
                *legacy_reduction.generated(self.directory)]}
        else:
            if not options.oracle_root:
                raise RuntimeError("native-lift: --oracle-root is required for the retired prototype")
            import legacy_lift
            self.legacy = legacy_lift
            package = options.oracle_root / "benchmarking/gr1-par2-20260923/oracle"
            assert (package / "acacia_lift/runner.py").is_file(), package
            sys.path.insert(0, str(package))
            sources = sorted((package / "acacia_lift").rglob("*.py"))
            self.runtime["prototype_tree_sha256"] = hashlib.sha256(b"".join(
                str(p.relative_to(package)).encode() + b"\0" + p.read_bytes() for p in sources)).hexdigest()
            self.runtime["prototype_environment_adjustment"] = "local libbddx hash allowlist with tested conservative 1024-variable cap"
            self.env = dict(os.environ, PYTHONPATH=os.pathsep.join((
                str(package), str(options.bindings_site))),
                LD_LIBRARY_PATH=str(options.spot / "lib"))

    def reduction(self, records):
        label, semantics, status = records[0][1]
        source = self.sources[label]
        prefix = self.directory / "reference"
        command = [sys.executable, str(Path(__file__).with_name("legacy_monitor.py")),
                   str(source), "--semantics", semantics,
                   "--output", str(prefix.with_suffix(".aag")),
                   "--provenance-out", str(prefix.with_suffix(".json"))]
        for tool in ("tlsf2ltl", "tlsf2tlsf", "tlsfinfo"):
            command += ["--" + tool, str(self.options.build / tool)]
        from regenerate import run
        reference = run(command, timeout=60, env=dict(os.environ,
            PYTHONPATH=str(self.options.bindings_site),
            LD_LIBRARY_PATH=str(self.options.spot / "lib")))
        assert reference.returncode in (0, 2, 3), (label, semantics, reference.stderr)
        assert (status == 0) == (reference.returncode == 0), (
            label, semantics, "INDEPENDENT DISAGREEMENT", status, reference.returncode, reference.stderr)
        if status == 0:
            native = dict(records[1:])
            aag = native[".aag"]
            other = prefix.with_suffix(".aag").read_text()
            if self.legacy.game_functions(aag) != self.legacy.game_functions(other):
                assert self.legacy.games_bisimilar(aag, other), (label, semantics, "AAG language/ownership")
            symbols = native[".symbols"].splitlines()
            assert symbols[0] == "tlsf-tools.game-symbol-map.v1"
            assert symbols[1] == hashlib.sha256(aag.encode()).hexdigest()
            assert symbols[2:] == self.legacy.symbol_entries(
                Path(str(prefix.with_suffix(".aag")) + ".symbols"), other.encode())
            # The comparator consumes fields while checking the legacy projection.
            projected = self.legacy.legacy_provenance(json.loads(json.dumps(native[".json"])))
            assert projected == json.loads(prefix.with_suffix(".json").read_text()), (label, semantics, "provenance")
        self.cases.append({"case": label + ":" + semantics, "status": status})

    def lift(self, records):
        label, status = records[0][1]
        source = self.current_source
        # source/artifacts are copied by Recorder while the native case exists.
        work = self.directory / label
        args = argparse.Namespace(native=self.options.build / "test/api/native_lift",
            seconds=12, bindings_python=Path(sys.executable),
            bindings_site=self.options.bindings_site, tools_build=self.options.build)
        result = self.legacy.compare_case(source, work, args, self.env,
                                         expected_success=status == 0)
        reference = json.loads((work / "reference-evidence.json").read_text())
        assert reference["route"] != "hard-timeout", (label, reference)
        assert (status == 0) == (reference["route"] == "lifted-certified"), (
            label, "INDEPENDENT DISAGREEMENT", status, reference)
        if status == 0:
            from test_native_lift_differential import stable
            native = dict(records[1:])
            assert native["evidence"] == stable(result), (label, "recorded evidence changed")
            for suffix in (".game.aag", ".cert.aag", ".policy.aag"):
                assert native[suffix] == Path(str(work / "native") + suffix).read_text()
        else:
            assert reference.get("lifting_failure"), (label, "unconfirmed decline", reference)
            native_stage = re.search(r"stage=([^ ]+)", dict(records[1:])["decline"]).group(1)
            assert native_stage == reference["lifting_failure"]["stage"], (label, "INDEPENDENT DISAGREEMENT: decline stage", reference)
        self.cases.append({"case": label, "status": status})

    def confirm(self, records):
        if self.name == "native-reduction":
            self.reduction(records)
        else:
            self.lift(records)

    def provenance(self):
        assert self.cases, "no independently confirmed cases"
        return {"status": "independently confirmed", "cases": len(self.cases),
                "native_status_counts": dict(Counter(str(c["status"]) for c in self.cases)),
                "reference": "Spot 2.16 Python reducer" if self.name == "native-reduction" else "retired acacia_lift prototype",
                "comparator_revision": "7b44d9f", "runtime": self.runtime,
                "independent_checks": (["supported/declined disposition", "circuit functions or reachable bisimulation", "ownership and symbol map", "legacy provenance projection"]
                    if self.name == "native-reduction" else ["lifted/declined disposition and decline stage", "seed values", "role partition", "predicate arities", "proof method and verdict", "certificate and policy Boolean functions"]),
                "native_snapshot": (["AAG serialization", "extended typed provenance fields", "metadata", "decline diagnostics and exact exit codes"]
                    if self.name == "native-reduction" else ["AAG serialization", "game AAG", "evidence hashes and exact role signatures", "decline diagnostic spelling"]),
                "reference_revision": ("7b44d9f" if self.name == "native-reduction" else "b615c3c4c2dc1a2b13c035b62b115c0d1148a977"),
                "comparator_sha256": hashlib.sha256(Path(self.legacy.__file__).read_bytes()).hexdigest(),
                "case_status_sha256": hashlib.sha256(json.dumps(self.cases, sort_keys=True).encode()).hexdigest()}
