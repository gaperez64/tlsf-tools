#!/usr/bin/env python3
"""Offline checks for ordering variant configuration and result grouping."""

import json
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import measure_tlsfsolve_memory as measure


def expect_error(function, text):
    try:
        function()
    except ValueError as error:
        assert text in str(error), error
    else:
        raise AssertionError(f"expected ValueError containing {text!r}")


def main():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        solver = root / "tlsfsolve"
        solver.write_bytes(b"test solver")
        order = root / "order.txt"
        order.write_text("tlsfsolve-order-v1 2\n1\n0\n")
        config = root / "variants.json"
        config.write_text(json.dumps({
            "schema": 1,
            "variants": [
                {"label": "baseline", "solver": str(solver), "args": []},
                {"label": "custom", "solver": str(solver),
                 "args": ["--oxidd-order-file", "order.txt",
                          "--oxidd-build-plan=gates"]},
            ],
        }))
        variants = measure.load_variants(None, config)
        assert list(variants) == ["baseline", "custom"]
        assert variants["baseline"]["variable_order"] == "input-first"
        assert variants["custom"]["variable_order"] == "custom"
        assert variants["custom"]["order_file"] == measure.fingerprint(order)
        assert variants["custom"]["args"][0].startswith("--oxidd-order-file=/")

        for argument in ("--game-profile=legacy-safety", "--oxidd-nodes",
                         "--oxidd-cache=256", "--oxidd-gc=auto",
                         "--oxidd-gc-threshold=80", "--oxidd-transitions=eager",
                         "--realizability-only"):
            expect_error(
                lambda argument=argument: measure.normalize_variant_args(
                    [argument], root),
                "campaign-owned")
        expect_error(
            lambda: measure.normalize_variant_args(["game.aag"], root),
            "input path")

        game = root / "game.aag"
        game.write_bytes(b"aag 0 0 0 1 0\n0\n")
        input_manifest = root / "inputs.json"
        input_manifest.write_text(json.dumps({
            "schema": 1,
            "source_commit": "pinned",
            "cases": [{
                "path": "family/game.aag", "file": "game.aag",
                "git_blob_sha1": measure.git_blob_sha(game.read_bytes()),
                "sha256": measure.fingerprint(game)["sha256"],
                "expected_status": None,
            }],
        }))
        inputs, commit, manifest_fingerprint = measure.load_inputs(
            root, input_manifest, None)
        assert commit == "pinned" and len(inputs) == 1
        assert inputs[0]["expected_status"] is None
        assert manifest_fingerprint == measure.fingerprint(input_manifest)

        missing_hash = json.loads(input_manifest.read_text())
        del missing_hash["cases"][0]["sha256"]
        input_manifest.write_text(json.dumps(missing_hash))
        expect_error(
            lambda: measure.load_inputs(root, input_manifest, None),
            "invalid input manifest case")

    common = {
        "instance": "example.aag", "input_sha256": "input", "variant": "v",
        "binary_sha256": "binary", "variable_order": "state-first",
        "order_file_sha256": None, "build_plan": "gates", "plan_version": 1,
        "profile": "legacy-safety", "nodes": 1024, "cache": 256,
        "gc": "auto", "gc_threshold": 80, "transitions": "eager",
        "mode": "full",
    }
    rows = measure.summarize([
        {**common, "status": "REALIZABLE", "rss_kib": 100, "elapsed_s": 1.0},
        {**common, "status": "SOLVER_ERROR", "rss_kib": 900,
         "elapsed_s": 9.0},
    ])
    assert len(rows) == 1
    assert rows[0]["completed_runs"] == 1
    assert rows[0]["rss_kib"]["median"] == 100
    assert rows[0]["elapsed_s"]["median"] == 1.0
    assert rows[0]["failures"] == [{
        "status": "SOLVER_ERROR", "runs": 1,
        "rss_kib": {"min": 900, "median": 900, "max": 900},
        "elapsed_s": {"min": 9.0, "median": 9.0, "max": 9.0},
    }]


if __name__ == "__main__":
    main()
