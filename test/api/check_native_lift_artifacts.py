#!/usr/bin/env python3
"""Compare off-mode API artifacts, optionally against an incumbent-built probe.

Build native_lift_artifacts.cpp against the incumbent headers/library without
TLSF_TYPED_ROLES_API, then supply it with --incumbent-probe. Proofs, sidecars,
evidence and verdict records must match byte-for-byte. Only checker wall/CPU
timing fields are excluded from the separate checker JSON comparison.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


FILES = {
    "game.aag", "certificate.aag", "certificate.json", "policy.aag",
    "policy.json", "check.json", "evidence.json", "record.txt",
}
ROUTES = ("pure-R", "combined-R", "combined-U")
APIS = ("legacy", "v1", "v2-null", "v2-off")


def untimed_check(path):
    data = path.read_bytes()
    value = json.loads(data)
    assert isinstance(value["elapsed_seconds"], (int, float)), path
    # Region checks use a top-level timer; policy checks time each method.
    timers = re.compile(rb'("(?:time_seconds|elapsed_seconds)":)-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?')
    return timers.sub(rb'\g<1>0', data)


def compare(expected, actual):
    assert {path.name for path in expected.iterdir()} == FILES, expected
    assert {path.name for path in actual.iterdir()} == FILES, actual
    for name in sorted(FILES - {"check.json"}):
        assert (expected / name).read_bytes() == (actual / name).read_bytes(), (
            expected, actual, name,
        )
    assert untimed_check(expected / "check.json") == untimed_check(actual / "check.json"), (
        expected, actual, "check.json",
    )
    evidence = json.loads((actual / "evidence.json").read_bytes())
    assert "r_typed_roles" not in evidence, actual
    assert "r_typed_roles" not in evidence.get("global_knobs", {}), actual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--probe", type=Path, required=True)
    parser.add_argument("--fixture", type=Path, required=True)
    parser.add_argument("--incumbent-probe", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="native-lift-artifacts-") as temporary:
        root = Path(temporary)
        current = root / "current"
        subprocess.run([str(args.probe.resolve()), str(current), str(args.fixture.resolve())],
                       check=True, timeout=120)
        for route in ROUTES:
            for api in APIS:
                compare(current / route / "legacy", current / route / api)
        if args.incumbent_probe:
            incumbent = root / "incumbent"
            subprocess.run([str(args.incumbent_probe.resolve()), str(incumbent),
                            str(args.fixture.resolve())], check=True, timeout=120)
            for route in ROUTES:
                for api in APIS:
                    baseline_api = api if api in ("legacy", "v1") else "v1"
                    compare(incumbent / route / baseline_api, current / route / api)
            print("Incumbent/off-mode artifact bytes match: 3 routes, 4 API variants")
        else:
            print("Off-mode artifact bytes match: 3 routes, legacy/v1/v2-null/v2-off APIs")


if __name__ == "__main__":
    main()
