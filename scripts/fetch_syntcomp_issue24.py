#!/usr/bin/env python3
"""Fetch the pinned SYNTCOMP AIGER files named in tlsf-tools issue #24."""

from __future__ import annotations

import argparse
import hashlib
import sys
import urllib.request
from pathlib import Path


COMMIT = "58e8213f85f395f661b4e23d9fb452c1ffe9015d"
BASE = f"https://raw.githubusercontent.com/SYNTCOMP/benchmarks/{COMMIT}/aiger"

CASES = [
    ("HWMCC12/beemprdcell2f1_c0to1.aag", "ccb2782e9af2e44202fe7e2d7dcda7382648ee13"),
    ("HWMCC12/beemprdcell2f1_c0to3.aag", "8e9eabde1acd7931f40e044926bc9e3aaf38d95b"),
    ("HWMCC12/beemprdcell2f1_c0to7.aag", "e082f5888bd3723bf01297d1da7b63bd3c504b4e"),
    ("driver/driver_c2y.aag", "629610d8c9620b1c4027d89c110c2dc260ef1530"),
    ("driver/driver_c2n.aag", "aa90a930a3a1ce841d6e8f9680644d3cf6cd8a0f"),
]


def git_blob_sha(data: bytes) -> str:
    h = hashlib.sha1()
    h.update(f"blob {len(data)}\0".encode("ascii"))
    h.update(data)
    return h.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--out",
        default="test/data/syntcomp/issue24",
        help="destination directory",
    )
    ns = ap.parse_args()
    out = Path(ns.out)
    out.mkdir(parents=True, exist_ok=True)

    manifest = [
        "path\tblob_sha1\tsha256\tbytes\tupstream_path",
    ]
    for upstream, expected_blob in CASES:
        url = f"{BASE}/{upstream}"
        data = urllib.request.urlopen(url, timeout=30).read()
        got_blob = git_blob_sha(data)
        if got_blob != expected_blob:
            print(
                f"blob mismatch for {upstream}: expected {expected_blob}, got {got_blob}",
                file=sys.stderr,
            )
            return 1
        name = Path(upstream).name
        (out / name).write_bytes(data)
        manifest.append(
            f"{name}\t{got_blob}\t{hashlib.sha256(data).hexdigest()}\t"
            f"{len(data)}\t{upstream}"
        )

    (out / "manifest.tsv").write_text("\n".join(manifest) + "\n", encoding="utf-8")
    (out / "UPSTREAM.md").write_text(
        f"# SYNTCOMP issue #24 corpus\n\n"
        f"Fetched from `SYNTCOMP/benchmarks` at commit `{COMMIT}`.\n"
        "These files are used as external regression/performance witnesses for "
        "gaperez64/tlsf-tools issue #24.\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
