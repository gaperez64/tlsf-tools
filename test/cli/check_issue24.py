#!/usr/bin/env python3
"""Offline pinned-corpus regression; large strategy proofs are a separate check."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from fetch_syntcomp_issue24 import CASES, git_blob_sha


def main():
    p = argparse.ArgumentParser()
    p.add_argument("solver")
    p.add_argument("corpus", type=Path)
    p.add_argument("case", type=int)
    p.add_argument("--memory-out", type=Path)
    args = p.parse_args()
    upstream, digest = CASES[args.case]
    path = args.corpus / Path(upstream).name
    data = path.read_bytes()
    assert git_blob_sha(data) == digest
    lines = data.decode("ascii").splitlines()
    header = list(map(int, lines[0].split()[1:]))
    expected = [(937, 26, 110, 1, 801)] * 3 + [(708, 52, 78, 1, 578), (978, 52, 78, 1, 848)]
    assert tuple(header[:5]) == expected[args.case] and not any(header[5:])
    _, ni, nl, no, ng = header[:5]
    symbols = {}
    for line in lines[1 + ni + nl + no + ng:]:
        if line == "c": break
        if line.startswith("i"):
            index, name = line.split(" ", 1)
            symbols[int(index[1:])] = name
    controls = [i for i, name in symbols.items() if name.startswith("controllable_")]
    assert len(controls) == [2, 4, 8, 24, 24][args.case]
    resets = [int(line.split()[2]) if len(line.split()) > 2 else 0
              for line in lines[1 + ni:1 + ni + nl]]
    assert not any(resets)
    nodes = 4194304 if args.memory_out else 33554432
    command = [str(Path(args.solver).resolve()), f"--oxidd-nodes={nodes}",
               "--oxidd-cache=4194304", str(path)]
    with tempfile.TemporaryDirectory() as directory:
        usage = Path(directory) / "usage.json"
        timer = Path("/usr/bin/time")
        measured = ([str(timer), "-q", "-o", str(usage), "-f",
                     '{"rss_kib":%M,"seconds":%e}'] + command) if timer.exists() else command
        proc = subprocess.run(measured, capture_output=True, timeout=120, check=False)
        record = {"case": upstream, "nodes": nodes, "cache": 4194304,
                  "returncode": proc.returncode, "stderr": proc.stderr.decode(),
                  "controls": controls, "resets": resets,
                  "output_literal": int(lines[1 + ni + nl]),
                  "usage": json.loads(usage.read_text()) if usage.exists() else None}
    assert proc.returncode in (0, 1, 2), record
    if not args.memory_out:
        assert proc.returncode == (0 if args.case < 3 else 1), record
    elif proc.returncode != 2:
        assert proc.returncode == (0 if args.case < 3 else 1), record
    if proc.returncode == 0: assert proc.stdout.startswith(b"aag ")
    else: assert not proc.stdout
    if args.memory_out:
        args.memory_out.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record))


if __name__ == "__main__":
    main()
