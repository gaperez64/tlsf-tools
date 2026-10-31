#!/usr/bin/env python3
"""Read-only native GR(1) inventory: BUILD OUTPUT.json.

Run in a memory-limited systemd scope. Uses the native API client with its
16 MiB artifact / 10,000 monitor-state caps and a 20-second process deadline.
The inventory includes every checked-in TLSF source under bench/ and test/.
Before/after measurements must use the same source checkout and input list.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("build", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    build = args.build.resolve()
    paths = sorted(set(root.glob("bench/**/*.tlsf")) |
                   set(root.glob("test/**/*.tlsf")))
    rows = []
    with tempfile.TemporaryDirectory(dir=build) as temp:
        prefix = Path(temp) / "result"
        for path in paths:
            row = {"path": str(path.relative_to(root)),
                   "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            try:
                result = subprocess.run(
                    [str(build / "test/api/native_reduction"), str(path),
                     "exact", str(prefix)], capture_output=True, text=True,
                    timeout=20)
                row.update(status=result.returncode, reason=result.stderr.strip())
                if result.returncode == 0:
                    data = json.loads(prefix.with_suffix(".json").read_text())
                    row["monitors"] = [
                        {key: monitor[key] for key in
                         ("conjunct", "construction_formula", "state_count", "mp_class")}
                        for monitor in data["monitors"]]
            except subprocess.TimeoutExpired:
                row["status"] = "timeout"
            rows.append(row)
            print(row["path"], row["status"], flush=True)
    args.output.write_text(json.dumps(rows, indent=2) + "\n")


if __name__ == "__main__":
    main()
