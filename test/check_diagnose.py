#!/usr/bin/env python3
"""Diagnostic artifact, signal, timeout, and verdict-only contracts."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    runner = Path(__file__).resolve().parents[1] / "scripts/diagnose_tlsfsolve.py"
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        fake = root / "solver"
        fake.write_text("""#!/usr/bin/env python3
import os, signal, sys, time
from pathlib import Path
if '--version' in sys.argv:
    print('tlsfsolve test diagnostics=yes'); sys.exit(0)
mode = Path(sys.argv[-1]).name
if mode in ('term', 'wait'):
    print('TLSFSOLVE_TRACE {"phase":"fixpoint","event":"op_begin","operation":"substitute","unknown":1}', file=sys.stderr, flush=True)
    print('TLSFSOLVE_TRACE {', file=sys.stderr, flush=True)
    if mode == 'term': os.kill(os.getpid(), signal.SIGTERM)
    time.sleep(30)
elif mode == 'verdict': print('REALIZABLE', file=sys.stderr)
elif mode == 'loss': print('UNREALIZABLE', file=sys.stderr); sys.exit(1)
else: print('aag 0 0 0 0 0')
""")
        fake.chmod(0o755)
        for mode in ("win", "loss", "verdict", "term", "wait"):
            source = root / mode
            source.write_text("fixture")
            out = root / (mode + "-out")
            command = [sys.executable, str(runner), "--solver", str(fake),
                       "--input", str(source), "--out", str(out)]
            if mode == "wait": command += ["--timeout", "0.1"]
            if mode == "verdict": command += ["--", "--realizability-only"]
            proc = subprocess.run(command, capture_output=True, text=True, timeout=5)
            assert proc.returncode == (124 if mode == "wait" else 0), proc.stderr
            summary = json.loads((out / "summary.json").read_text())
            assert summary["stdout_file"] == ("strategy.aag" if mode == "win" else "stdout.txt")
            if mode in ("term", "wait"):
                assert summary["unfinished_operation"]["operation"] == "substitute"
                assert summary["malformed_trace_lines"] == ["{"]
            if mode == "term": assert summary["signal"] == 15 and not summary["timed_out"]
            if mode == "wait": assert summary["timed_out"] and summary["signal"] is None
            if sys.platform.startswith("linux"):
                assert summary["resource_usage"]["peak_rss_kib"] > 0
        fake.write_text(fake.read_text().replace("diagnostics=yes", "diagnostics=no"))
        proc = subprocess.run([sys.executable, str(runner), "--solver", str(fake),
                               "--input", str(root / "win"), "--out", str(root / "release")],
                              capture_output=True, text=True)
        assert proc.returncode == 2 and "no diagnostics" in proc.stderr
    print("6 diagnostic contracts passed")


if __name__ == "__main__":
    main()
