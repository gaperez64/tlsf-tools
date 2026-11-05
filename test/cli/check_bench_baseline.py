#!/usr/bin/env python3
"""Baseline and check modes use the last measurement for duplicate basenames."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

bench = Path(sys.argv[1]).resolve()
bash = sys.argv[3] if len(sys.argv) > 3 else "bash"
with tempfile.TemporaryDirectory(dir=sys.argv[2], prefix="bench baseline ") as temporary:
    work = Path(temporary)
    script = work / "bench.sh"
    shutil.copy2(bench, script)
    for directory in ("early", "late"):
        specs = work / "specs" / directory
        specs.mkdir(parents=True)
        (specs / "foo.tlsf").write_text("unused by stub\n")
    binaries = work / "bin"
    binaries.mkdir()
    tool = binaries / "tlsf2ltl"
    tool.write_text("#!/bin/sh\nexit 0\n")
    tool.chmod(0o755)
    # Control elapsed times without sleeps or dependence on machine speed.
    date = binaries / "date"
    date.write_text(
        '#!/bin/sh\nhead -n 1 "$BENCH_CLOCK"\n'
        'sed \'1d\' "$BENCH_CLOCK" > "$BENCH_CLOCK.next"\n'
        'mv "$BENCH_CLOCK.next" "$BENCH_CLOCK"\n'
    )
    date.chmod(0o755)
    clock = work / "clock"
    baseline = work / "baseline.tsv"
    baseline.write_text("# spec\tms\tkib\nfoo\t10\t1000000\n")
    env = dict(os.environ, PATH=f"{binaries}:{os.environ['PATH']}",
               BENCH_CLOCK=str(clock))
    command = [bash, str(script), "--build", str(binaries), "--runs", "1"]

    def run(mode, early_ms, late_ms):
        clock.write_text(f"0\n{early_ms * 1000000}\n0\n{late_ms * 1000000}\n")
        return subprocess.run([*command, mode], env=env, capture_output=True,
                              text=True, timeout=30)

    for early_ms, late_ms, expected in ((10, 1000, 1), (1000, 10, 0)):
        result = run("--check", early_ms, late_ms)
        assert result.returncode == expected, result
        assert f"10 -> {late_ms}" in result.stdout, result
        assert ("REGRESSIONS DETECTED" in result.stderr) == bool(expected), result

    result = run("--baseline", 10, 1000)
    assert result.returncode == 0, result
    rows = [line.split("\t") for line in baseline.read_text().splitlines()[1:]]
    assert len(rows) == 2 and rows[0] == rows[1], rows
    assert rows[0][:2] == ["foo", "1000"], rows
print("benchmark duplicate basenames use the last measurement")
