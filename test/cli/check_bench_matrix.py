#!/usr/bin/env python3
"""A Meson setup failure must fail benchmark matrix mode, with no obsolete option."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile

bench = Path(sys.argv[1]).resolve()
with tempfile.TemporaryDirectory(dir=sys.argv[2]) as temporary:
    work = Path(temporary)
    (work / "trivial.tlsf").write_text("unused by the failed build\n")
    meson = work / "meson"
    meson.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > "$MATRIX_SETUP_ARGS"\nexit 42\n')
    meson.chmod(0o755)
    args_file = work / "setup-args"
    result = subprocess.run(
        ["bash", str(bench), "--matrix", str(work), "--runs", "3"],
        env=dict(os.environ, PATH=f"{work}:{os.environ['PATH']}",
                 MATRIX_SETUP_ARGS=str(args_file)),
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode != 0, result
    assert "failed to build matrix configuration" in result.stderr, result
    assert "-Doxidd=" not in args_file.read_text(), args_file.read_text()
print("benchmark matrix propagates setup failures")
