"""Keep normalization help and rejected legacy options consistent."""

import subprocess
import sys


normalize = sys.argv[1]
result = subprocess.run([normalize, "--help"], text=True, capture_output=True)
assert result.returncode == 0 and "--norm-soundness" in result.stderr, result
assert "--check-equivalence" not in result.stderr, result
for option in ("--check-equivalence", "--check-equivalence=auto",
               "--check-equivalence=spot", "--check-equivalence=off"):
    result = subprocess.run([normalize, option], text=True, capture_output=True)
    assert result.returncode == 1 and "unknown option" in result.stderr, result
