"""Require a healthy extraction and a handled failure at the reviewed boundary."""
import os
import re
import subprocess
import sys

mode, healthy, fixture, *extra = sys.argv[1:]
options = ["--certify", "--solve", "--format", extra[1]] if mode == "template" else []


def run(tool, args, nth=0):
    return subprocess.run([tool, *args, fixture], text=True, capture_output=True,
                          env={**os.environ, "TLSF_TEST_COMPOSITION_ALLOC": str(nth)})


normal = run(healthy, options)
assert normal.returncode == 0 and normal.stdout, normal
if mode == "composition":
    probe = run(extra[0], options)
    assert probe.returncode == 0 and probe.stdout == normal.stdout, probe
    count = int(re.search(r"composition allocations: (\d+)", probe.stderr)[1])
    assert count >= 12, probe
    for n in range(1, count + 1):
        failed = run(extra[0], options, n)
        assert failed.returncode == 1 and not failed.stdout, failed
        assert f"injected composition allocation failure {n}\n" in failed.stderr, failed
        assert "out of memory" in failed.stderr, failed
    probe = run(extra[0], options, count + 1)
    assert probe.returncode == 0 and probe.stdout == normal.stdout, probe
    assert "injected" not in probe.stderr, probe
    sys.exit(0)
if mode == "io":
    failed = run(healthy, ["--output", "/dev/full"])
    marker = "failed"
else:
    failed = run(extra[0], options)
    marker = ("injected residual_cluster_keys allocation failure" if mode == "cluster"
              else "injected formula_str allocation failure")
assert failed.returncode == 1, failed
assert marker in failed.stderr, failed
if mode == "cluster":
    assert "c clusters 1" in normal.stdout and "\nfalse\n" in normal.stdout, normal
    assert "c clusters" not in failed.stdout, failed
elif mode == "template":
    assert "emission failed" in failed.stderr, failed
    assert "cl 0 \n" not in failed.stdout, failed
