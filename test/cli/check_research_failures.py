"""Require a healthy extraction and a handled failure at the reviewed boundary."""
import subprocess
import sys

mode, healthy, fixture, *extra = sys.argv[1:]
options = ["--certify", "--solve", "--format", extra[1]] if mode == "template" else []


def run(tool, args):
    return subprocess.run([tool, *args, fixture], text=True, capture_output=True)


normal = run(healthy, options)
assert normal.returncode == 0 and normal.stdout, normal
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
