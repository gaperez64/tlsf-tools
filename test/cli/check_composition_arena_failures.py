"""Sweep every composition arena allocation through each research CLI."""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


name, healthy, fault = sys.argv[1:]
options = ["--certify", "--solve", "--check"] if name == "tlsftemplates" else []


def run(tool, fixture, nth=None):
    env = dict(os.environ)
    env.pop("TLSF_TEST_COMPOSITION_ALLOC", None)
    env.pop("TLSF_TEST_COMPOSITION_ARENA", None)
    if nth is not None:
        env["TLSF_TEST_COMPOSITION_ARENA"] = str(nth)
    return subprocess.run([tool, *options, str(fixture)], text=True,
                          capture_output=True, env=env, timeout=15)


with tempfile.TemporaryDirectory(prefix="compose-arena-") as scratch:
    for body in ["G(a -> p); G(b -> p);",
                 "G(a -> p); G(b -> p); G(c -> p);",
                 "G(a -> !p); G(b -> !p);", "F p;", "F G p;",
                 "G(p <-> a);"]:
        fixture = Path(scratch) / "composition.tlsf"
        inputs = "a; b; c;" if "c ->" in body else "a; b;"
        fixture.write_text("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                           "INPUTS { " + inputs + " } OUTPUTS { p; } GUARANTEES { "
                           + body + " } }")
        normal = run(healthy, fixture)
        assert normal.returncode == 0 and normal.stdout, normal
        probe = run(fault, fixture, 0)
        assert probe.returncode == 0 and probe.stdout == normal.stdout, probe
        count = int(re.search(r"composition allocations: (\d+)", probe.stderr)[1])
        assert count >= 3, probe
        for n in range(1, count + 1):
            failed = run(fault, fixture, n)
            assert failed.returncode == 1, failed
            assert f"injected composition arena failure {n}\n" in failed.stderr, failed
            assert "composition result: null arena_failed=1\n" in failed.stderr, failed
            assert "out of memory" in failed.stderr, failed
            if name == "tlsftemplates":
                assert "composition:" not in failed.stdout, failed
            elif name == "tlsfbenchgraph":
                assert "\tfail\t" in failed.stdout and "\tok\t" not in failed.stdout, failed
            else:
                assert not failed.stdout, failed
        probe = run(fault, fixture, count + 1)
        assert probe.returncode == 0 and probe.stdout == normal.stdout, probe
        assert "injected" not in probe.stderr, probe
