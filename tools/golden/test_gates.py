#!/usr/bin/env python3
"""Offline integration check: the real recorder must reject decline-everything.

Requires the same --build/--spot/--bindings-site setup as regeneration, and
must run under its memory-limited scope. Never registered with Meson or CI.
"""
import argparse
from pathlib import Path
import runpy
import sys
import tempfile
import types

import regenerate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("build", "spot", "bindings-site"):
        parser.add_argument("--" + name, type=Path, required=True)
    options = parser.parse_args()
    for key, value in vars(options).items():
        setattr(options, key, value.expanduser().resolve())
    options.oracle_root = None
    regenerate.OPTIONS = options
    with tempfile.TemporaryDirectory(dir=options.build) as temp:
        directory = Path(temp)
        fake_build = directory / "build"
        (fake_build / "test/api").mkdir(parents=True)
        fake = fake_build / "test/api/native_reduction"
        fake.write_text('#!/bin/sh\necho "injected erroneous decline" >&2\nexit 3\n')
        fake.chmod(0o755)
        regenerate.DEST = directory / "golden"
        regenerate.DEST.mkdir()
        target = regenerate.DEST / "native-reduction.json"
        target.write_text("original recording must survive\n")
        original = target.read_bytes()
        module = types.ModuleType("golden")
        module.Golden = regenerate.Recorder
        sys.modules["golden"] = module
        sys.argv = [str(regenerate.ROOT / "test/oracle/test_native_reduction.py"),
                    "--builddir", str(fake_build)]
        try:
            runpy.run_path(sys.argv[0], run_name="__main__")
        except AssertionError as error:
            assert "INDEPENDENT DISAGREEMENT" in str(error), error
            print("decline-everything rejected by independent reference:", error)
        else:
            raise AssertionError("decline-everything mutant was accepted")
        assert target.read_bytes() == original, "unconfirmed results overwrote the golden"
        assert not (regenerate.DEST / "provenance.json").exists()
        unconfirmed = regenerate.Recorder("native-language")
        unconfirmed.check("native-only", "unchecked output")
        try:
            unconfirmed.finish()
        except AssertionError as error:
            assert "missing independent checks" in str(error)
        else:
            raise AssertionError("recording without a required language check was accepted")
        assert not (regenerate.DEST / "native-language.json").exists()
        options.bindings_site = None
        try:
            regenerate.Recorder("native-reduction")
        except RuntimeError as error:
            assert "--bindings-site is required" in str(error)
        else:
            raise AssertionError("recording without a reference was accepted")
    print("offline recording gates: 3 checks passed; no unconfirmed files written")


if __name__ == "__main__":
    main()
