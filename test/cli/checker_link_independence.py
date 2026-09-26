#!/usr/bin/env python3
"""The installed checker must not acquire a GR(1) solve dependency."""

import pathlib
import subprocess
import sys

build = pathlib.Path(sys.argv[1])
checker = pathlib.Path(sys.argv[2])
object_file = build / "src/lib/libtlsf-oxidd.a.p/gr1_check.c.o"


def symbols(*args: str) -> str:
    return subprocess.run(["nm", *args], check=True, capture_output=True,
                          text=True).stdout


assert object_file.is_file(), object_file
assert "tlsf_gr1_check" in symbols(str(object_file))
for path, args in ((object_file, ("-u",)), (checker, ())):
    listing = symbols(*args, str(path))
    assert "solve_gr1_oxidd" not in listing, path
assert "tlsf_gr1_check" in symbols(str(checker))
