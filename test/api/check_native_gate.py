#!/usr/bin/env python3
"""Assert an OxiDD-only build keeps native GR(1) out of libtlsf/install.

Run after compiling: the archive's defined symbols are what a consumer links,
including any objects folded in from tlsf-oxidd.
"""

import json
import pathlib
import subprocess
import sys

build = pathlib.Path(sys.argv[1]).resolve()
plan = json.loads((build / "meson-info/intro-install_plan.json").read_text())
installed = {pathlib.PurePath(entry["destination"]).name
             for section in ("headers", "targets")
             for entry in plan[section].values()}
gr1_headers = {"gr1_oxidd.h", "gr1_check.h", "gr1_reduction.h", "gr1_lift.h",
               "safety_oxidd.h", "oxidd_options.h"}
assert not gr1_headers & installed, gr1_headers & installed

archive = next(pathlib.Path(path) for path in plan["targets"]
               if path.endswith("/libtlsf.a"))
listing = subprocess.run(["nm", "--defined-only", "-g", str(archive)],
                         check=True, capture_output=True, text=True).stdout
defined = {line.split()[-1] for line in listing.splitlines()
           if len(line.split()) == 3}
# One entry point from each of gr1_service.c, gr1_check.c, gr1_oxidd.c and
# safety_oxidd.c.
for forbidden in ("tlsf_gr1_validate_game", "tlsf_gr1_check",
                  "solve_gr1_oxidd", "solve_safety_oxidd"):
    assert forbidden not in defined, forbidden
