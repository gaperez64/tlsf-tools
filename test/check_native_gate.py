#!/usr/bin/env python3
"""Assert an OxiDD-only build keeps native GR(1) out of libtlsf/install."""

import json
import pathlib
import subprocess
import sys

build = pathlib.Path(sys.argv[1]).resolve()
targets = json.loads(subprocess.check_output(
    ["meson", "introspect", "--targets", str(build)]))
libraries = [target for target in targets if target["name"] == "tlsf"]
assert len(libraries) == 1
sources = " ".join(str(source) for group in libraries[0]["target_sources"]
                   for source in group.get("sources", []))
for forbidden in ("src/native/gr1_service.c", "src/native/gr1_check.c",
                  "src/gr1_oxidd.c", "src/safety_oxidd.c"):
    assert forbidden not in sources, forbidden
plan = json.loads((build / "meson-info/intro-install_plan.json").read_text())
headers = next(value for key, value in plan["install_subdirs"].items()
               if key.endswith("/include/tlsf"))
excluded = set(headers["exclude_files"])
assert {"native.h", "gr1_oxidd.h", "gr1_check.h", "oxidd_options.h",
        "oxidd_common.h"} <= excluded
