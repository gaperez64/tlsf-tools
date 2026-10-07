#!/usr/bin/env python3
"""Check the source layout rules (issue #40) against a configured build.

1. Each source file is compiled into exactly one target; the exceptions are
   the test-only fault-injection builds and their shared probe main.
2. The installed tlsf headers are exactly include/tlsf/ (the GR(1) headers
   only under native_gr1), plus the generated version.h.
3. (Enforced by compilation: test/api sees include/ only.)
4. Nothing in src/lib includes a tool header, and nothing in include/tlsf
   includes a header outside include/tlsf.

usage: check_layout.py SOURCE_ROOT BUILD_DIR
"""

import collections
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1]).resolve()
build = pathlib.Path(sys.argv[2]).resolve()
while not (build / "meson-info/intro-targets.json").is_file() and build.parent != build:
    build = build.parent
info = build / "meson-info"
errors = []

targets = json.loads((info / "intro-targets.json").read_text())
compiled = collections.defaultdict(list)
for target in targets:
    for group in target["target_sources"]:
        for source in group.get("sources", []):
            path = pathlib.Path(source).resolve()
            if root in path.parents:
                relative = path.relative_to(root)
                if "subprojects" not in relative.parts:
                    compiled[relative].append(target["name"])
for source, owners in sorted(compiled.items()):
    fault_owners = {
        pathlib.Path("src/lib/gr1_reduction.cc"): {"native_contract_api", "acacia-bonsai-native-test"},
        pathlib.Path("test/unit/reduction_contract_hooks.cc"): {"acacia-bonsai-native-test"},
        pathlib.Path("src/lib/gr1_lift.cc"): {"native_lift_api", "native_both_api",
                                               "native_real_both_api", "env_rank_fault_probe"},
        pathlib.Path("src/lib/gr1_typed.cc"): {"native_lift_api", "native_both_api",
                                                "native_real_both_api", "env_rank_fault_probe"},
        pathlib.Path("src/lib/gr1_env_lift.cc"): {"native_both_api",
                                                   "native_real_both_api", "env_rank_fault_probe"},
        pathlib.Path("test/unit/env_rank_probe.cpp"): {"env_rank_fault_probe"},
    }
    extra = sorted(set(owners) - fault_owners.get(source, set()))
    if len(extra) > 1:
        errors.append(f"rule 1: {source} compiled into {sorted(owners)}")

options = {option["name"]: option["value"] for option in
           json.loads((info / "intro-buildoptions.json").read_text())}
gr1 = {"gr1_check.h", "gr1_lift.h", "gr1_oxidd.h", "gr1_reduction.h",
       "oxidd_options.h", "safety_oxidd.h"}
public = {path.name for path in (root / "include/tlsf").iterdir()
          if path.suffix in (".h", ".hpp")}
native_gr1 = options.get("native_gr1", options.get("tlsf-tools:native_gr1"))
expected = (public if native_gr1 == "enabled" else public - gr1)
expected |= {"version.h"}
plan = json.loads((info / "intro-install_plan.json").read_text())
installed = {pathlib.PurePath(entry["destination"]).name
             for section in ("headers", "targets")
             for entry in plan[section].values()
             if entry["destination"].startswith("{includedir}/tlsf/")}
if installed != expected:
    errors.append(f"rule 2: installed-only {sorted(installed - expected)}, "
                  f"not installed {sorted(expected - installed)}")

include = re.compile(r'^\s*#\s*include\s*"([^"]+)"', re.MULTILINE)
tool_headers = {path.name for path in (root / "src/tools").rglob("*.h")}
for path in sorted((root / "src/lib").iterdir()):
    for name in include.findall(path.read_text()) if path.is_file() else ():
        if name in tool_headers:
            errors.append(f"rule 4: {path.relative_to(root)} includes {name}")
for path in sorted((root / "include/tlsf").iterdir()):
    for name in include.findall(path.read_text()):
        if not (name.startswith("tlsf/") and
                (name[5:] in public or name == "tlsf/version.h")):
            errors.append(f"rule 4: {path.relative_to(root)} includes {name}")

for error in errors:
    print(error, file=sys.stderr)
sys.exit(1 if errors else 0)
