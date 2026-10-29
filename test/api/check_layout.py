#!/usr/bin/env python3
"""Check the source layout rules (issue #40) against a configured build.

1. Each source file is compiled into exactly one target; the exceptions are
   the test-only fault-injection builds and their shared probe main.
2. The installed tlsf headers are exactly include/tlsf/, plus the generated version.h.
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
info = pathlib.Path(sys.argv[2]).resolve() / "meson-info"
errors = []

targets = json.loads((info / "intro-targets.json").read_text())
compiled = collections.defaultdict(list)
for target in targets:
    # A parent project may also compile the exported fault-injection sources.
    # Audit targets defined by this project, as in a standalone build.
    if not pathlib.Path(target["defined_in"]).resolve().is_relative_to(root):
        continue
    for group in target["target_sources"]:
        for source in group.get("sources", []):
            path = pathlib.Path(source).resolve()
            if root in path.parents and "subprojects" not in path.relative_to(root).parts:
                compiled[path.relative_to(root)].append(target["name"])
for source, owners in sorted(compiled.items()):
    fault_owners = {
        pathlib.Path("src/lib/arena.c"): {"objective_alloc"},
        pathlib.Path("src/tools/tlsf2ltl/main.c"): {"objective-cli"},
        pathlib.Path("src/tools/tlsfresidual/main.c"): {"residual-fault"},
        pathlib.Path("src/tools/tlsftemplates/main.c"): {"template-fault"},
        pathlib.Path("test/unit/research_fault.c"): {"residual-fault", "template-fault"},
        pathlib.Path("src/lib/gr1_reduction.cc"): {"native_contract_api"},
        pathlib.Path("src/lib/gr1_lift.cc"): {"native_lift_api", "native_both_api",
                                               "native_real_both_api", "env_rank_fault_probe"},
        pathlib.Path("src/lib/gr1_env_lift.cc"): {"native_both_api",
                                                   "native_real_both_api", "env_rank_fault_probe"},
        pathlib.Path("test/unit/env_rank_probe.cpp"): {"env_rank_fault_probe"},
    }
    extra = sorted(set(owners) - fault_owners.get(source, set()))
    if len(extra) > 1:
        errors.append(f"rule 1: {source} compiled into {sorted(owners)}")

public = {path.name for path in (root / "include/tlsf").iterdir()
          if path.suffix in (".h", ".hpp")}
expected = public.copy()
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
