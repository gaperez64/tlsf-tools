#!/usr/bin/env python3
"""TOOLS ONLY: REQUIRES Spot; build the historical full-language DPA oracle.

After compiling the current checkout, run inside the memory-limited scope:
  python3 tools/golden/build_legacy.py build
This reuses the configured compiler/dependency flags and never changes Meson.
"""
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
build = Path(sys.argv[1]).resolve()
spot_prefix = Path(sys.argv[2]).expanduser().resolve() if len(sys.argv) > 2 else Path.home() / "spot-2.16-install"
environment = dict(os.environ, PKG_CONFIG_PATH=str(spot_prefix / "lib/pkgconfig"))
cflags = shlex.split(subprocess.check_output(["pkg-config", "--cflags", "libspot"], env=environment, text=True))
libs = shlex.split(subprocess.check_output(["pkg-config", "--libs", "libspot"], env=environment, text=True))
entries = json.loads((build / "compile_commands.json").read_text())
entry = next(e for e in entries if e["file"].endswith("test/unit/dpa_equivalence.cpp"))
source = str(root / "tools/golden/legacy_dpa_equivalence.cpp")
obj = "golden-legacy.o"
args = shlex.split(entry["command"])
old_obj = args[args.index("-o") + 1]
args = [source if a == entry["file"] else obj if a == old_obj else obj + ".d" if a == old_obj + ".d" else a for a in args]
args.extend(cflags)
subprocess.run(args, cwd=build, check=True, timeout=120)
commands = subprocess.check_output(["ninja", "-t", "commands", "test/unit/dpa_equivalence"],
                                   cwd=build, text=True, timeout=30).splitlines()
link = next(shlex.split(line) for line in reversed(commands)
            if " -o test/unit/dpa_equivalence " in line)
link = [obj if a == old_obj else "golden-legacy" if a == "test/unit/dpa_equivalence" else a for a in link]
link.extend([*libs, "-Wl,-rpath," + str(spot_prefix / "lib")])
# The manual executable lives at the build root, so the original target's
# $ORIGIN-relative paths need absolute equivalents for subproject libraries.
library_dirs = set()
for argument in link:
    library = Path(argument)
    library = library if library.is_absolute() else build / library
    if (".so" in argument or ".dylib" in argument) and library.is_file():
        library_dirs.add(str(library.parent.resolve()))
link.extend("-Wl,-rpath," + directory for directory in sorted(library_dirs))
subprocess.run(link, cwd=build, check=True, timeout=120)
print(build / "golden-legacy")
