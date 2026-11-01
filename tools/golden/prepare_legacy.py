#!/usr/bin/env python3
"""Offline setup for the archived lift reference and Spot 2.16 Python bindings.

Run under the same memory-limited systemd scope as regeneration. No downloads,
Meson registration or CI dependencies. The archive is read from a local Acacia
repository. The reference algorithms are unmodified; only an environment
allowlist gains a conservatively tested 1024-variable cap for this libbddx build.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

PROTOTYPE = "b615c3c4c2dc1a2b13c035b62b115c0d1148a977"
ROOT = Path(__file__).resolve().parents[2]


def run(args, **kwargs):
    return subprocess.run(list(map(str, args)), check=True, timeout=180, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--acacia", type=Path, required=True)
    parser.add_argument("--spot-source", type=Path, required=True)
    parser.add_argument("--spot", type=Path, required=True)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    for name, value in vars(args).items():
        setattr(args, name, value.expanduser().resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    site = args.output / "spot-python"
    (site / "spot").mkdir(parents=True, exist_ok=True)
    source = args.spot_source / "python"
    shutil.copy(source / "buddy.py", site)
    for path in (source / "spot").glob("*.py"):
        shutil.copy(path, site / "spot")
    suffix = subprocess.check_output(["python3-config", "--extension-suffix"], text=True).strip()
    includes = subprocess.check_output(["python3-config", "--includes"], text=True).split()
    for module in ("buddy", "spot/impl"):
        target = site / Path(module).parent / ("_" + Path(module).name + suffix)
        run(["clang++", "-std=c++20", "-O0", "-g0", "-fPIC", "-shared",
             "-DSWIG_TYPE_TABLE=spot", "-I" + str(args.spot / "include"),
             "-I" + str(args.spot_source), *includes,
             source / (module + "_wrap.cxx"), "-o", target,
             "-L" + str(args.spot / "lib"), "-lspot", "-lbddx",
             "-Wl,-rpath," + str(args.spot / "lib")])
    archive = args.output / "prototype.tar"
    with archive.open("wb") as stream:
        run(["git", "-C", args.acacia, "archive", PROTOTYPE,
             "benchmarking/gr1-par2-20260923/oracle"], stdout=stream)
    prototype = args.output / "prototype"
    prototype.mkdir(exist_ok=True)
    with tarfile.open(archive) as stream:
        stream.extractall(prototype, filter="data")
    archive.unlink()
    tools = prototype / "subprojects/tlsf-tools"
    (tools / "scripts").mkdir(parents=True, exist_ok=True)
    for target, link in ((ROOT / ".git", tools / ".git"),
                         (ROOT / "external", tools / "external"),
                         (ROOT / "tools/golden/legacy_monitor.py", tools / "scripts/gr1_monitor_game.py")):
        if not link.exists():
            link.symlink_to(target)
    library = (args.spot / "lib/libbddx.so").resolve()
    digest = hashlib.sha256(library.read_bytes()).hexdigest()
    # Test the conservative cap and every variable number within it. Release
    # builds omit BuDDy's range guards, so do not probe beyond MAXVAR.
    probe = '''import buddy
buddy.bdd_init(100000,10000)
buddy.bdd_setvarnum(1024)
assert all(buddy.bdd_var(buddy.bdd_ithvar(i)) == i for i in range(1024))
'''
    environment = dict(os.environ, PYTHONPATH=str(site), LD_LIBRARY_PATH=str(library.parent))
    run([sys.executable, "-c", probe], env=environment)
    adapter = prototype / "benchmarking/gr1-par2-20260923/oracle/acacia_lift/buddy_veccompose.py"
    with adapter.open("a") as stream:
        stream.write(f'\n# Offline local-build allowlist; conservative tested ceiling.\nPINNED_BDDX_MAX_VARIABLE_COUNTS[{digest!r}] = 1024\n')
    manifest = {
        "source_commit": subprocess.check_output(["git", "-C", ROOT, "rev-parse", "HEAD"], text=True).strip(),
        "oxidd_commit": subprocess.check_output(["git", "-C", ROOT / "external/oxidd", "rev-parse", "HEAD"], text=True).strip(),
        "sha256": {name: hashlib.sha256((args.build / name).read_bytes()).hexdigest()
                   for name in ("tlsf2tlsf", "tlsf2ltl", "tlsfinfo", "tlsfsolve", "tlsfcertcheck")}}
    (args.build / "acacia-toolchain.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (args.output / "reference-setup.json").write_text(json.dumps({
        "prototype_revision": PROTOTYPE, "libbddx_sha256": digest,
        "local_variable_cap": 1024}, indent=2) + "\n")
    print(f"--bindings-site {site} --oracle-root {prototype}")


if __name__ == "__main__":
    main()
