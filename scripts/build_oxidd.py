#!/usr/bin/env python3
"""Build the locked OxiDD staticlib, C headers and verified stamp for Meson."""
import pathlib
import shutil
import subprocess
import sys

import oxidd_stamp

source, output = map(pathlib.Path, sys.argv[1:3])
cargo, cbindgen = sys.argv[3:5]
crate = source / "crates/oxidd-ffi-c"
output.mkdir(parents=True, exist_ok=True)
subprocess.run([cargo, "build", "-j", "4", "--release", "--locked",
                "--target-dir", str(output / "target"),
                "--manifest-path", str(crate / "Cargo.toml")], check=True)
archive = output / "liboxidd_ffi_c.a"
shutil.copyfile(output / "target/release/liboxidd_ffi_c.a", archive)
subprocess.run([cbindgen, "--output", str(output / "capi.h"), str(crate)], check=True)
oxidd_stamp.write_if_changed(output / "config.h", "/* C-only OxiDD config */\n")
commit, dirty = oxidd_stamp.revision(source)
stamp = output / "oxidd-build-stamp"
oxidd_stamp.write_if_changed(stamp, f"commit={commit}\ndirty={dirty}\n"
                            f"sha256={oxidd_stamp.archive_hash(archive)}\n")
subprocess.run([sys.executable, str(pathlib.Path(oxidd_stamp.__file__)), "header",
                str(source), str(archive), str(stamp),
                str(output / "oxidd_build_stamp.h")], check=True)
