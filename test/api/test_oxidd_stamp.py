"""Exercise OxiDD stamp failures and Meson's rebuild path with a scratch archive."""

import hashlib
import pathlib
import subprocess
import sys
import tempfile


def run(*args, expect=0):
    result = subprocess.run(args, text=True, capture_output=True)
    if result.returncode != expect:
        raise AssertionError(
            f"{args!r}: exit {result.returncode}, expected {expect}\n"
            f"stdout: {result.stdout}\nstderr: {result.stderr}"
        )
    return result


def meson_quote(path):
    return "'" + str(path).replace("\\", "\\\\").replace("'", "\\'") + "'"


def build_archive(root, value):
    source = root / "ffi.c"
    source.write_text(f"int ffi(void) {{ return {value}; }}\n")
    run("cc", "-c", str(source), "-o", str(root / "ffi.o"))
    archive = root / "libffi.a"
    archive.unlink(missing_ok=True)
    run("ar", "rcs", str(archive), str(root / "ffi.o"))


def main():
    script = pathlib.Path(sys.argv[1]).resolve()
    oxidd = pathlib.Path(sys.argv[2]).resolve()
    build_root = pathlib.Path(sys.argv[3]).resolve()
    with tempfile.TemporaryDirectory(prefix="oxidd-stamp-", dir=build_root) as temp:
        root = pathlib.Path(temp)
        archive = root / "libffi.a"
        stamp = root / "oxidd-build-stamp"
        cmd = (sys.executable, str(script))

        build_archive(root, 1)
        run(*cmd, "write", str(oxidd), str(archive), str(stamp))
        run(*cmd, "check", str(oxidd), str(archive), str(stamp))
        # The real export may lack Git metadata. Exercise known-revision
        # mismatch checks through the real stamp code with a controlled source
        # identity; archive hashing and the Meson relink remain unmodified.
        probe = root / "stamp_probe.py"
        probe.write_text(
            "import importlib.util, sys\n"
            f"spec = importlib.util.spec_from_file_location('stamp', {str(script)!r})\n"
            "module = importlib.util.module_from_spec(spec)\n"
            "spec.loader.exec_module(module)\n"
            "module.revision = lambda source: ('f' * 40, '0')\n"
            "sys.exit(module.main())\n"
        )
        script = probe
        cmd = (sys.executable, str(script))
        run(*cmd, "write", str(oxidd), str(archive), str(stamp))
        original = stamp.read_text()
        current = next(line[7:] for line in original.splitlines()
                       if line.startswith("commit="))
        other = "0" * 40 if current != "0" * 40 else "1" * 40
        stamp.write_text(original.replace(f"commit={current}", f"commit={other}"))
        mismatch = run(*cmd, "check", str(oxidd), str(archive), str(stamp),
                       expect=1).stderr
        assert other in mismatch and current in mismatch, mismatch
        assert "Rerun scripts/build_oxidd.sh" in mismatch, mismatch

        stamp.write_text(original)
        archive.write_bytes(archive.read_bytes() + b"tampered")
        tamper = run(*cmd, "check", str(oxidd), str(archive), str(stamp),
                     expect=1).stderr
        assert "hash differs" in tamper and current in tamper, tamper
        build_archive(root, 1)
        run(*cmd, "write", str(oxidd), str(archive), str(stamp))

        fixture = root / "fixture"
        fixture.mkdir()
        (fixture / "consumer.c").write_text(
            '#include "oxidd_build_stamp.h"\n'
            "int ffi(void);\nint consumer(void) { return ffi(); }\n"
        )
        (fixture / "main.c").write_text(
            '#include <stdio.h>\n'
            'int consumer(void);\nint main(void) { printf("%d\\n", consumer()); return 0; }\n'
        )
        (fixture / "meson.build").write_text(
            "project('oxidd-stamp-probe', 'c', meson_version: '>=1.7.0')\n"
            "python3 = find_program('python3')\n"
            "stamp_header = custom_target('oxidd_build_stamp',\n"
            "  output: 'oxidd_build_stamp.h',\n"
            f"  command: [python3, {meson_quote(script)}, 'header',\n"
            f"            {meson_quote(oxidd)}, {meson_quote(archive)},\n"
            f"            {meson_quote(stamp)}, '@OUTPUT@'],\n"
            "  build_always_stale: true)\n"
            "consumer = static_library('consumer', ['consumer.c', stamp_header])\n"
            "executable('app', 'main.c', link_with: consumer,\n"
            f"  link_args: [{meson_quote(archive)}])\n"
        )
        build = root / "build"
        run("meson", "setup", "--wrap-mode=nodownload", str(build), str(fixture))
        run("ninja", "-C", str(build), "-j", "3", "app")
        assert run(str(build / "app")).stdout.strip() == "1"
        first_digest = hashlib.sha256((build / "app").read_bytes()).hexdigest()
        first_header = (build / "oxidd_build_stamp.h").read_text()

        good_stamp = stamp.read_text()
        stamp.write_text(good_stamp.replace(f"commit={current}", f"commit={other}"))
        build_mismatch = run("ninja", "-C", str(build), "-j", "3", "app", expect=1)
        failure = build_mismatch.stdout + build_mismatch.stderr
        assert other in failure and current in failure, failure
        assert "Rerun scripts/build_oxidd.sh" in failure, failure
        stamp.write_text(good_stamp)

        build_archive(root, 2)
        run(*cmd, "write", str(oxidd), str(archive), str(stamp))
        run("ninja", "-C", str(build), "-j", "3", "app")
        assert run(str(build / "app")).stdout.strip() == "2"
        assert (build / "oxidd_build_stamp.h").read_text() != first_header
        assert hashlib.sha256((build / "app").read_bytes()).hexdigest() != first_digest
    print("OxiDD stamp mismatch, tamper, and relink: passed")


if __name__ == "__main__":
    main()
