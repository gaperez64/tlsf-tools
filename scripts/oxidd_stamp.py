#!/usr/bin/env python3
"""Record and verify the source and archive used by the OxiDD FFI build."""

import argparse
import hashlib
import pathlib
import re
import subprocess
import sys


def revision(oxidd):
    try:
        top = subprocess.run(
            ["git", "-C", str(oxidd), "rev-parse", "--show-toplevel"],
            check=True, capture_output=True, text=True,
        ).stdout.strip()
        # A source export inside another Git checkout must not inherit its HEAD.
        if pathlib.Path(top).resolve() != oxidd.resolve():
            return "unknown", "unknown"
        commit = subprocess.run(
            ["git", "-C", str(oxidd), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True,
        ).stdout.strip()
        dirty = subprocess.run(
            ["git", "-C", str(oxidd), "status", "--porcelain"],
            check=True, capture_output=True, text=True,
        ).stdout != ""
        return commit, "1" if dirty else "0"
    except (OSError, subprocess.CalledProcessError):
        return "unknown", "unknown"


def archive_hash(archive):
    digest = hashlib.sha256()
    with archive.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_stamp(path):
    fields = {}
    try:
        for line in path.read_text().splitlines():
            key, value = line.split("=", 1)
            if key in fields or key not in ("commit", "dirty", "sha256"):
                raise ValueError("invalid field")
            fields[key] = value
    except (OSError, ValueError) as exc:
        raise ValueError(f"missing or invalid OxiDD build stamp ({exc})") from exc
    if (not re.fullmatch(r"(?:[0-9a-f]{40}|unknown)", fields.get("commit", ""))
            or fields.get("dirty") not in ("0", "1", "unknown")
            or not re.fullmatch(r"[0-9a-f]{64}", fields.get("sha256", ""))):
        raise ValueError("invalid OxiDD build stamp")
    return fields


def validate(oxidd, archive, stamp):
    current, current_dirty = revision(oxidd)
    try:
        fields = read_stamp(stamp)
    except ValueError as exc:
        raise ValueError(f"{exc}; stamp commit unknown, current commit {current}. "
                         "Rerun scripts/build_oxidd.sh") from exc
    built = fields["commit"]
    if built != "unknown" and current != "unknown" and built != current:
        raise ValueError(f"OxiDD build stamp commit {built} differs from current "
                         f"commit {current}. Rerun scripts/build_oxidd.sh")
    try:
        actual_hash = archive_hash(archive)
    except OSError as exc:
        raise ValueError(f"OxiDD archive missing ({exc}); stamp commit {built}, "
                         f"current commit {current}. Rerun scripts/build_oxidd.sh") from exc
    if fields["sha256"] != actual_hash:
        raise ValueError(f"OxiDD archive hash differs from build stamp; stamp commit "
                         f"{built}, current commit {current}. "
                         "Rerun scripts/build_oxidd.sh")
    if built == "unknown" or current == "unknown":
        print(f"OxiDD commit is unknown (stamp {built}, current {current}); "
              "archive hash verified", file=sys.stdout)
    if fields["dirty"] == "1" or current_dirty == "1":
        print(f"OxiDD submodule is dirty (stamp {fields['dirty']}, "
              f"current {current_dirty}); archive hash verified", file=sys.stdout)
    return fields


def write_if_changed(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_text() == content:
        return
    path.write_text(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("write", "check", "header"))
    parser.add_argument("oxidd", type=pathlib.Path)
    parser.add_argument("archive", type=pathlib.Path)
    parser.add_argument("stamp", type=pathlib.Path)
    parser.add_argument("output", nargs="?", type=pathlib.Path)
    args = parser.parse_args()
    try:
        if args.action == "write":
            commit, dirty = revision(args.oxidd)
            content = (f"commit={commit}\ndirty={dirty}\n"
                       f"sha256={archive_hash(args.archive)}\n")
            write_if_changed(args.stamp, content)
        else:
            fields = validate(args.oxidd, args.archive, args.stamp)
            if args.action == "header":
                if args.output is None:
                    parser.error("header requires an output path")
                write_if_changed(
                    args.output,
                    "/* Generated after checking the OxiDD FFI build stamp. */\n"
                    f"#define TLSF_OXIDD_ARCHIVE_SHA256 \"{fields['sha256']}\"\n"
                    f"#define TLSF_OXIDD_COMMIT \"{fields['commit']}\"\n",
                )
    except (OSError, ValueError) as exc:
        print(f"oxidd_stamp: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
