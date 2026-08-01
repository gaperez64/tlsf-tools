#!/usr/bin/env python3
"""Resolve a version string from git, archive metadata, or fall back to 'unknown'."""

import pathlib
import re
import subprocess
import sys

# Relative to the source root. Must be listed in .gitattributes as export-subst.
ARCHIVE_FILE = "scripts/version-archive.txt"
TAG_PREFIX = "v"


def git_output(source_root: pathlib.Path, *args: str) -> str | None:
    try:
        completed = subprocess.run(
            ["git", "-C", str(source_root), *args],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
        )
    except OSError:
        return None
    if completed.returncode != 0:
        return None
    return completed.stdout.strip()


def live_git_version(source_root: pathlib.Path, dirty: bool) -> str | None:
    if git_output(source_root, "rev-parse", "--git-dir") is None:
        return None

    version = git_output(
        source_root,
        "describe",
        "--tags",
        "--exact-match",
        "--match",
        "v*",
        "HEAD",
    )
    if not version:
        version = git_output(source_root, "rev-parse", "--short=7", "HEAD")
    if not version:
        return None
    version = version.removeprefix(TAG_PREFIX)

    if dirty and git_output(source_root, "status", "--porcelain"):
        version += "-dirty"
    return version


def archive_version(source_root: pathlib.Path) -> str | None:
    try:
        text = (source_root / ARCHIVE_FILE).read_text(encoding="utf-8")
    except OSError:
        return None
    fields = dict(line.split("=", 1) for line in text.splitlines() if "=" in line)

    describe = fields.get("describe", "")
    commit = fields.get("commit", "")

    # Built by concatenation so this script is never rewritten by its own
    # export-subst rule, should the attribute scope ever widen.
    placeholder = "$" + "Format:"
    if placeholder in describe or placeholder in commit:
        return None

    # A "-<N>-g<sha>" suffix means this commit is not exactly a tag, so use
    # the bare commit hash just as the live-git path does.
    if describe and not re.search(r"-\d+-g[0-9a-f]+$", describe):
        return describe.removeprefix(TAG_PREFIX)
    return commit or None


def main() -> None:
    try:
        source_root = pathlib.Path(sys.argv[0]).resolve().parent.parent
        dirty = "--dirty" in sys.argv[1:]
        version = (
            live_git_version(source_root, dirty)
            or archive_version(source_root)
            or "unknown"
        )
    except Exception:
        version = "unknown"
    print(version)


if __name__ == "__main__":
    main()
