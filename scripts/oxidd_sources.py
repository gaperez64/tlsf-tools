#!/usr/bin/env python3
"""List the vendored build inputs without depending on Git or host artifacts."""
import pathlib
import sys


def sources(root):
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if any(part in {".git", "target", "build", "__pycache__"} for part in relative.parts):
            continue
        if path.is_file():
            yield path


if __name__ == "__main__":
    for path in sources(pathlib.Path(sys.argv[1])):
        print(path)
