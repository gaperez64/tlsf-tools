#!/usr/bin/env python3
"""tlsfobf's command line: help, exit statuses, and nothing written on error."""

import pathlib
import subprocess
import sys
import tempfile


def run(*command, stdin=None):
    return subprocess.run(command, check=False, capture_output=True, text=True,
                          input=stdin)


def fails(tool, *args, message, stdin=None):
    done = run(tool, *args, stdin=stdin)
    assert done.returncode == 1, (args, done.returncode, done.stderr)
    assert done.stdout == "", (args, done.stdout)
    assert message in done.stderr, (args, done.stderr)


def main() -> None:
    tool, spec = sys.argv[1], pathlib.Path(sys.argv[2])
    done = run(tool, "--help")
    assert done.returncode == 0 and "Usage:" in done.stderr, done
    for word in ("--mode rename|reorder|all", "--seed", "--map", "--param",
                 "--output"):
        assert word in done.stderr, word

    fails(tool, "--mode", "shuffle", str(spec), message="invalid mode 'shuffle'")
    fails(tool, "--mode", message="--mode requires an argument")
    fails(tool, "--seed", "-1", str(spec), message="invalid seed '-1'")
    fails(tool, "--seed", "x", str(spec), message="invalid seed 'x'")
    fails(tool, "--bogus", message="unknown option '--bogus'")
    fails(tool, str(spec), str(spec), message="multiple input files")
    fails(tool, "/nonexistent/spec.tlsf", message="/nonexistent/spec.tlsf")
    fails(tool, "--param", "height=2", str(spec),
          message="unknown parameter 'height'")
    fails(tool, stdin="INFO {", message="input does not parse")

    with tempfile.TemporaryDirectory() as directory:
        out = pathlib.Path(directory) / "out.tlsf"
        mapping = pathlib.Path(directory) / "map.tsv"
        fails(tool, "--output", str(out), "--map", str(out), str(spec),
              message="need different files")
        for fault in ("1", "2"):
            fails(tool, "--test-fault", fault, "--output", str(out), "--map",
                  str(mapping), str(spec), message="self-check")
            assert not out.exists() and not mapping.exists(), fault

        # stdin and stdout, and the file forms, agree byte for byte.
        piped = run(tool, "--seed", "4", stdin=spec.read_text())
        assert piped.returncode == 0, piped.stderr
        done = run(tool, "--seed", "4", "--output", str(out), "--map",
                   str(mapping), str(spec))
        assert done.returncode == 0 and done.stdout == "", done
        assert out.read_text() == piped.stdout
        assert mapping.read_text().startswith("original\tobfuscated\tkind\n")


if __name__ == "__main__":
    main()
