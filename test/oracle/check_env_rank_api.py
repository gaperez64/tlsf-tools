#!/usr/bin/env python3
"""Exercise the native rank boundary and its preflight refusals."""

import argparse
import pathlib
import re
import subprocess




def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=pathlib.Path, required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    parser.add_argument("--fixture", type=pathlib.Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    source = args.out / "source.tlsf"
    source.write_text(args.fixture.read_text())
    renamed = args.out / "renamed.tlsf"
    renamed.write_text(re.sub(r"\bg\b", "reply", re.sub(
        r"\br\b", "incoming", source.read_text())))

    def run(path, mode):
        output = args.out / f"rank-{path.stem}-{mode}.aag"
        result = subprocess.run([str(args.binary), str(path), str(output),
                                 str(mode)], capture_output=True, text=True,
                                timeout=120, check=False)
        return result.returncode, result.stdout.strip(), result.stderr.strip()

    def check():
        alignment = subprocess.run(
            [str(args.binary), "--alignment-selftest"],
            capture_output=True, text=True, timeout=10, check=False)
        assert alignment.returncode == 0, (alignment.stdout, alignment.stderr)
        code, output, error = run(source, 0)
        assert code == 0, (output, error)
        baseline = output
        assert "solves=3 checks=3" in output, output
        assert "classes=" in output and "applies=" in output, output
        fields = dict(field.split("=", 1) for field in output.split()
                      if "=" in field)
        assert int(fields["anchor_free"]) > 0, output
        assert int(fields["previous"]) > 0, output
        for mode in (1, 2, 3, 4, 5):
            code, output, error = run(source, mode)
            assert code == 1 and ("stage=schema_abi" if mode == 5 else
                                  "stage=typed_alignment") in output, (
                mode, output, error)
        code, output, error = run(source, 6)
        assert code == 1 and "stage=schema" in output, (output, error)
        code, output, error = run(source, 7)
        assert code == 1 and "stage=typed_alignment" in output, (output, error)
        assert "ambiguous sibling linkage" in error, error
        code, renamed_output, error = run(renamed, 0)
        assert code == 0, (renamed_output, error)
        assert baseline.split("classes=")[-1].split()[0] == (
            renamed_output.split("classes=")[-1].split()[0])

    check()


if __name__ == "__main__":
    main()
