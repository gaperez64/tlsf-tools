#!/usr/bin/env python3
"""Pin historical GCC gate IDs and export artifacts for the CI compiler diff."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


# Captured from GCC at cd51aa7, before explicit operand sequencing.
EQUIVALENCE_SHA256 = "309a904d1caa720b48cfecab739de3688936db087585ade176e98a8906094675"
CASES = [
    ("equivalence", "", "G (a <-> b);"),
    ("negated-equivalence", "", "G !(a <-> b);"),
    ("next-equivalence", "", "G (a <-> X b);"),
    ("response", "G F a;", "G (a -> F b);"),
    ("assumption-release", "G (a <-> b);", "G F b;"),
    ("weak-until", "", "G (a W b);"),
    ("until", "", "G (a U b);"),
    ("boolean", "", "G ((a && b) || (!a && !b));"),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--builddir", type=Path, required=True)
    args = parser.parse_args()
    build = args.builddir.resolve()
    directory = build / "compiler-order"
    directory.mkdir(exist_ok=True)
    for name, assumptions, guarantees in CASES:
        source = directory / (name + ".tlsf")
        source.write_text('''INFO {
  TITLE: "compiler evaluation order"
  DESCRIPTION: "Gate numbering must preserve the GCC right-first order"
  SEMANTICS: Mealy
  TARGET: Mealy
}
MAIN {
  INPUTS { a; }
  OUTPUTS { b; }
''' + (f"  ASSUMPTIONS {{ {assumptions} }}\n" if assumptions else "") +
                          f"  GUARANTEES {{ {guarantees} }}\n}}\n")
        for semantics in ("exact", "strict"):
            prefix = directory / f"{name}-{semantics}"
            subprocess.run([build / "test/api/native_reduction", source,
                            semantics, prefix], check=True, timeout=30,
                           capture_output=True, text=True)
            digest = hashlib.sha256(prefix.with_suffix(".aag").read_bytes()).hexdigest()
            metadata = json.loads(prefix.with_suffix(".metadata.json").read_text())
            assert metadata["game_sha256"] == digest, (name, semantics, metadata)
            if name == "equivalence" and semantics == "exact":
                assert digest == EQUIVALENCE_SHA256, (digest, EQUIVALENCE_SHA256)
    print(f"{2 * len(CASES)} compiler-order reductions; historical GCC AAG preserved")


if __name__ == "__main__":
    main()
