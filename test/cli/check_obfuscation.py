#!/usr/bin/env python3
"""Round-trip tlsfobf against the existing tools.

For every input and mode: the output is deterministic, re-parses with
tlsf2tlsf, keeps the expanded interface under the map, and contains no
comment, original free text or original identifier. In rename mode the
basic expansion of the output must equal the input's after renaming its
atoms; reordering only permutes and swaps, so there the comparison is on the
interface and the number of formulas per section.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

TOKEN = re.compile(r"[A-Za-z_@][A-Za-z0-9_'@]*")  # IDENT in src/lib/tlsf.l
SECTIONS = ("INITIALLY", "PRESET", "REQUIRE", "ASSERT", "ASSUME", "GUARANTEE")


def run(*command: str) -> str:
    done = subprocess.run(command, check=False, capture_output=True, text=True)
    if done.returncode != 0:
        sys.exit(f"{' '.join(command)} failed:\n{done.stderr}")
    return done.stdout


def read_map(path: pathlib.Path) -> list[tuple[str, str, str]]:
    lines = path.read_text().splitlines()
    assert lines[0] == "original\tobfuscated\tkind", lines[0]
    return [tuple(line.split("\t")) for line in lines[1:]]


def body(basic: str) -> list[str]:
    """The basic spec without its INFO block, one line per entry."""
    return basic[basic.index("MAIN {"):].splitlines()


def counts(basic: str) -> dict[str, int]:
    found, current = {}, None
    for line in body(basic):
        word = line.strip().split(" ")[0]
        if word in SECTIONS:
            current = word
        elif line.strip() == "}":
            current = None
        elif current:
            found[current] = found.get(current, 0) + 1
    return found


def interface(tlsfinfo: str, path: pathlib.Path) -> tuple[list[str], list[str]]:
    ins = run(tlsfinfo, "--expanded-ins", str(path)).strip()
    outs = run(tlsfinfo, "--expanded-outs", str(path)).strip()
    return (sorted(filter(None, ins.split(","))),
            sorted(filter(None, outs.split(","))))


def check(args, source: pathlib.Path, scratch: pathlib.Path) -> None:
    original = run(args.tlsf2tlsf, "--basic", str(source))
    outputs = {}
    for mode in ("rename", "reorder", "all"):
        for seed in ("1", "2"):
            out, mapping = scratch / f"{mode}{seed}.tlsf", scratch / "map.tsv"
            run(args.tlsfobf, "--mode", mode, "--seed", seed,
                "--map", str(mapping), "--output", str(out), str(source))
            text = out.read_text()
            again = run(args.tlsfobf, "--mode", mode, "--seed", seed,
                        str(source))
            assert text == again, f"{source}: {mode} is not deterministic"
            outputs[mode, seed] = text
            code = re.sub(r'"[^"]*"', '""', text)  # reorder keeps INFO text
            assert "//" not in code and "/*" not in code, source
            basic = run(args.tlsf2tlsf, "--basic", str(out))
            entries = read_map(mapping) if mode != "reorder" else []
            signals = {old: new for old, new, kind in entries
                       if kind.endswith("-signal")}
            if mode == "reorder":
                assert interface(args.tlsfinfo, source) == \
                    interface(args.tlsfinfo, out), source
            else:
                ins, outs = interface(args.tlsfinfo, source)
                assert interface(args.tlsfinfo, out) == (
                    sorted(signals[s] for s in ins),
                    sorted(signals[s] for s in outs)), source
                names = {old for old, _, _ in entries}
                fresh = {new for _, new, _ in entries}
                leaked = (set(TOKEN.findall(text)) & names) - fresh
                assert not leaked, f"{source}: {mode} keeps {sorted(leaked)}"
                assert 'TITLE:       "obfuscated"' in text, source
                assert "TAGS" not in text, source
            assert counts(original) == counts(basic), f"{source}: {mode}"
            if mode == "rename":
                renamed = [TOKEN.sub(lambda m: signals.get(m[0], m[0]), line)
                           for line in body(original)]
                assert renamed == body(basic), \
                    f"{source}: rename changed the expansion"
    if args.distinct:
        for mode in ("rename", "reorder", "all"):
            assert outputs[mode, "1"] != outputs[mode, "2"], \
                f"{source}: seeds 1 and 2 agree in {mode} mode"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("tlsfobf")
    parser.add_argument("tlsf2tlsf")
    parser.add_argument("tlsfinfo")
    parser.add_argument("--distinct", action="store_true",
                        help="also require different seeds to differ")
    parser.add_argument("inputs", nargs="+", type=pathlib.Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as directory:
        for source in args.inputs:
            check(args, source, pathlib.Path(directory))


if __name__ == "__main__":
    main()
