#!/usr/bin/env python3
"""Differential and source-identity checks for frontend expansion provenance."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import re
import shutil
import subprocess
import tempfile

CASES = pathlib.Path(__file__).parents[1] / "fixtures" / "cases"


def run(*argv: str) -> str:
    result = subprocess.run(argv, text=True, capture_output=True, timeout=30)
    if result.returncode:
        raise AssertionError(f"{argv}: {result.stderr}")
    return result.stdout.strip()


def projected(data: dict) -> tuple:
    return (
        [(s["direction"], s["declaration_id"], s["dimensions"],
          s["index_tuple"], s["index_role"]) for s in data["signals"]],
        [(c["block"], c["source_formula_id"], c["source_node_id"],
          c["generated_position"],
          [(b["binder_id"], b["value"]) for b in c["bindings"]])
         for c in data["conjuncts"]],
    )


def make_provenance(tool: pathlib.Path, source: pathlib.Path,
                    directory: pathlib.Path, *params: str) -> tuple[dict, pathlib.Path]:
    basic = directory / "basic.tlsf"
    output = directory / "origin.json"
    args = [arg for param in params for arg in ("--param", param)]
    run(str(tool), *args, "--provenance-out", str(output),
        "--output", str(basic), str(source))
    data = json.loads(output.read_text())
    assert data["schema"] == "tlsf-tools.frontend-provenance.v1"
    assert data["source_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert not data["ambiguous"], source
    keys = [(c["source_formula_id"], c["generated_position"])
            for c in data["conjuncts"]]
    assert len(keys) == len(set(keys)), source
    return data, basic


def test_colliding_signals(tool: pathlib.Path, directory: pathlib.Path) -> None:
    source = directory / "colliding-signals.tlsf"
    source.write_text('''INFO {
  TITLE: "collision"
  DESCRIPTION: "collision"
  SEMANTICS: Mealy
  TARGET: Mealy
}
MAIN {
  INPUTS { a[0..1]; a_0; }
  OUTPUTS { o; }
  GUARANTEES { G (a_0 -> o); }
}
''')
    output = directory / "collision.json"
    run(str(tool), "--provenance-out", str(output),
        "--output", str(directory / "collision-basic.tlsf"), str(source))
    data = json.loads(output.read_text())
    assert data["ambiguous"] is True
    assert [s["name"] for s in data["signals"]].count("a_0") == 2
    assert any(c["unresolved_signal_reference"] for c in data["conjuncts"])


def differential(args, source: pathlib.Path, directory: pathlib.Path) -> dict:
    data, basic = make_provenance(args.tlsf2tlsf, source, directory)
    assert [s["name"] for s in data["signals"] if s["direction"] == "input"] == \
        run(str(args.tlsfinfo), "--expanded-ins", str(basic)).split(",")
    assert [s["name"] for s in data["signals"] if s["direction"] == "output"] == \
        run(str(args.tlsfinfo), "--expanded-outs", str(basic)).split(",")
    plain = directory / "plain.tlsf"
    run(str(args.tlsf2tlsf), "--basic", "--output", str(plain), str(source))
    assert basic.read_bytes() == plain.read_bytes(), source
    copied = directory / "reexpanded.json"
    run(str(args.tlsf2tlsf), "--provenance-out", str(copied),
        "--output", "/dev/null", str(basic))
    again = json.loads(copied.read_text())
    assert [(c["block"], c["formula"], c["signals"])
            for c in data["conjuncts"]] == [
                (c["block"], c["formula"], c["signals"])
                for c in again["conjuncts"]], source
    assert run(str(args.tlsf2ltl), "--format", "ltl", str(source)) == \
        run(str(args.tlsf2ltl), "--format", "ltl", str(basic)), source
    return data


def alpha_rename(source: pathlib.Path, names: list[str], directory: pathlib.Path,
                 corpus: pathlib.Path | None) -> pathlib.Path:
    text = source.read_text()
    obfuscator = (corpus.parent / "benchmarking" / "gr1-par2-20260923" /
                  "obfuscate-tlsf.py") if corpus else None
    if obfuscator and obfuscator.exists():
        spec = importlib.util.spec_from_file_location("obfuscate_tlsf", obfuscator)
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        renamed, _mapping = module.obfuscate(source.read_bytes(), 27819)
    else:
        mapping = {name: f"renamed_{i}" for i, name in enumerate(names)}
        pattern = re.compile(r"\b(" + "|".join(map(re.escape, names)) + r")\b")
        renamed = pattern.sub(lambda match: mapping[match.group()], text).encode()
    path = directory / "renamed_source.tlsf"
    path.write_bytes(renamed)
    return path


def identities(args, source: pathlib.Path, directory: pathlib.Path,
               corpus: pathlib.Path | None) -> None:
    original, _ = make_provenance(args.tlsf2tlsf, source, directory)
    moved = directory / "unrelated_basename.tlsf"
    shutil.copyfile(source, moved)
    renamed_path = alpha_rename(
        source, sorted({signal["source_name"] for signal in original["signals"]}),
        directory, corpus)
    moved_data, _ = make_provenance(args.tlsf2tlsf, moved, directory)
    renamed_data, _ = make_provenance(args.tlsf2tlsf, renamed_path, directory)
    assert projected(original) == projected(moved_data)
    assert projected(original) == projected(renamed_data)
    assert original["source_sha256"] == moved_data["source_sha256"]
    assert original["source_sha256"] != renamed_data["source_sha256"]
    if original["parameters"]:
        parameter = original["parameters"][0]
        changed, _ = make_provenance(
            args.tlsf2tlsf, source, directory,
            f'{parameter["name"]}={parameter["value"] + 1}')
        assert changed["parameters"][0]["value"] == parameter["value"] + 1
        shared = {(c["source_formula_id"], c["source_node_id"])
                  for c in original["conjuncts"]} & {
                  (c["source_formula_id"], c["source_node_id"])
                  for c in changed["conjuncts"]}
        assert shared, source
        def coordinates(data):
            result = {}
            for conjunct in data["conjuncts"]:
                key = (conjunct["source_formula_id"],
                       tuple((binding["binder_id"], binding["value"])
                             for binding in conjunct["bindings"]))
                result.setdefault(key, set()).add(conjunct["source_node_id"])
            return result
        before = coordinates(original)
        after = coordinates(changed)
        common = before.keys() & after.keys()
        assert common and all(before[key] & after[key] for key in common)
        assert {s["declaration_id"] for s in original["signals"]} == {
            s["declaration_id"] for s in changed["signals"]}


def sample(corpus: pathlib.Path) -> list[pathlib.Path]:
    names = [
        *(f"arbiter_pb_{n}_pe_.tlsf" for n in range(2, 6)),
        *(f"amba_case_study_pb_{n}_pe_.tlsf" for n in range(2, 4)),
        *(f"round_robin_arbiter_unreal2_pb_{n}_pe_.tlsf" for n in range(2, 4)),
        *(f"load_balancer_pb_{n}_pe_.tlsf" for n in range(2, 4)),
        *(f"arbiter_with_buffer_pb_{n}_pe_.tlsf" for n in range(2, 4)),
        *(f"full_arbiter_unreal1_pb_2_{u}_pe_.tlsf" for u in range(2, 10)),
        *(f"chomp_pb_2_{m}_pe_.tlsf" for m in range(2, 7)),
        "chomp_pb_3_2_pe_.tlsf",
        *(f"robot_grid_pb_{x}_{y}_pe_.tlsf"
          for x, y in ((2, 2), (3, 3), (5, 1), (6, 1))),
    ]
    nonparam = [path for path in sorted(corpus.glob("*.tlsf"))
                if "PARAMETERS" not in path.read_text().upper()][:10]
    files = [corpus / name for name in names] + nonparam
    assert len(files) == 40 and all(path.is_file() for path in files)
    return files


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tlsf2tlsf", type=pathlib.Path, required=True)
    parser.add_argument("--tlsfinfo", type=pathlib.Path, required=True)
    parser.add_argument("--tlsf2ltl", type=pathlib.Path, required=True)
    parser.add_argument("--corpus", type=pathlib.Path)
    args = parser.parse_args()
    args.tlsf2tlsf = args.tlsf2tlsf.resolve()
    args.tlsfinfo = args.tlsfinfo.resolve()
    args.tlsf2ltl = args.tlsf2ltl.resolve()
    sources = (sample(args.corpus) if args.corpus else
               [CASES / "expand_demo.tlsf", CASES / "ranges.tlsf"])
    with tempfile.TemporaryDirectory(dir=args.tlsf2tlsf.parent) as root:
        test_colliding_signals(args.tlsf2tlsf, pathlib.Path(root))
        for i, source in enumerate(sources):
            directory = pathlib.Path(root) / str(i)
            directory.mkdir()
            data = differential(args, source, directory)
            if source.name == "ranges.tlsf":
                ranged = [c for c in data["conjuncts"]
                          if c["source_formula_id"] == "GUARANTEE:1"]
                assert len(ranged) == 2
                assert {c["generated_position"] for c in ranged} == {0, 1}
            if source.name.startswith("amba_case_study_pb_"):
                assert any(signal["width_kind"] == "proved-logarithmic-encoding"
                           and signal["index_role"] == "representation-bit"
                           for signal in data["signals"])
            if source.name.startswith("chomp_pb_"):
                assert any(len(conjunct["bindings"]) >= 2
                           for conjunct in data["conjuncts"])
            if (i < 5 or i == 12 or
                    source.name.startswith(("chomp", "robot_grid"))):
                identities(args, source, directory, args.corpus)
    print(f"frontend provenance: {len(sources)} differential cases passed")


if __name__ == "__main__":
    main()
