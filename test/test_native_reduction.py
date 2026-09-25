#!/usr/bin/env python3
"""Differential test of the in-process reducer against the Python oracle."""

from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
import os
import pathlib
import random
import signal
import subprocess
import sys
import tempfile
import time

import buddy

_bdd_vars = 0


def run(command: list[str]) -> tuple[subprocess.CompletedProcess[str], float]:
    start = time.monotonic()
    process = subprocess.Popen(command, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=15)
        result = subprocess.CompletedProcess(command, process.returncode,
                                             stdout, stderr)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        result = subprocess.CompletedProcess(command, 124, "", "time cap")
    return result, time.monotonic() - start


def generated(directory: pathlib.Path) -> list[pathlib.Path]:
    names = ["i", "@", "a'", "controllable_x", "uncontrollable_x",
             "monitor_0_state_0", "assumption_safety_violated", "req@i"]
    outputs = ["o", "z'", "controllable_o", "uncontrollable_y",
               "curr_0", "val'", "@", "monitor_1_state_2"]
    guarantees = ["G ({i} -> {o});", "G !{i};", "G {o};",
                  "G ({i} -> X {o});", "G F {o};",
                  "G !{i}; G {o};", "G ({i} -> F {o});"]
    result = []
    for index, (input_name, output_name) in enumerate(zip(names, outputs)):
        if input_name == output_name:
            continue
        source = directory / f"generated-{index}.tlsf"
        source.write_text(f'''INFO {{
  TITLE: "native differential"
  DESCRIPTION: "generated"
  SEMANTICS: Mealy
  TARGET: Mealy
}}
MAIN {{
  INPUTS {{ {input_name}; }}
  OUTPUTS {{ {output_name}; }}
  ASSUMPTIONS {{ G F {input_name}; }}
  GUARANTEES {{ {guarantees[index % len(guarantees)].format(i=input_name, o=output_name)} }}
}}
''')
        result.append(source)
    crossed = [
        ("controllable_o0", "uncontrollable_i0"),
        ("controllable_o1", "uncontrollable_i1"),
        ("uncontrollable_i0", "controllable_o0"),
        ("controllable_o0_extra", "uncontrollable_i0_extra"),
        ("controllable_o0x", "uncontrollable_i0x"),
        ("controllable_o0_1", "uncontrollable_i0_1"),
    ]
    for index, (input_name, output_name) in enumerate(crossed):
        source = directory / f"generated-crossed-{index}.tlsf"
        source.write_text(f'''INFO {{
  TITLE: "native differential crossed names"
  DESCRIPTION: "generated"
  SEMANTICS: Mealy
  TARGET: Mealy
}}
MAIN {{
  INPUTS {{ {input_name}; }}
  OUTPUTS {{ {output_name}; }}
  ASSUMPTIONS {{ G F {input_name}; }}
  GUARANTEES {{ G F {output_name}; }}
}}
''')
        result.append(source)
    for label, semantics, assumptions, guarantees in (
            ("moore", "Moore", "true;", "G o;"),
            ("unsupported-mp", "Mealy", "true;", "F G o;"),
            ("safety-release", "Mealy", "G i;", "G o;"),
            ("safety-bad", "Mealy", "true;", "G !o;"),
            ("fallback", "Mealy", "true;",
             "G (F o || ((!i || X i) && (i || X !i)));"),
            ("duplicate-origin", "Mealy", "true;", "G o; G (o && true);")):
        source = directory / f"generated-{label}.tlsf"
        source.write_text(f'''INFO {{
  TITLE: "native differential"
  DESCRIPTION: "generated"
  SEMANTICS: {semantics}
  TARGET: {semantics}
}}
MAIN {{
  INPUTS {{ i; }}
  OUTPUTS {{ o; }}
  ASSUMPTIONS {{ {assumptions} }}
  GUARANTEES {{ {guarantees} }}
}}
''')
        result.append(source)
    return result


def game_functions(text: str, state: int | None = None):
    global _bdd_vars
    lines = text.splitlines()
    header = [int(value) for value in lines[0].split()[1:]]
    header += [0] * (9 - len(header))
    maximum, ni, nl, no, na, nb, nc, nj, nf = header[:9]
    position = 1

    def take():
        nonlocal position
        value = lines[position]
        position += 1
        return value

    inputs = [int(take()) for _ in range(ni)]
    latches = [tuple(map(int, take().split())) for _ in range(nl)]
    outputs = [int(take()) for _ in range(no)]
    bad = [int(take()) for _ in range(nb)]
    constraints = [int(take()) for _ in range(nc)]
    justice_sizes = [int(take()) for _ in range(nj)]
    justice = [[int(take()) for _ in range(size)] for size in justice_sizes]
    fairness = [int(take()) for _ in range(nf)]
    gates = [tuple(map(int, take().split())) for _ in range(na)]
    names = {"i": [None] * ni, "l": [None] * nl}
    while position < len(lines):
        line = take()
        if line == "c":
            break
        if line[:1] in names and len(line) > 2 and line[1].isdigit():
            label, name = line.split(maxsplit=1)
            index = int(label[1:])
            if index < len(names[label[0]]):
                names[label[0]][index] = name
    if ni + nl > _bdd_vars:
        buddy.bdd_setvarnum(ni + nl)
        _bdd_vars = ni + nl
    values = [buddy.bddfalse] * (maximum + 1)
    for index, literal in enumerate(inputs):
        values[literal // 2] = buddy.bdd_ithvar(index)
    for index, (current, _next, _reset) in enumerate(latches):
        if state is None:
            values[current // 2] = buddy.bdd_ithvar(ni + index)
        else:
            values[current // 2] = (buddy.bddtrue if state & (1 << index)
                                    else buddy.bddfalse)

    def lit(number):
        if number < 2:
            return buddy.bddtrue if number else buddy.bddfalse
        value = values[number // 2]
        return -value if number & 1 else value

    for lhs, left, right in gates:
        values[lhs // 2] = lit(left) & lit(right)
    return (names, [latch[2] for latch in latches],
            [lit(latch[1]) for latch in latches], [lit(x) for x in outputs],
            [lit(x) for x in bad], [lit(x) for x in constraints],
            [[lit(x) for x in group] for group in justice],
            [lit(x) for x in fairness])


def games_bisimilar(native: str, oracle: str) -> bool:
    native_start = game_functions(native)
    oracle_start = game_functions(oracle)
    if native_start[0]["i"] != oracle_start[0]["i"]:
        return False
    if len(native_start[2]) + len(oracle_start[2]) > 40:
        raise AssertionError("state equivalence cap exceeded")
    def reset_state(game):
        return sum((1 << index) for index, reset in enumerate(game[1])
                   if reset == 1)

    pending = deque([(reset_state(native_start), reset_state(oracle_start))])
    seen = set()
    cached_native = {}
    cached_oracle = {}
    while pending:
        pair = pending.popleft()
        if pair in seen:
            continue
        seen.add(pair)
        if len(seen) > 10000:
            raise AssertionError("state equivalence cap exceeded")
        left_state, right_state = pair
        left = cached_native.setdefault(
            left_state, game_functions(native, left_state))
        right = cached_oracle.setdefault(
            right_state, game_functions(oracle, right_state))
        if left[3:] != right[3:]:
            return False
        regions = [(buddy.bddtrue, 0, 0)]
        for side, functions in enumerate((left[2], right[2])):
            for index, function in enumerate(functions):
                split = []
                for region, lhs, rhs in regions:
                    when_false = region & -function
                    when_true = region & function
                    if when_false != buddy.bddfalse:
                        split.append((when_false, lhs, rhs))
                    if when_true != buddy.bddfalse:
                        if side == 0:
                            split.append((when_true, lhs | (1 << index), rhs))
                        else:
                            split.append((when_true, lhs, rhs | (1 << index)))
                regions = split
        for _region, lhs, rhs in regions:
            if (lhs, rhs) not in seen:
                pending.append((lhs, rhs))
    return True


def symbol_entries(path: pathlib.Path, aag: bytes) -> list[str]:
    lines = path.read_text().splitlines()
    assert lines[0] == "tlsf-tools.game-symbol-map.v1"
    assert lines[1] == hashlib.sha256(aag).hexdigest()
    return lines[2:]


def compare(source: pathlib.Path, semantics: str, directory: pathlib.Path,
            args: argparse.Namespace) -> tuple[int, float, float]:
    prefix = directory / "native"
    python_aag = directory / "python.aag"
    python_json = directory / "python.json"
    native, native_time = run([str(args.native), str(source), semantics,
                               str(prefix)])
    python, python_time = run([
        sys.executable, str(args.builder), str(source),
        "--semantics", semantics, "--output", str(python_aag),
        "--provenance-out", str(python_json),
        "--tlsf2ltl", str(args.tlsf2ltl),
        "--tlsf2tlsf", str(args.tlsf2tlsf),
        "--tlsfinfo", str(args.tlsfinfo)])
    if native.returncode == 124 or python.returncode == 124:
        return -1, native_time, python_time
    if (native.returncode == 0 or python.returncode == 0):
        if (native.returncode == 0 and python.returncode == 2 and
                "maximum recursion depth exceeded" in python.stderr):
            return -1, native_time, python_time
        assert native.returncode == python.returncode == 0, (
            source, semantics, native.returncode, native.stderr,
            python.returncode, python.stderr)
        native_aag = prefix.with_suffix(".aag").read_bytes()
        oracle_aag = python_aag.read_bytes()
        if native_aag != oracle_aag:
            native_text, oracle_text = native_aag.decode(), oracle_aag.decode()
            if game_functions(native_text) != game_functions(oracle_text):
                assert games_bisimilar(native_text, oracle_text), (
                    source, semantics, "AAG language or ownership")
        assert symbol_entries(prefix.with_suffix(".symbols"), native_aag) == \
            symbol_entries(pathlib.Path(str(python_aag) + ".symbols"),
                           oracle_aag), (source, semantics, "symbol map")
        assert json.loads(prefix.with_suffix(".json").read_text()) == \
            json.loads(python_json.read_text()), (source, semantics, "provenance")
        return 1, native_time, python_time
    assert native.returncode in (2, 3), (source, semantics, native.stderr)
    assert python.returncode in (2, 3), (source, semantics, python.stderr)
    return 0, native_time, python_time


def main() -> None:
    parser = argparse.ArgumentParser()
    for name in ("native", "builder", "tlsf2ltl", "tlsf2tlsf", "tlsfinfo",
                 "fixtures", "builddir"):
        parser.add_argument("--" + name, type=pathlib.Path, required=True)
    parser.add_argument("--corpus", type=pathlib.Path)
    args = parser.parse_args()
    for name in ("native", "builder", "tlsf2ltl", "tlsf2tlsf", "tlsfinfo",
                 "fixtures", "builddir"):
        setattr(args, name, getattr(args, name).resolve())
    if args.corpus:
        args.corpus = args.corpus.resolve()
    fixtures = sorted(args.fixtures.glob("*.tlsf"))
    sample = []
    sampled_parametric = 0
    if args.corpus:
        corpus = sorted(args.corpus.glob("*.tlsf"))
        assert len(corpus) >= 100
        parametric = [path for path in corpus if "PARAMETERS" in path.read_text()]
        nonparametric = [path for path in corpus if path not in set(parametric)]
        rng = random.Random(20260923)
        for group_index, group in enumerate((parametric, nonparametric)):
            candidates = []
            for path in sorted(group, key=lambda item: (item.stat().st_size,
                                                         item.name))[:350]:
                try:
                    lowered = subprocess.run(
                        [str(args.tlsf2ltl), "--format", "ltl", str(path)],
                        capture_output=True, check=False, timeout=1)
                except subprocess.TimeoutExpired:
                    continue
                if lowered.returncode != 0 or len(lowered.stdout) > 200:
                    continue
                input_list = subprocess.run(
                    [str(args.tlsfinfo), "--expanded-ins", str(path)],
                    capture_output=True, check=False, timeout=1)
                output_list = subprocess.run(
                    [str(args.tlsfinfo), "--expanded-outs", str(path)],
                    capture_output=True, check=False, timeout=1)
                if input_list.returncode or output_list.returncode:
                    continue
                signals = [name for output in (input_list, output_list)
                           for name in output.stdout.decode().strip().split(",")
                           if name]
                if len(signals) <= 4:
                    candidates.append(path)
            assert len(candidates) >= 52, len(candidates)
            sample.extend(candidates)
            if group_index == 0:
                sampled_parametric = len(candidates)
        sample.sort()
        required = ("simple_arbiter_enc_pb_13_pe_.tlsf",
                    "simple_arbiter_enc_pb_14_pe_.tlsf",
                    "full_arbiter_enc_pb_10_pe_.tlsf")
        for name in required:
            path = args.corpus / name
            assert path.is_file(), path
            if path not in sample:
                sample.append(path)
        sample.sort()
    counts = {"fixture": 0, "corpus": 0, "generated": 0}
    reviewed = counts.copy()
    declined = counts.copy()
    oracle_limits = counts.copy()
    reviewed_corpus_sources = set()
    times = {"native": 0.0, "python": 0.0}
    corpus_times = {"native": 0.0, "python": 0.0}
    buddy.bdd_init(2_000_000, 100_000)
    with tempfile.TemporaryDirectory(prefix="native-diff-",
                                     dir=args.builddir) as temp:
        directory = pathlib.Path(temp)
        cases = [("fixture", path) for path in fixtures]
        cases += [("corpus", path) for path in sample]
        cases += [("generated", path) for path in generated(directory)]
        for index, (kind, path) in enumerate(cases):
            if index % 10 == 0:
                print(f"native differential progress {index}/{len(cases)}",
                      file=sys.stderr, flush=True)
            work = directory / f"case-{index}"
            work.mkdir()
            source_statuses = []
            for semantics in ("exact", "strict"):
                success, native_time, python_time = compare(
                    path, semantics, work, args)
                source_statuses.append(success)
                counts[kind] += success == 1
                reviewed[kind] += success >= 0
                declined[kind] += success == 0
                oracle_limits[kind] += success == -1
                times["native"] += native_time
                times["python"] += python_time
                if kind == "corpus" and success >= 0:
                    corpus_times["native"] += native_time
                    corpus_times["python"] += python_time
            if kind == "corpus" and all(status >= 0 for status in source_statuses):
                reviewed_corpus_sources.add(path)
    if args.corpus:
        assert len(reviewed_corpus_sources) >= 100, len(reviewed_corpus_sources)
        assert counts["corpus"] and declined["corpus"], (counts, declined)
    buddy.bdd_done()
    print(f"native reduction differential: {len(fixtures)} fixtures, "
          f"{len(sample)} corpus ({sampled_parametric} parametric), {len(cases)-len(fixtures)-len(sample)} "
          f"generated, both semantics; successful reductions {counts}; "
          f"reviewed {reviewed} ({len(reviewed_corpus_sources)} corpus inputs), "
          f"declined {declined}, oracle limits {oracle_limits}; "
          f"time all native {times['native']:.2f}s, Python {times['python']:.2f}s; "
          f"corpus native {corpus_times['native']:.2f}s, "
          f"Python {corpus_times['python']:.2f}s")


if __name__ == "__main__":
    main()
