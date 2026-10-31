#!/usr/bin/env python3
"""Evaluate native AAG games on committed golden lasso memberships."""

from __future__ import annotations

import argparse
import json
import pathlib
import random
import re
import subprocess
import sys
import tempfile

from golden import Golden


class Game:
    def __init__(self, text: str):
        lines = text.splitlines()
        fields = [int(value) for value in lines[0].split()[1:]]
        fields += [0] * (9 - len(fields))
        self.maxvar, ni, nl, no, na, nb, nc, nj, nf = fields[:9]
        assert no == 1 and nb == nc == 0
        position = 1

        def take():
            nonlocal position
            line = lines[position]
            position += 1
            return line

        self.inputs = [int(take()) for _ in range(ni)]
        self.latches = [tuple(map(int, take().split())) for _ in range(nl)]
        self.bad = int(take())
        sizes = [int(take()) for _ in range(nj)]
        self.justice = [[int(take()) for _ in range(size)] for size in sizes]
        self.fairness = [int(take()) for _ in range(nf)]
        self.gates = [tuple(map(int, take().split())) for _ in range(na)]
        self.input_names = [None] * ni
        while position < len(lines):
            line = take()
            if line == "c":
                break
            if line.startswith("i") and " " in line:
                label, name = line.split(maxsplit=1)
                if label[1:].isdigit() and int(label[1:]) < ni:
                    self.input_names[int(label[1:])] = name
        assert all(self.input_names)

    def initial(self):
        return sum(1 << index for index, item in enumerate(self.latches)
                   if item[2] == 1)

    def step(self, state: int, letter: int):
        values = [False] * (self.maxvar + 1)
        for index, literal in enumerate(self.inputs):
            values[literal // 2] = bool(letter & (1 << index))
        for index, (current, _next, _reset) in enumerate(self.latches):
            values[current // 2] = bool(state & (1 << index))

        def lit(number):
            if number < 2:
                return bool(number)
            value = values[number // 2]
            return not value if number & 1 else value

        for lhs, left, right in self.gates:
            values[lhs // 2] = lit(left) and lit(right)
        next_state = sum(1 << index for index, (_current, next_lit, _reset)
                         in enumerate(self.latches) if lit(next_lit))
        justice = tuple(all(lit(item) for item in group)
                        for group in self.justice)
        fairness = tuple(lit(item) for item in self.fairness)
        return next_state, lit(self.bad), justice, fairness

    def accepts(self, prefix: list[int], loop: list[int]):
        state = self.initial()
        bad = False
        for letter in prefix:
            state, violated, _justice, _fairness = self.step(state, letter)
            bad |= violated
        seen = {}
        observations = []
        position = 0
        while (state, position) not in seen:
            seen[state, position] = len(observations)
            next_state, violated, justice, fairness = self.step(
                state, loop[position])
            bad |= violated
            observations.append((justice, fairness))
            state = next_state
            position = (position + 1) % len(loop)
        cycle = observations[seen[state, position]:]
        if bad:
            return False
        if self.fairness and any(not any(row[1][i] for row in cycle)
                                 for i in range(len(self.fairness))):
            return True
        return all(any(row[0][i] for row in cycle)
                   for i in range(len(self.justice)))


def tiny(input_name: str, output_name: str, assumptions: str,
         guarantees: str) -> str:
    return f'''INFO {{
  TITLE: "language check"
  DESCRIPTION: "generated"
  SEMANTICS: Mealy
  TARGET: Mealy
}}
MAIN {{
  INPUTS {{ {input_name}; }}
  OUTPUTS {{ {output_name}; }}
  ASSUMPTIONS {{ {assumptions} }}
  GUARANTEES {{ {guarantees} }}
}}
'''


def check(source: pathlib.Path, args, directory: pathlib.Path,
          expect_fallback: bool):
    prefix = directory / source.stem
    subprocess.run([str(args.native), str(source), "exact", str(prefix)],
                   check=True, capture_output=True, timeout=60)
    game = Game(prefix.with_suffix(".aag").read_text())
    metadata = json.loads(prefix.with_suffix(".metadata.json").read_text())
    if expect_fallback:
        assert metadata["fallback_monitor_count"] > 0
    lowered = subprocess.run([str(args.tlsf2ltl), "--format", "ltl",
                              str(source)], check=True, capture_output=True,
                             text=True).stdout
    # Preserve declaration order while mapping complete tokens to game APs.
    input_name, output_name = source.stem.split("--", maxsplit=1)
    symbols = {input_name: "uncontrollable_i0",
               output_name: "controllable_o0"}
    token = re.compile(r"[A-Za-z_@][A-Za-z0-9_@']*")
    formula = token.sub(lambda match: '"' + symbols[match[0]] + '"'
                        if match[0] in symbols else match[0], lowered).strip()

    rng = random.Random(0x20260923)
    words = [([], [bits]) for bits in range(4)]
    words += [([rng.randrange(4) for _ in range(rng.randrange(3))],
               [rng.randrange(4) for _ in range(rng.randrange(1, 4))])
              for _ in range(48)]

    actual = "".join("1" if game.accepts(prefix, loop) else "0"
                     for prefix, loop in words)
    args.gold.language(formula, game.input_names, words, actual)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--builddir", type=pathlib.Path, required=True)
    args = parser.parse_args()
    args.builddir = args.builddir.resolve()
    args.native = args.builddir / "test/api/native_reduction"
    args.tlsf2ltl = args.builddir / "tlsf2ltl"
    args.gold = Golden("native-language")
    cases = [
        ("i", "o", "true;", "G (i -> o);", False),
        ("controllable_x", "uncontrollable_y", "G F controllable_x;",
         "G (controllable_x -> X uncontrollable_y); G F uncontrollable_y;",
         False),
        ("@", "z'", "G @;", "G z';", False),
        ("monitor_0_state_0", "assumption_safety_violated", "true;",
         "G !monitor_0_state_0; G F assumption_safety_violated;", False),
        ("controllable_o0", "uncontrollable_i0", "G F controllable_o0;",
         "G F uncontrollable_i0;", False),
        ("controllable_o1", "uncontrollable_i1", "G F controllable_o1;",
         "G F uncontrollable_i1;", False),
        ("uncontrollable_i0", "controllable_o0", "G F uncontrollable_i0;",
         "G F controllable_o0;", False),
        ("controllable_o0_extra", "uncontrollable_i0_extra",
         "G F controllable_o0_extra;", "G F uncontrollable_i0_extra;", False),
        ("controllable_o0x", "uncontrollable_i0x", "G F controllable_o0x;",
         "G F uncontrollable_i0x;", False),
        ("controllable_o0_1", "uncontrollable_i0_1",
         "G F controllable_o0_1;", "G F uncontrollable_i0_1;", False),
        ("s", "g", "true;",
         "G (F g || ((!s || X s) && (s || X !s)));", True),
    ]
    with tempfile.TemporaryDirectory(prefix="native-language-",
                                     dir=args.builddir) as temp:
        directory = pathlib.Path(temp)
        for input_name, output_name, assumptions, guarantees, fallback in cases:
            source = directory / f"{input_name}--{output_name}.tlsf"
            source.write_text(tiny(input_name, output_name, assumptions,
                                   guarantees))
            check(source, args, directory, fallback)
    args.gold.finish()
    print(f"native golden language checks: {len(cases)} cases, 52 lassos each")


if __name__ == "__main__":
    main()
