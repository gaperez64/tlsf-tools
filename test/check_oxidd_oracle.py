#!/usr/bin/env python3
"""Fixed-seed explicit safety-game oracle and exhaustive closed-loop checks."""
import itertools
from pathlib import Path
import random
import subprocess
import sys
import tempfile


def bits(n):
    return list(itertools.product((False, True), repeat=n))


def encode(nu, nc, nl, tables, reset):
    ni = nu + nc
    gates = []

    def conjunction(a, b):
        lit = 2 * (ni + nl + len(gates) + 1)
        gates.append((lit, a, b))
        return lit

    roots = []
    for table in tables:
        root = 0
        for assignment, value in zip(bits(ni + nl), table):
            if value:
                term = 1
                for i, bit in enumerate(assignment):
                    term = conjunction(term, 2 * (i + 1) ^ (not bit))
                root = conjunction(root ^ 1, term ^ 1) ^ 1
        roots.append(root)
    lines = [f"aag {ni + nl + len(gates)} {ni} {nl} 1 {len(gates)}"]
    lines += [str(2 * (i + 1)) for i in range(ni)]
    lines += [f"{2 * (ni + i + 1)} {roots[i + 1]} {int(reset[i])}" for i in range(nl)]
    lines += [str(roots[0])]
    lines += [" ".join(map(str, gate)) for gate in gates]
    lines += [f"i{i} env_{i}" if i < nu else f"i{i} controllable_{i - nu}" for i in range(ni)]
    return "\n".join(lines) + "\n"


def table_eval(tables, values):
    index = 0
    for value in values:
        index = index * 2 + value
    return tables[0][index], tuple(table[index] for table in tables[1:])


def winning(nu, nc, nl, tables):
    states = set(bits(nl))
    while True:
        new = set()
        for state in states:
            if all(any(not bad and nxt in states
                       for ctrl in bits(nc)
                       for bad, nxt in [table_eval(tables, env + ctrl + state)])
                   for env in bits(nu)):
                new.add(state)
        if new == states:
            return states
        states = new


def parse_strategy(text):
    lines = iter(text.splitlines())
    _, _, ni, nl, no, ng = next(lines).split()
    ni, nl, no, ng = map(int, (ni, nl, no, ng))
    inputs = [int(next(lines)) for _ in range(ni)]
    latches = [list(map(int, next(lines).split())) for _ in range(nl)]
    outputs = [int(next(lines)) for _ in range(no)]
    gates = [list(map(int, next(lines).split())) for _ in range(ng)]
    names = {}
    for line in lines:
        if line == "c":
            break
        key, name = line.split(" ", 1)
        names[key] = name
    return inputs, latches, outputs, gates, names


def verify_strategy(text, nu, nc, tables, reset):
    inputs, latches, outputs, gates, names = parse_strategy(text)
    initial = tuple(bool(l[2]) if len(l) > 2 else False for l in latches)
    seen = set()
    todo = [(reset, initial)]
    while todo:
        state, memory = todo.pop()
        if (state, memory) in seen:
            continue
        seen.add((state, memory))
        for env in bits(nu):
            values = {0: False}

            def lit(v):
                return values[v // 2] ^ bool(v & 1)

            for i, v in enumerate(inputs):
                values[v // 2] = env[int(names[f"i{i}"].removeprefix("env_"))]
            for latch, value in zip(latches, memory):
                values[latch[0] // 2] = value
            for lhs, a, b in gates:
                values[lhs // 2] = lit(a) and lit(b)
            ctrl = [False] * nc
            for i, v in enumerate(outputs):
                ctrl[int(names[f"o{i}"].removeprefix("controllable_"))] = lit(v)
            bad, nxt = table_eval(tables, env + tuple(ctrl) + state)
            assert not bad, (state, env, ctrl)
            todo.append((nxt, tuple(lit(l[1]) for l in latches)))


def main():
    solver = str(Path(sys.argv[1]).resolve())
    rng = random.Random(240928)
    tested = 0
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "game.aag"
        for nu, nc, nl in itertools.product(range(2), range(2), range(3)):
            for sample in range(4):
                tables = [[rng.random() < (0.15 if j == 0 else 0.5)
                           for _ in bits(nu + nc + nl)] for j in range(nl + 1)]
                wins = winning(nu, nc, nl, tables)
                # Every initial state checks the entire winning region, not
                # just one verdict for each generated arena.
                for reset in bits(nl):
                    path.write_text(encode(nu, nc, nl, tables, reset))
                    for gc, transitions, verdict_only in itertools.product(
                            ("auto", "pressure"), ("eager", "demand"), (False, True)):
                        proc = subprocess.run([solver, "--oxidd-nodes=4096",
                                               "--oxidd-cache=256", f"--oxidd-gc={gc}",
                                               f"--oxidd-transitions={transitions}"] +
                                              (["--realizability-only"] if verdict_only else []) +
                                              [str(path)], capture_output=True, text=True,
                                              timeout=20, check=False)
                        assert proc.returncode == (0 if reset in wins else 1), (tested, proc.stderr)
                        if reset in wins:
                            if verdict_only:
                                assert not proc.stdout and proc.stderr.strip() == "REALIZABLE"
                            else:
                                verify_strategy(proc.stdout, nu, nc, tables, reset)
                        else:
                            assert not proc.stdout and proc.stderr.strip() == "UNREALIZABLE"
                        tested += 1
    print(f"{tested} solver runs: explicit winning regions and closed-loop strategies agree")


if __name__ == "__main__":
    main()
