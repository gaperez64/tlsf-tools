#!/usr/bin/env python3
"""Deterministic explicit-state differential tests for tlsfsolve GR(1).

This is intentionally self-contained: it writes tiny ASCII AIGER games,
computes the PPS/BJPPSS GR(1) fixpoint over Python sets, compares tlsfsolve's
verdict, and independently model-checks every emitted strategy by SCC analysis.

Run directly (pytest is not required):
  python3 test/oracle/test_gr1_differential.py --solver build-oxidd/tlsfsolve
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import os
import pathlib
import random
import subprocess
import tempfile
from typing import Callable, Iterable


@dataclasses.dataclass
class ParsedAag:
    inputs: list[int]
    input_names: list[str]
    latches: list[tuple[int, int, int]]
    outputs: list[int]
    output_names: list[str]
    bad: list[int]
    justice: list[list[int]]
    fairness: list[int]
    gates: list[tuple[int, int, int]]
    maxvar: int

    def eval_lit(self, lit: int, input_values: list[bool], state: int) -> bool:
        values = [False] * (self.maxvar + 1)
        for value, input_lit in zip(input_values, self.inputs):
            values[input_lit // 2] = value
        for k, (cur, _next, _reset) in enumerate(self.latches):
            values[cur // 2] = bool((state >> k) & 1)
        for lhs, rhs0, rhs1 in self.gates:
            values[lhs // 2] = _lit_value(rhs0, values) and _lit_value(rhs1, values)
        return _lit_value(lit, values)

    def initial_state(self) -> int:
        return sum((reset != 0) << k for k, (_cur, _next, reset) in enumerate(self.latches))

    def lit_input_indices(self, lit: int) -> frozenset[int]:
        input_vars = {input_lit // 2: index
                      for index, input_lit in enumerate(self.inputs)}
        latch_vars = {cur // 2 for cur, _next, _reset in self.latches}
        gates = {lhs // 2: (rhs0, rhs1) for lhs, rhs0, rhs1 in self.gates}
        memo: dict[int, frozenset[int]] = {}

        def visit(candidate: int) -> frozenset[int]:
            if candidate < 2:
                return frozenset()
            var = candidate // 2
            if var in memo:
                return memo[var]
            if var in input_vars:
                memo[var] = frozenset([input_vars[var]])
            elif var in latch_vars:
                memo[var] = frozenset()
            else:
                rhs0, rhs1 = gates[var]
                memo[var] = visit(rhs0) | visit(rhs1)
            return memo[var]

        return visit(lit)

    def lit_reads_input(self, lit: int) -> bool:
        return bool(self.lit_input_indices(lit))


def _lit_value(lit: int, values: list[bool]) -> bool:
    if lit < 2:
        return lit == 1
    value = values[lit // 2]
    return not value if lit & 1 else value


def parse_aag(text: str) -> ParsedAag:
    lines = text.splitlines()
    if not lines or not lines[0].startswith("aag "):
        raise AssertionError("missing aag header")
    header = [int(word) for word in lines[0].split()[1:]]
    if len(header) < 5:
        raise AssertionError("short aag header")
    header += [0] * (9 - len(header))
    maxvar, ni, nl, no, na, nb, nc, nj, nf = header[:9]
    pos = 1

    inputs = [int(lines[pos + k].split()[0]) for k in range(ni)]
    pos += ni
    latches: list[tuple[int, int, int]] = []
    for _ in range(nl):
        fields = [int(word) for word in lines[pos].split()]
        pos += 1
        latches.append((fields[0], fields[1], fields[2] if len(fields) == 3 else 0))
    outputs = [int(lines[pos + k].split()[0]) for k in range(no)]
    pos += no
    bad = [int(lines[pos + k].split()[0]) for k in range(nb)]
    pos += nb
    pos += nc
    justice_sizes = [int(lines[pos + k].split()[0]) for k in range(nj)]
    pos += nj
    justice: list[list[int]] = []
    for size in justice_sizes:
        justice.append([int(lines[pos + k].split()[0]) for k in range(size)])
        pos += size
    fairness = [int(lines[pos + k].split()[0]) for k in range(nf)]
    pos += nf
    gates: list[tuple[int, int, int]] = []
    for _ in range(na):
        lhs, rhs0, rhs1 = (int(word) for word in lines[pos].split())
        gates.append((lhs, rhs0, rhs1))
        pos += 1

    input_names = [f"i{k}" for k in range(ni)]
    output_names = [f"o{k}" for k in range(no)]
    while pos < len(lines) and lines[pos] != "c":
        line = lines[pos]
        pos += 1
        if len(line) < 3 or line[0] not in "io":
            continue
        prefix, name = line.split(maxsplit=1)
        index = int(prefix[1:])
        if prefix[0] == "i" and index < ni:
            input_names[index] = name
        elif prefix[0] == "o" and index < no:
            output_names[index] = name
    return ParsedAag(inputs, input_names, latches, outputs, output_names, bad,
                     justice, fairness, gates, maxvar)


class AagBuilder:
    def __init__(self, input_names: list[str], resets: list[int]):
        self.input_names = input_names
        self.resets = resets
        self.ninputs = len(input_names)
        self.nlatches = len(resets)
        self.nextvar = self.ninputs + self.nlatches
        self.inputs = [2 * (k + 1) for k in range(self.ninputs)]
        self.latches = [2 * (self.ninputs + k + 1) for k in range(self.nlatches)]
        self.gates: list[tuple[int, int, int]] = []

    def negate(self, lit: int) -> int:
        return lit ^ 1

    def land(self, left: int, right: int) -> int:
        if left == 0 or right == 0:
            return 0
        if left == 1:
            return right
        if right == 1 or left == right:
            return left
        if left == (right ^ 1):
            return 0
        self.nextvar += 1
        lhs = 2 * self.nextvar
        self.gates.append((lhs, left, right))
        return lhs

    def lor(self, left: int, right: int) -> int:
        return self.negate(self.land(self.negate(left), self.negate(right)))

    def lxor(self, left: int, right: int) -> int:
        return self.lor(self.land(left, self.negate(right)),
                        self.land(self.negate(left), right))

    def random_expr(self, rng: random.Random, atoms: list[int], depth: int) -> int:
        if depth == 0 or rng.random() < 0.45:
            lit = rng.choice([0, 1, *atoms])
            return self.negate(lit) if lit >= 2 and rng.random() < 0.35 else lit
        left = self.random_expr(rng, atoms, depth - 1)
        right = self.random_expr(rng, atoms, depth - 1)
        return rng.choice((self.land, self.lor, self.lxor))(left, right)

    def finish(self, next_lits: list[int], bad_lit: int | None,
               bad_record: bool, justice: list[int], fairness: list[int]) -> str:
        outputs = [] if bad_record else [0 if bad_lit is None else bad_lit]
        bad = [bad_lit] if bad_lit is not None and bad_record else []
        lines = [
            f"aag {self.nextvar} {self.ninputs} {self.nlatches} "
            f"{len(outputs)} {len(self.gates)} {len(bad)} 0 "
            f"{len(justice)} {len(fairness)}"
        ]
        lines.extend(str(lit) for lit in self.inputs)
        for cur, nxt, reset in zip(self.latches, next_lits, self.resets):
            lines.append(f"{cur} {nxt} {reset}")
        lines.extend(str(lit) for lit in outputs)
        lines.extend(str(lit) for lit in bad)
        lines.extend("1" for _ in justice)
        lines.extend(str(lit) for lit in justice)
        lines.extend(str(lit) for lit in fairness)
        lines.extend(f"{lhs} {rhs0} {rhs1}" for lhs, rhs0, rhs1 in self.gates)
        lines.extend(f"i{k} {name}" for k, name in enumerate(self.input_names))
        if outputs:
            lines.append("o0 bad")
        if bad:
            lines.append("b0 bad_record")
        lines.extend(f"j{k} justice_{k}" for k in range(len(justice)))
        lines.extend(f"f{k} fairness_{k}" for k in range(len(fairness)))
        return "\n".join(lines) + "\n"


def make_random_game(rng: random.Random, index: int) -> str:
    # Seeded alternating-latch variants ensure the suite exercises exactly the
    # old union-of-negated-fairness error, not merely reader loss of liveness.
    if index % 73 == 0:
        nu, nc = rng.randint(1, 3), rng.randint(1, 2)
        names = [*(f"u{k}" for k in range(nu)),
                 *(f"controllable_c{k}" for k in range(nc))]
        builder = AagBuilder(names, [rng.randint(0, 1)])
        q = builder.latches[0]
        return builder.finish([q ^ 1], None, False, [0], [q, q ^ 1])

    # A recurring exact counterexample guarantees that the archived
    # pre-follow-up solver is tested on the input-acceptance bug: the
    # environment keeps u == q forever, so GF(q <-> u) holds while GF false
    # cannot.  The system's c controls q's next value but cannot prevent this.
    if index % 79 == 1:
        builder = AagBuilder(["u0", "controllable_c0"], [0])
        u, c = builder.inputs
        q = builder.latches[0]
        q_equals_u = builder.negate(builder.lxor(q, u))
        return builder.finish([c], None, False, [0], [q_equals_u])

    nu, nc, nl = rng.randint(1, 3), rng.randint(1, 2), rng.randint(1, 3)
    names = [*(f"u{k}" for k in range(nu)),
             *(f"controllable_c{k}" for k in range(nc))]
    builder = AagBuilder(names, [rng.randint(0, 1) for _ in range(nl)])
    all_atoms = [*builder.inputs, *builder.latches]
    next_lits = [builder.random_expr(rng, all_atoms, rng.randint(1, 3))
                 for _ in range(nl)]
    state_atoms = list(builder.latches)
    fairness = [builder.random_expr(rng, state_atoms, rng.randint(0, 2))
                for _ in range(rng.randint(0, 3))]
    justice = [builder.random_expr(rng, state_atoms, rng.randint(0, 2))
               for _ in range(rng.randint(1, 2))]
    # A deterministic fraction of games has genuinely transition-level
    # acceptance over both sides' current choices.  XOR with a latch makes the
    # dependence semantic as well as syntactic.
    if index % 5 == 2:
        fairness.append(builder.lxor(builder.inputs[0], builder.latches[0]))
        justice.append(builder.lxor(builder.inputs[nu], builder.latches[-1]))
    bad_lit = None
    if rng.random() < 0.35:
        bad_lit = builder.random_expr(rng, all_atoms, rng.randint(0, 2))
    return builder.finish(next_lits, bad_lit, rng.random() < 0.5,
                          justice, fairness)


class ExplicitGame:
    def __init__(self, aag: ParsedAag):
        self.aag = aag
        self.nu_indices = [k for k, name in enumerate(aag.input_names)
                           if not name.startswith("controllable_")]
        self.nc_indices = [k for k, name in enumerate(aag.input_names)
                           if name.startswith("controllable_")]
        self.states = frozenset(range(1 << len(aag.latches)))
        self.goals = [lit for record in aag.justice for lit in record]
        acceptance_inputs = frozenset().union(*(
            aag.lit_input_indices(lit)
            for lit in [*self.goals, *aag.fairness]
        ))
        self.input_acceptance = bool(acceptance_inputs)
        self.uncontrollable_acceptance = any(
            index in self.nu_indices for index in acceptance_inputs
        )
        self.controllable_acceptance = any(
            index in self.nc_indices for index in acceptance_inputs
        )

        # Exact turn-based arena for transition acceptance:
        #   environment-state(s) -> controller-state(s,u)
        #     -> transition(s,u,c) -> environment-state(next(s,u,c)).
        # Acceptance predicates label transition vertices using the current
        # letter (s,u,c); no sampled acceptance state is introduced here.
        self.env_vertex: dict[int, int] = {}
        self.successors: list[list[int]] = []
        self.owner: list[str] = []
        self.transition_letter: dict[int, tuple[int, int, int]] = {}

        def add_vertex(owner: str) -> int:
            vertex = len(self.successors)
            self.successors.append([])
            self.owner.append(owner)
            return vertex

        for state in self.states:
            self.env_vertex[state] = add_vertex("environment")
        for state in self.states:
            source = self.env_vertex[state]
            for u in range(1 << len(self.nu_indices)):
                system = add_vertex("system")
                self.successors[source].append(system)
                for c in range(1 << len(self.nc_indices)):
                    unsafe, nxt = self.step(state, u, c)
                    if unsafe:
                        continue
                    transition = add_vertex("transition")
                    self.transition_letter[transition] = (state, u, c)
                    self.successors[system].append(transition)
                    self.successors[transition].append(self.env_vertex[nxt])

    def inputs(self, u: int, c: int) -> list[bool]:
        result = [False] * len(self.aag.inputs)
        for bit, index in enumerate(self.nu_indices):
            result[index] = bool((u >> bit) & 1)
        for bit, index in enumerate(self.nc_indices):
            result[index] = bool((c >> bit) & 1)
        return result

    def prop(self, lit: int, state: int, u: int, c: int) -> bool:
        return self.aag.eval_lit(lit, self.inputs(u, c), state)

    def step(self, state: int, u: int, c: int) -> tuple[bool, int]:
        inputs = self.inputs(u, c)
        bad_lits = list(self.aag.bad)
        if not bad_lits and len(self.aag.outputs) == 1:
            bad_lits.append(self.aag.outputs[0])
        unsafe = any(self.aag.eval_lit(lit, inputs, state) for lit in bad_lits)
        nxt = 0
        for k, (_cur, next_lit, _reset) in enumerate(self.aag.latches):
            if self.aag.eval_lit(next_lit, inputs, state):
                nxt |= 1 << k
        return unsafe, nxt

    def cpre(self, target: frozenset[int]) -> frozenset[int]:
        result = set()
        for vertex, successors in enumerate(self.successors):
            if self.owner[vertex] == "system":
                winning = any(successor in target for successor in successors)
            else:
                winning = bool(successors) and all(
                    successor in target for successor in successors
                )
            if winning:
                result.add(vertex)
        return frozenset(result)

    def solve(self, old_union: bool = False) -> frozenset[int]:
        all_vertices = frozenset(range(len(self.successors)))
        fairness_sets = [
            frozenset(
                vertex for vertex, (state, u, c) in self.transition_letter.items()
                if self.prop(lit, state, u, c)
            )
            for lit in self.aag.fairness
        ]
        goals = [
            frozenset(
                vertex for vertex, (state, u, c) in self.transition_letter.items()
                if self.prop(lit, state, u, c)
            )
            for lit in self.goals
        ]
        if not goals:
            # No system recurrence obligation: only safety remains.
            z = all_vertices
            while True:
                new_z = self.cpre(z)
                if new_z == z:
                    return frozenset(
                        state for state, vertex in self.env_vertex.items()
                        if vertex in z
                    )
                z = new_z

        z = all_vertices
        while True:
            new_z = all_vertices
            for goal in goals:
                y = frozenset()
                while True:
                    if old_union:
                        not_fair = (frozenset().union(
                            *(all_vertices - fair for fair in fairness_sets))
                            if fairness_sets else frozenset())
                        x = all_vertices
                        while True:
                            new_x = self.cpre((z & goal) | y | (x & not_fair))
                            if new_x == x:
                                break
                            x = new_x
                        new_y = x
                    else:
                        new_y = frozenset()
                        disjuncts: Iterable[frozenset[int]] = (
                            fairness_sets if fairness_sets else [all_vertices]
                        )
                        for fair in disjuncts:
                            not_fair = (all_vertices - fair
                                        if fairness_sets else frozenset())
                            x = all_vertices
                            while True:
                                new_x = self.cpre((z & goal) | y | (x & not_fair))
                                if new_x == x:
                                    break
                                x = new_x
                            new_y |= x
                    if new_y == y:
                        break
                    y = new_y
                new_z &= y
            if new_z == z:
                return frozenset(
                    state for state, vertex in self.env_vertex.items()
                    if vertex in z
                )
            z = new_z


def _tarjan(nodes: set[int], adjacency: dict[int, set[int]]) -> list[list[int]]:
    index = 0
    indices: dict[int, int] = {}
    low: dict[int, int] = {}
    stack: list[int] = []
    on_stack: set[int] = set()
    components: list[list[int]] = []

    def visit(node: int) -> None:
        nonlocal index
        indices[node] = low[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for successor in adjacency.get(node, set()):
            if successor not in nodes:
                continue
            if successor not in indices:
                visit(successor)
                low[node] = min(low[node], low[successor])
            elif successor in on_stack:
                low[node] = min(low[node], indices[successor])
        if low[node] == indices[node]:
            component = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == node:
                    break
            components.append(component)

    for node in nodes:
        if node not in indices:
            visit(node)
    return components


def check_strategy(game: ExplicitGame, strategy_text: str) -> None:
    strategy = parse_aag(strategy_text)
    original_latches = len(game.aag.latches)
    if len(strategy.latches) < original_latches:
        raise AssertionError("strategy dropped game latches")
    output_by_name = dict(zip(strategy.output_names, strategy.outputs))
    for index in game.nc_indices:
        name = game.aag.input_names[index]
        if name not in output_by_name:
            raise AssertionError(f"strategy is missing controllable output {name}")

    strategy_inputs = {name: k for k, name in enumerate(strategy.input_names)}
    for index in game.nu_indices:
        if game.aag.input_names[index] not in strategy_inputs:
            raise AssertionError("strategy is missing an uncontrollable input")

    initial = strategy.initial_state()
    expected_game_initial = game.aag.initial_state()
    if initial & ((1 << original_latches) - 1) != expected_game_initial:
        raise AssertionError("strategy game-latch reset mismatch")

    reachable = {initial}
    queue = collections.deque([initial])
    transitions: list[tuple[int, int, int, int, int]] = []
    while queue:
        strategy_state = queue.popleft()
        game_state = strategy_state & ((1 << original_latches) - 1)
        for u in range(1 << len(game.nu_indices)):
            strategy_input_values = [False] * len(strategy.inputs)
            for bit, game_index in enumerate(game.nu_indices):
                name = game.aag.input_names[game_index]
                strategy_input_values[strategy_inputs[name]] = bool((u >> bit) & 1)
            c = 0
            for bit, game_index in enumerate(game.nc_indices):
                name = game.aag.input_names[game_index]
                if strategy.eval_lit(output_by_name[name], strategy_input_values,
                                     strategy_state):
                    c |= 1 << bit
            unsafe, game_next = game.step(game_state, u, c)
            if unsafe:
                raise AssertionError("emitted strategy reaches bad")

            strategy_next = 0
            for bit, (_cur, next_lit, _reset) in enumerate(strategy.latches):
                if strategy.eval_lit(next_lit, strategy_input_values, strategy_state):
                    strategy_next |= 1 << bit
            if strategy_next & ((1 << original_latches) - 1) != game_next:
                raise AssertionError("strategy's game-latch copy diverges")
            transitions.append((strategy_state, strategy_next,
                                game_state, u, c))
            if strategy_next not in reachable:
                reachable.add(strategy_next)
                queue.append(strategy_next)

    # Preserve transition labels by splitting each controller edge through a
    # dedicated vertex.  A violating lasso has, for some system goal, a cyclic
    # SCC after goal-true transition vertices are removed, with at least one
    # transition satisfying each fairness predicate.  This evaluates
    # acceptance directly on (state_t, u_t, c_t), independently of the
    # solver's sampling-latch transformation.
    state_vertex = {state: vertex
                    for vertex, state in enumerate(sorted(reachable))}
    adjacency: dict[int, set[int]] = collections.defaultdict(set)
    transition_letter: dict[int, tuple[int, int, int]] = {}
    next_vertex = len(state_vertex)
    for source, target, game_state, u, c in transitions:
        transition_vertex = next_vertex
        next_vertex += 1
        transition_letter[transition_vertex] = (game_state, u, c)
        adjacency[state_vertex[source]].add(transition_vertex)
        adjacency[transition_vertex].add(state_vertex[target])

    state_nodes = set(state_vertex.values())
    for goal in game.goals:
        allowed = state_nodes | {
            vertex for vertex, (state, u, c) in transition_letter.items()
            if not game.prop(goal, state, u, c)
        }
        for component in _tarjan(allowed, adjacency):
            cyclic = len(component) > 1 or component[0] in adjacency[component[0]]
            if not cyclic:
                continue
            if all(any(vertex in transition_letter and
                       game.prop(fair, *transition_letter[vertex])
                       for vertex in component)
                   for fair in game.aag.fairness):
                raise AssertionError("strategy has a fair lasso that misses justice")


def run_solver(executable: pathlib.Path, game_text: str,
               *options: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".aag", encoding="utf-8") as game_file:
        game_file.write(game_text)
        game_file.flush()
        return subprocess.run(
            [str(executable), *options, game_file.name], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            timeout=10)


def run_suite(solver: pathlib.Path, games: int, seed: int,
              old_solver: pathlib.Path | None) -> dict[str, int]:
    constraint_game = "aag 1 1 0 0 0 0 1 0 0\n2\n2\ni0 u\n"
    rejected = run_solver(solver, constraint_game)
    # The intent is that a game with invariant constraints is clearly rejected, not
    # that it is rejected in any particular words: the diagnostic has been
    # reworded before, so match the behaviour and the subject, not the sentence.
    if rejected.returncode != 2 or "constraints" not in rejected.stderr:
        raise AssertionError(
            f"game reader did not clearly reject C > 0: rc={rejected.returncode} "
            f"stderr={rejected.stderr!r}")
    bad_record_game = "aag 0 0 0 0 0 1 0 0 0\n1\nb0 always_bad\n"
    bad_result = run_solver(
        solver, bad_record_game, "--game-profile=multi-safety")
    if bad_result.returncode != 1:
        raise AssertionError("AIGER bad-state record was not enforced")

    combined_game = """aag 3 2 1 0 0 1 0 1 0
2
4
6 7
6
1
7
i0 env
i1 controllable_c
b0 unsafe
"""
    for options in ((), ("--game-profile=gr1",)):
        combined = run_solver(solver, combined_game, *options)
        if combined.returncode != 1:
            raise AssertionError(
                "combined bad-state/justice game was not solved as GR(1): "
                f"options={options!r} rc={combined.returncode} "
                f"stderr={combined.stderr!r}")

    pure_justice_game = """aag 2 2 0 0 0 0 0 1 0
2
4
1
1
i0 env
i1 controllable_c
"""
    pure_justice = run_solver(solver, pure_justice_game)
    if pure_justice.returncode != 0:
        raise AssertionError(
            "pure-justice AIGER game was not accepted: "
            f"rc={pure_justice.returncode} stderr={pure_justice.stderr!r}")

    typed_precedence_game = """aag 2 2 0 1 0 1 0 1 0
2
4
1
0
1
1
i0 env
i1 controllable_c
o0 legacy_bad
b0 safe
"""
    typed_precedence = run_solver(solver, typed_precedence_game)
    if typed_precedence.returncode != 0:
        raise AssertionError(
            "ordinary output overrode an AIGER bad-state property: "
            f"rc={typed_precedence.returncode} "
            f"stderr={typed_precedence.stderr!r}")

    multiple_bad_game = """aag 2 2 0 0 0 2 0 1 0
2
4
0
1
1
1
i0 env
i1 controllable_c
b0 safe
b1 unsafe
"""
    multiple_bad = run_solver(solver, multiple_bad_game)
    if multiple_bad.returncode != 1:
        raise AssertionError(
            "GR(1) did not disjoin multiple bad-state properties: "
            f"rc={multiple_bad.returncode} stderr={multiple_bad.stderr!r}")

    rng = random.Random(seed)
    old_union_wrong = 0
    old_solver_wrong = 0
    old_solver_input_wrong = 0
    input_acceptance_games = 0
    uncontrollable_acceptance_games = 0
    controllable_acceptance_games = 0
    realizable = 0
    strategies_checked = 0
    bad_record_games = 0
    for index in range(games):
        text = make_random_game(rng, index)
        parsed = parse_aag(text)
        game = ExplicitGame(parsed)
        expected_real = game.aag.initial_state() in game.solve()
        old_union_real = game.aag.initial_state() in game.solve(old_union=True)
        old_union_wrong += old_union_real != expected_real
        bad_record_games += bool(parsed.bad)
        input_acceptance_games += game.input_acceptance
        uncontrollable_acceptance_games += game.uncontrollable_acceptance
        controllable_acceptance_games += game.controllable_acceptance

        result = run_solver(solver, text)
        expected_status = 0 if expected_real else 1
        if result.returncode != expected_status:
            raise AssertionError(
                f"game {index}: explicit={'REAL' if expected_real else 'UNREAL'}, "
                f"solver rc={result.returncode}, stderr={result.stderr!r}\n{text}"
            )
        if expected_real:
            realizable += 1
            check_strategy(game, result.stdout)
            strategies_checked += 1
        elif result.stdout:
            raise AssertionError(f"game {index}: unreal solver emitted a strategy")

        if old_solver is not None:
            old_result = run_solver(old_solver, text)
            old_solver_wrong += old_result.returncode != expected_status
            if game.input_acceptance:
                old_solver_input_wrong += old_result.returncode != expected_status

    if old_union_wrong == 0:
        raise AssertionError("seeded generator did not expose the fairness-union bug")
    if input_acceptance_games == 0:
        raise AssertionError("seeded generator did not emit input acceptance")
    if uncontrollable_acceptance_games == 0 or controllable_acceptance_games == 0:
        raise AssertionError("seeded generator did not cover both input players")
    if old_solver is not None and old_solver_input_wrong == 0:
        raise AssertionError("archived solver did not expose input-acceptance bug")
    return {
        "games": games,
        "realizable": realizable,
        "unrealizable": games - realizable,
        "bad_record_games": bad_record_games,
        "input_acceptance_games": input_acceptance_games,
        "uncontrollable_acceptance_games": uncontrollable_acceptance_games,
        "controllable_acceptance_games": controllable_acceptance_games,
        "old_union_wrong": old_union_wrong,
        "old_solver_wrong": old_solver_wrong,
        "old_solver_input_wrong": old_solver_input_wrong,
        "new_solver_wrong": 0,
        "new_solver_input_wrong": 0,
        "strategies_checked": strategies_checked,
        "strategy_failures": 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--old-solver", type=pathlib.Path)
    parser.add_argument("--games", type=int, default=320)
    parser.add_argument("--seed", type=int, default=0x5A17C0DE)
    args = parser.parse_args()
    summary = run_suite(args.solver.resolve(), args.games, args.seed,
                        args.old_solver.resolve() if args.old_solver else None)
    print(" ".join(f"{key}={value}" for key, value in summary.items()))
    return 0


def test_explicit_differential() -> None:
    """Pytest entry point; Meson calls main() directly because pytest is optional."""
    default_solver = pathlib.Path(__file__).parents[2] / "build-oxidd/tlsfsolve"
    solver = pathlib.Path(os.environ.get("TLSFSOLVE", default_solver))
    summary = run_suite(solver.resolve(), 320, 0x5A17C0DE, None)
    assert summary["new_solver_wrong"] == 0
    assert summary["strategy_failures"] == 0


if __name__ == "__main__":
    raise SystemExit(main())
