#!/usr/bin/env python3
"""Differential and one-step tests for tlsfsolve GR(1) certificates."""

from __future__ import annotations

import argparse
import dataclasses
import json
import pathlib
import random
import subprocess
import sys
import tempfile
from collections.abc import Callable

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import test_gr1_differential as differential  # noqa: E402


ParsedAag = differential.ParsedAag


@dataclasses.dataclass
class Fixpoint:
    winning: frozenset[int]
    goals: list[frozenset[int]]
    fairness: list[frozenset[int]]
    y: list[list[frozenset[int]]]
    x: list[list[list[frozenset[int]]]]  # goal, level, fairness
    moves: list[frozenset[tuple[int, int, int]]]


class SampledGame:
    """Independent explicit model of the solver's acceptance sampling."""

    def __init__(self, game: ParsedAag):
        self.game = game
        self.nu_indices = [
            k for k, name in enumerate(game.input_names)
            if not name.startswith("controllable_")
        ]
        self.nc_indices = [
            k for k, name in enumerate(game.input_names)
            if name.startswith("controllable_")
        ]
        flat_goals = [lit for record in game.justice for lit in record]
        self.samples: list[tuple[str, int, int]] = []
        self.goal_sources = [self._source("justice", k, lit)
                             for k, lit in enumerate(flat_goals)]
        self.fair_sources = [self._source("fairness", k, lit)
                             for k, lit in enumerate(game.fairness)]
        self.nstate = len(game.latches) + len(self.samples)
        self.states = frozenset(range(1 << self.nstate))
        self.reset = game.initial_state()

    def _source(self, kind: str, index: int, lit: int) -> tuple[str, int]:
        if self.game.lit_reads_input(lit):
            bit = len(self.game.latches) + len(self.samples)
            self.samples.append((kind, index, lit))
            return "sample", bit
        return "literal", lit

    def inputs(self, u: int, c: int) -> list[bool]:
        result = [False] * len(self.game.inputs)
        for bit, index in enumerate(self.nu_indices):
            result[index] = bool((u >> bit) & 1)
        for bit, index in enumerate(self.nc_indices):
            result[index] = bool((c >> bit) & 1)
        return result

    def source(self, source: tuple[str, int], state: int) -> bool:
        kind, value = source
        if kind == "sample":
            return bool((state >> value) & 1)
        return self.game.eval_lit(
            value, [False] * len(self.game.inputs), state)

    def step(self, state: int, u: int, c: int) -> tuple[bool, int]:
        values = self.inputs(u, c)
        bad_lits = list(self.game.bad)
        bad_lits.extend(
            lit for name, lit in zip(self.game.output_names, self.game.outputs)
            if name == "bad"
        )
        unsafe = any(self.game.eval_lit(lit, values, state)
                     for lit in bad_lits)
        nxt = 0
        for bit, (_cur, next_lit, _reset) in enumerate(self.game.latches):
            if self.game.eval_lit(next_lit, values, state):
                nxt |= 1 << bit
        for offset, (_kind, _index, lit) in enumerate(self.samples):
            if self.game.eval_lit(lit, values, state):
                nxt |= 1 << (len(self.game.latches) + offset)
        return unsafe, nxt

    def cpre(self, target: frozenset[int]) -> frozenset[int]:
        result = set()
        for state in self.states:
            winning = True
            for u in range(1 << len(self.nu_indices)):
                if not any(
                    not unsafe and nxt in target
                    for c in range(1 << len(self.nc_indices))
                    for unsafe, nxt in [self.step(state, u, c)]
                ):
                    winning = False
                    break
            if winning:
                result.add(state)
        return frozenset(result)

    def solve(self) -> Fixpoint:
        goals = [frozenset(s for s in self.states if self.source(src, s))
                 for src in self.goal_sources]
        fairness = [
            frozenset(s for s in self.states if self.source(src, s))
            for src in self.fair_sources
        ]
        nfair = len(fairness) or 1
        z = self.states
        while True:
            new_z = self.states
            final_y: list[list[frozenset[int]]] = []
            final_x: list[list[list[frozenset[int]]]] = []
            for goal in goals:
                y = frozenset()
                y_levels: list[frozenset[int]] = []
                x_by_level: list[list[frozenset[int]]] = []
                while True:
                    new_y = frozenset()
                    level: list[frozenset[int]] = []
                    for i in range(nfair):
                        not_fair = (self.states - fairness[i]
                                    if fairness else frozenset())
                        x = self.states
                        while True:
                            new_x = self.cpre(
                                (z & goal) | y | (x & not_fair))
                            if new_x == x:
                                break
                            x = new_x
                        level.append(x)
                        new_y |= x
                    x_by_level.append(level)
                    y_levels.append(new_y)
                    converged = new_y == y
                    y = new_y
                    if converged:
                        break
                new_z &= y
                final_y.append(y_levels)
                final_x.append(x_by_level)
            if new_z == z:
                moves = self._moves(z, goals, fairness, final_y, final_x)
                return Fixpoint(z, goals, fairness, final_y, final_x, moves)
            z = new_z

    def _moves(self, winning, goals, fairness, y_levels, x_levels):
        result: list[frozenset[tuple[int, int, int]]] = []
        nfair = len(fairness) or 1
        for j, goal in enumerate(goals):
            at_goal = winning & goal
            moves: set[tuple[int, int, int]] = set()
            for state in at_goal:
                for u in range(1 << len(self.nu_indices)):
                    for c in range(1 << len(self.nc_indices)):
                        unsafe, nxt = self.step(state, u, c)
                        if not unsafe and nxt in winning:
                            moves.add((state, u, c))
            covered = set(at_goal)
            for k, level in enumerate(x_levels[j]):
                strict = set(at_goal if k == 0
                             else at_goal | y_levels[j][k - 1])
                for i in range(nfair):
                    xki = level[i]
                    layer = xki - covered
                    target = strict | set(xki - fairness[i] if fairness
                                          else frozenset())
                    for state in layer:
                        for u in range(1 << len(self.nu_indices)):
                            for c in range(1 << len(self.nc_indices)):
                                unsafe, nxt = self.step(state, u, c)
                                if not unsafe and nxt in target:
                                    moves.add((state, u, c))
                    covered |= xki
            result.append(frozenset(moves))
        return result


class Certificate:
    def __init__(self, aag: ParsedAag, sidecar: dict):
        self.aag = aag
        self.sidecar = sidecar
        self.outputs = dict(zip(aag.output_names, aag.outputs))
        self.state_map = sidecar["variables"]["state"]
        self.game_inputs = {
            item["game_input"]: item["certificate_input"]
            for role in ("uncontrollable", "controllable")
            for item in sidecar["variables"][role]
        }
        self.overrides: dict[str, str | Callable[[int, int, int], bool]] = {}

    def value(self, name: str, state: int, u: int, c: int,
              model: SampledGame) -> bool:
        override = self.overrides.get(name)
        if callable(override):
            return override(state, u, c)
        if isinstance(override, str):
            name = override
        inputs = [False] * len(self.aag.inputs)
        for item in self.state_map:
            inputs[item["certificate_input"]] = bool(
                (state >> item["game_latch"]) & 1)
        game_values = model.inputs(u, c)
        for game_index, cert_index in self.game_inputs.items():
            inputs[cert_index] = game_values[game_index]
        return self.aag.eval_lit(self.outputs[name], inputs, 0)


def run_solver(solver: pathlib.Path, game_text: str):
    with tempfile.TemporaryDirectory(prefix="tlsf-gr1-cert-") as directory:
        root = pathlib.Path(directory)
        game = root / "game.aag"
        aag = root / "certificate.aag"
        sidecar = root / "certificate.json"
        game.write_text(game_text, encoding="utf-8")
        result = subprocess.run(
            [str(solver), "--certificate", str(aag), "--certificate-json",
             str(sidecar), str(game)],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False, timeout=20)
        return (result, differential.parse_aag(aag.read_text(encoding="utf-8")),
                json.loads(sidecar.read_text(encoding="utf-8")))


def check_exact(model: SampledGame, fixpoint: Fixpoint,
                certificate: Certificate, expected_real: bool) -> int:
    sidecar = certificate.sidecar
    assert sidecar["status"] == ("realizable" if expected_real
                                 else "unrealizable")
    assert sidecar["side"] == ("system" if expected_real else "environment")
    assert sidecar["reduction_semantics"] == "exact"
    assert sidecar["counts"]["goals"] == len(fixpoint.goals)
    assert sidecar["counts"]["fairness_assumptions"] == len(fixpoint.fairness)
    assert sidecar["counts"]["levels_per_goal"] == [
        len(levels) for levels in fixpoint.y]
    assert sidecar["counts"]["aig_latches"] == 0
    assert sidecar["counts"]["sampling_latches"] == len(model.samples)
    sampled_records = sidecar["variables"]["state"][len(model.game.latches):]
    for offset, ((kind, index, lit), record) in enumerate(
            zip(model.samples, sampled_records)):
        assert record["solver_added"] is True
        assert record["reset"] == 0
        assert record["next_game_literal"] == lit
        assert record["name"].startswith("__tlsf_gr1_sample_")
        source = record["source"]
        assert source["kind"] == kind
        if kind == "fairness":
            assert source["index"] == index
        else:
            assert source["record"] == index
            assert source["member"] == 0
        assert record["game_latch"] == len(model.game.latches) + offset

    predicates = 0
    for state in model.states:
        assert certificate.value("inv", state, 0, 0, model) == (
            state in fixpoint.winning)
        predicates += 1
        if not expected_real:
            assert certificate.value("losing", state, 0, 0, model) == (
                state not in fixpoint.winning)
            predicates += 1
        for j, goal in enumerate(fixpoint.goals):
            assert certificate.value(f"goal_{j}", state, 0, 0, model) == (
                state in goal)
            predicates += 1
            for k, y_level in enumerate(fixpoint.y[j]):
                assert certificate.value(
                    f"y_{j}_{k}", state, 0, 0, model) == (state in y_level)
                predicates += 1
                for i, x_level in enumerate(fixpoint.x[j][k]):
                    assert certificate.value(
                        f"x_{j}_{k}_{i}", state, 0, 0, model
                    ) == (state in x_level)
                    predicates += 1
    if expected_real:
        for j, moves in enumerate(fixpoint.moves):
            for state in model.states:
                for u in range(1 << len(model.nu_indices)):
                    for c in range(1 << len(model.nc_indices)):
                        assert certificate.value(
                            f"move_{j}", state, u, c, model
                        ) == ((state, u, c) in moves)
                        predicates += 1
    return predicates


def _rank(certificate: Certificate, model: SampledGame, goal: int,
          state: int) -> tuple[int, int] | None:
    if certificate.value(f"goal_{goal}", state, 0, 0, model):
        return (-1, -1)
    levels = certificate.sidecar["counts"]["levels_per_goal"][goal]
    nfair = certificate.sidecar["counts"]["fairness_assumptions"] or 1
    for k in range(levels):
        for i in range(nfair):
            if certificate.value(f"x_{goal}_{k}_{i}", state, 0, 0, model):
                return k, i
    return None


def check_one_step(model: SampledGame, certificate: Certificate,
                   strategy_text: str) -> int:
    strategy = differential.parse_aag(strategy_text)
    goals = certificate.sidecar["counts"]["goals"]
    if len(strategy.latches) != model.nstate + goals:
        raise AssertionError("strategy/certificate latch mapping mismatch")
    if not certificate.value("inv", model.reset, 0, 0, model):
        raise AssertionError("reset state is outside inv")
    strategy_inputs = {name: k for k, name in enumerate(strategy.input_names)}
    strategy_outputs = dict(zip(strategy.output_names, strategy.outputs))
    checks = 0
    for state in model.states:
        if not certificate.value("inv", state, 0, 0, model):
            continue
        for goal in range(goals):
            strategy_state = state | (1 << (model.nstate + goal))
            for u in range(1 << len(model.nu_indices)):
                inputs = [False] * len(strategy.inputs)
                for bit, game_index in enumerate(model.nu_indices):
                    name = model.game.input_names[game_index]
                    inputs[strategy_inputs[name]] = bool((u >> bit) & 1)
                c = 0
                for bit, game_index in enumerate(model.nc_indices):
                    name = model.game.input_names[game_index]
                    if strategy.eval_lit(
                            strategy_outputs[name], inputs, strategy_state):
                        c |= 1 << bit
                unsafe, expected_next = model.step(state, u, c)
                actual_next = 0
                for bit, (_cur, next_lit, _reset) in enumerate(
                        strategy.latches[:model.nstate]):
                    if strategy.eval_lit(next_lit, inputs, strategy_state):
                        actual_next |= 1 << bit
                if unsafe or actual_next != expected_next:
                    raise AssertionError("strategy transition is not the game transition")
                if not certificate.value("inv", actual_next, 0, 0, model):
                    raise AssertionError("inv is not inductive under strategy")
                if not certificate.value(
                        f"move_{goal}", state, u, c, model):
                    raise AssertionError("strategy move is outside move relation")

                at_goal = certificate.value(
                    f"goal_{goal}", state, 0, 0, model)
                next_counters = 0
                for bit, (_cur, next_lit, _reset) in enumerate(
                        strategy.latches[model.nstate:]):
                    if strategy.eval_lit(next_lit, inputs, strategy_state):
                        next_counters |= 1 << bit
                expected_counter = (goal + 1) % goals if at_goal else goal
                if next_counters != 1 << expected_counter:
                    raise AssertionError("goal counter does not advance as documented")
                if not at_goal:
                    rank = _rank(certificate, model, goal, state)
                    next_rank = _rank(certificate, model, goal, actual_next)
                    if rank is None or next_rank is None:
                        raise AssertionError("inv state has no certificate rank")
                    fair_holds = (
                        model.source(model.fair_sources[rank[1]], actual_next)
                        if model.fair_sources else True
                    )
                    if not (next_rank < rank or
                            (next_rank == rank and not fair_holds)):
                        raise AssertionError("rank does not decrease or stutter fairly")
                checks += 1
    return checks


def expect_rejected(action: Callable[[], None], description: str) -> None:
    try:
        action()
    except AssertionError:
        return
    raise AssertionError(f"mutated certificate was accepted: {description}")


def _bdd_values(circuit: ParsedAag, inputs, latches, buddy_module):
    values = [buddy_module.bddfalse] * (circuit.maxvar + 1)
    for lit, value in zip(circuit.inputs, inputs):
        values[lit // 2] = value
    for (cur, _next, _reset), value in zip(circuit.latches, latches):
        values[cur // 2] = value

    def lit_value(lit: int):
        if lit == 0:
            return buddy_module.bddfalse
        if lit == 1:
            return buddy_module.bddtrue
        value = values[lit // 2]
        return -value if lit & 1 else value

    for lhs, rhs0, rhs1 in circuit.gates:
        values[lhs // 2] = lit_value(rhs0) & lit_value(rhs1)
    return values, lit_value


def check_one_step_symbolic(game: ParsedAag, certificate: Certificate,
                            strategy_text: str) -> int:
    """Universal one-step oracle over all inv states, using BuDDy."""
    import buddy

    strategy = differential.parse_aag(strategy_text)
    sidecar = certificate.sidecar
    nstate = sidecar["counts"]["state_variables"]
    original_nlat = sidecar["counts"]["original_game_latches"]
    goals = sidecar["counts"]["goals"]
    nu_indices = [
        k for k, name in enumerate(game.input_names)
        if not name.startswith("controllable_")
    ]
    nc_indices = [
        k for k, name in enumerate(game.input_names)
        if name.startswith("controllable_")
    ]
    if len(strategy.latches) != nstate + goals:
        raise AssertionError("strategy/certificate latch mapping mismatch")

    buddy.bdd_init(1_000_000, 100_000)
    try:
        buddy.bdd_setvarnum(nstate + len(nu_indices))
        state = [buddy.bdd_ithvar(k) for k in range(nstate)]
        uexpr = {
            game_index: buddy.bdd_ithvar(nstate + bit)
            for bit, game_index in enumerate(nu_indices)
        }
        strategy_input_index = {
            name: k for k, name in enumerate(strategy.input_names)
        }
        strategy_output = dict(zip(strategy.output_names, strategy.outputs))

        def compile_certificate(state_expr, game_inputs):
            inputs = [buddy.bddfalse] * len(certificate.aag.inputs)
            for item in sidecar["variables"]["state"]:
                inputs[item["certificate_input"]] = state_expr[
                    item["game_latch"]]
            for role in ("uncontrollable", "controllable"):
                for item in sidecar["variables"][role]:
                    inputs[item["certificate_input"]] = game_inputs[
                        item["game_input"]]
            _values, lit = _bdd_values(
                certificate.aag, inputs, [], buddy)
            return {
                name: lit(output_lit)
                for name, output_lit in zip(
                    certificate.aag.output_names, certificate.aag.outputs)
            }

        def compile_strategy(goal):
            inputs = [buddy.bddfalse] * len(strategy.inputs)
            for game_index, expression in uexpr.items():
                name = game.input_names[game_index]
                inputs[strategy_input_index[name]] = expression
            counters = [buddy.bddtrue if j == goal else buddy.bddfalse
                        for j in range(goals)]
            _values, lit = _bdd_values(
                strategy, inputs, [*state, *counters], buddy)
            controllable = {
                game_index: lit(strategy_output[game.input_names[game_index]])
                for game_index in nc_indices
            }
            next_state = [lit(next_lit)
                          for _cur, next_lit, _reset
                          in strategy.latches[:nstate]]
            next_counters = [lit(next_lit)
                             for _cur, next_lit, _reset
                             in strategy.latches[nstate:]]
            return controllable, next_state, next_counters

        def compile_game(controllable):
            game_inputs = [buddy.bddfalse] * len(game.inputs)
            for game_index, expression in uexpr.items():
                game_inputs[game_index] = expression
            for game_index, expression in controllable.items():
                game_inputs[game_index] = expression
            _values, lit = _bdd_values(
                game, game_inputs, state[:original_nlat], buddy)
            next_state = [
                lit(item["next_game_literal"])
                for item in sidecar["variables"]["state"]
            ]
            _next_values, next_lit = _bdd_values(
                game, game_inputs, next_state[:original_nlat], buddy)
            bad = buddy.bddfalse
            for bad_lit in game.bad:
                bad |= lit(bad_lit)
            for name, output_lit in zip(game.output_names, game.outputs):
                if name == "bad":
                    bad |= lit(output_lit)
            return game_inputs, lit, next_lit, next_state, bad

        # Reset membership is checked directly, independent of BuDDy.
        reset_inputs = [False] * len(certificate.aag.inputs)
        for item in sidecar["variables"]["state"]:
            reset_inputs[item["certificate_input"]] = bool(item["reset"])
        inv_lit = certificate.outputs["inv"]
        if not certificate.aag.eval_lit(inv_lit, reset_inputs, 0):
            raise AssertionError("reset state is outside inv")

        checks = 0
        for goal in range(goals):
            controllable, strategy_next, counter_next = compile_strategy(goal)
            game_inputs, game_lit, game_next_lit, game_next, bad = compile_game(
                controllable)
            current = compile_certificate(state, game_inputs)
            successor = compile_certificate(game_next, game_inputs)
            inv = current["inv"]
            violation = inv & (bad | -successor["inv"])
            for actual, expected in zip(strategy_next, game_next):
                violation |= inv & (actual ^ expected)
            violation |= inv & -current[f"move_{goal}"]

            at_goal = current[f"goal_{goal}"]
            for j, actual in enumerate(counter_next):
                expected = ((-at_goal if j == goal else buddy.bddfalse) |
                            (at_goal if j == (goal + 1) % goals
                             else buddy.bddfalse))
                violation |= inv & (actual ^ expected)

            covered = at_goal
            levels = sidecar["counts"]["levels_per_goal"][goal]
            nfair = sidecar["counts"]["fairness_assumptions"] or 1
            lower_next = successor[f"goal_{goal}"]
            for k in range(levels):
                for i in range(nfair):
                    name = f"x_{goal}_{k}_{i}"
                    layer = current[name] & -covered
                    if sidecar["counts"]["fairness_assumptions"]:
                        fair_lit = game.fairness[i]
                        # M1 games are state-based.  Sampling-latch games are
                        # handled by finding the documented fairness sample.
                        sample = next((item for item in sidecar["variables"]["state"]
                                       if item.get("source") == {
                                           "kind": "fairness", "index": i}),
                                      None)
                        fair_next = (game_next[sample["game_latch"]]
                                     if sample else game_next_lit(fair_lit))
                    else:
                        fair_next = buddy.bddtrue
                    allowed = lower_next | (successor[name] & -fair_next)
                    violation |= inv & -at_goal & layer & -allowed
                    covered |= current[name]
                    lower_next |= successor[name]
            violation |= inv & -at_goal & -covered
            if violation != buddy.bddfalse:
                raise AssertionError(
                    f"symbolic one-step certificate check failed for goal {goal}")
            checks += 1
        return checks
    finally:
        buddy.bdd_done()


def check_large_game(solver: pathlib.Path, path: pathlib.Path) -> int:
    text = path.read_text(encoding="utf-8")
    game = differential.parse_aag(text)
    result, cert_aag, sidecar = run_solver(solver, text)
    if result.returncode != 0:
        raise AssertionError(
            f"large game {path} is not realizable: rc={result.returncode} "
            f"stderr={result.stderr}")
    return check_one_step_symbolic(
        game, Certificate(cert_aag, sidecar), result.stdout)


def run_suite(solver: pathlib.Path, games: int, seed: int) -> dict[str, int]:
    rng = random.Random(seed)
    real = 0
    unreal = 0
    input_acceptance = 0
    exact_checks = 0
    one_step_checks = 0
    mutated = 0
    bad_records = 0
    rank_mutation_rejected = False
    for index in range(games):
        text = differential.make_random_game(rng, index)
        parsed = differential.parse_aag(text)
        bad_records += bool(parsed.bad)
        model = SampledGame(parsed)
        fixpoint = model.solve()
        expected_real = model.reset in fixpoint.winning
        result, cert_aag, sidecar = run_solver(solver, text)
        if result.returncode != (0 if expected_real else 1):
            raise AssertionError(
                f"game {index}: solver status {result.returncode}, "
                f"expected {'REAL' if expected_real else 'UNREAL'}: "
                f"{result.stderr}")
        input_acceptance += bool(model.samples)
        if not expected_real:
            unreal += 1
            assert sidecar["side"] == "environment"
            assert sidecar["reduction_semantics"] == "exact"
            assert sidecar["environment_counter_strategy_exported"] is True
            continue
        certificate = Certificate(cert_aag, sidecar)
        exact_checks += check_exact(model, fixpoint, certificate, expected_real)
        real += 1
        one_step_checks += check_one_step(model, certificate, result.stdout)

        if mutated == 0:
            original = certificate.overrides.copy()
            certificate.overrides["inv"] = (
                lambda state, _u, _c, reset=model.reset:
                state != reset and state in fixpoint.winning)
            expect_rejected(
                lambda: check_one_step(model, certificate, result.stdout),
                "drop reset from inv")
            certificate.overrides = original.copy()
            certificate.overrides["move_0"] = lambda _s, _u, _c: False
            expect_rejected(
                lambda: check_one_step(model, certificate, result.stdout),
                "weaken move relation")
            certificate.overrides = original
            mutated += 2

        if not rank_mutation_rejected:
            for goal, levels in enumerate(fixpoint.x):
                if len(levels) < 2:
                    continue
                original = certificate.overrides.copy()
                for i in range(len(levels[0])):
                    certificate.overrides[f"x_{goal}_0_{i}"] = f"x_{goal}_1_{i}"
                    certificate.overrides[f"x_{goal}_1_{i}"] = f"x_{goal}_0_{i}"
                try:
                    check_one_step(model, certificate, result.stdout)
                except AssertionError:
                    rank_mutation_rejected = True
                    mutated += 1
                certificate.overrides = original
                break
    if input_acceptance == 0:
        raise AssertionError("generator did not exercise sampling latches")
    if not rank_mutation_rejected:
        raise AssertionError("no swapped-level mutation was rejected")
    return {
        "games": games,
        "realizable": real,
        "unrealizable": unreal,
        "input_acceptance_games": input_acceptance,
        "bad_record_games": bad_records,
        "exact_predicate_evaluations": exact_checks,
        "one_step_checks": one_step_checks,
        "mutations_rejected": mutated,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--games", type=int, default=240)
    parser.add_argument("--seed", type=int, default=0xC3A71F1C)
    parser.add_argument("--large-game", type=pathlib.Path, action="append",
                        default=[])
    args = parser.parse_args()
    fields = []
    if args.games:
        summary = run_suite(args.solver.resolve(), args.games, args.seed)
        fields.extend(f"{key}={value}" for key, value in summary.items())
    large_checks = sum(check_large_game(args.solver.resolve(), path)
                       for path in args.large_game)
    if args.large_game:
        fields.extend((f"large_games={len(args.large_game)}",
                       f"large_symbolic_goal_checks={large_checks}"))
    print(" ".join(fields))
    return 0


def test_gr1_certificate() -> None:
    default = pathlib.Path(__file__).parents[1] / "build-oxidd/tlsfsolve"
    summary = run_suite(default.resolve(), 240, 0xC3A71F1C)
    assert summary["mutations_rejected"] == 3


if __name__ == "__main__":
    raise SystemExit(main())
