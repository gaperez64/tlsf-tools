#!/usr/bin/env python3
"""Differential, mutation, and explicit-SCC tests for UNREAL certificates."""

from __future__ import annotations

import argparse
import json
import pathlib
import random
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import test_gr1_certificate as certificate_test  # noqa: E402
import test_gr1_certcheck as checker_test  # noqa: E402
import test_gr1_differential as differential  # noqa: E402


def run(command: list[str], expected: tuple[int, ...] = (0,)):
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False, timeout=20)
    if result.returncode not in expected:
        raise AssertionError(
            f"command returned {result.returncode}: {' '.join(command)}\n"
            f"{result.stdout}{result.stderr}")
    return result


def cyclic_sccs(nodes: set[tuple[int, int]],
                edges: dict[tuple[int, int], set[tuple[int, int]]]):
    index = 0
    indices: dict[tuple[int, int], int] = {}
    low: dict[tuple[int, int], int] = {}
    stack: list[tuple[int, int]] = []
    on_stack: set[tuple[int, int]] = set()
    result: list[set[tuple[int, int]]] = []

    def visit(node):
        nonlocal index
        indices[node] = low[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for successor in edges.get(node, set()) & nodes:
            if successor not in indices:
                visit(successor)
                low[node] = min(low[node], low[successor])
            elif successor in on_stack:
                low[node] = min(low[node], indices[successor])
        if low[node] != indices[node]:
            return
        component = set()
        while True:
            item = stack.pop()
            on_stack.remove(item)
            component.add(item)
            if item == node:
                break
        if len(component) > 1 or any(
                item in edges.get(item, set()) for item in component):
            result.append(component)

    for node in nodes:
        if node not in indices:
            visit(node)
    return result


def environment_policy_wins_explicit(game_text: str, policy_text: str,
                                     sidecar: dict) -> bool:
    """Independent finite-graph oracle for a Moore environment policy."""
    game = differential.parse_aag(game_text)
    model = certificate_test.SampledGame(game)
    policy = differential.parse_aag(policy_text)
    inputs = {name: index for index, name in enumerate(policy.input_names)}
    outputs = dict(zip(policy.output_names, policy.outputs))
    state_inputs = sidecar["inputs"]["state"]
    counters = sidecar["inputs"]["counter"]
    ncounter = len(counters)

    def evaluate(state: int, counter: int):
        values = [False] * len(policy.inputs)
        for item in state_inputs:
            values[item["policy_input"]] = bool(
                (state >> item["game_latch"]) & 1)
        for item in counters:
            values[item["policy_input"]] = bool(
                (counter >> item["fairness"]) & 1)
        uncontrollable = 0
        for bit, game_index in enumerate(model.nu_indices):
            name = game.input_names[game_index]
            if policy.eval_lit(outputs[name], values, 0):
                uncontrollable |= 1 << bit
        next_counter = 0
        for bit in range(ncounter):
            if policy.eval_lit(outputs[f"curr_next_{bit}"], values, 0):
                next_counter |= 1 << bit
        return uncontrollable, next_counter

    initial = (model.reset, 0)
    reachable = {initial}
    edges: dict[tuple[int, int], set[tuple[int, int]]] = {}
    work = [initial]
    while work:
        node = work.pop()
        state, counter = node
        uncontrollable, next_counter = evaluate(state, counter)
        successors = edges.setdefault(node, set())
        for control in range(1 << len(model.nc_indices)):
            unsafe, next_state = model.step(state, uncontrollable, control)
            if unsafe:
                continue
            successor = (next_state, next_counter)
            successors.add(successor)
            if successor not in reachable:
                reachable.add(successor)
                work.append(successor)

    fairness = [
        {node for node in reachable if model.source(source, node[0])}
        for source in model.fair_sources
    ]
    goals = [
        {node for node in reachable if model.source(source, node[0])}
        for source in model.goal_sources
    ]
    # The system satisfies the implication if it can stay safe while one
    # environment fairness set eventually disappears.
    for fair in fairness:
        allowed = reachable - fair
        if cyclic_sccs(allowed, edges):
            return False
    # Or it can stay safe and visit all fairness and justice sets infinitely.
    for component in cyclic_sccs(reachable, edges):
        if all(component & acceptance for acceptance in [*fairness, *goals]):
            return False
    return True


def solve_export(solver: pathlib.Path, root: pathlib.Path, index: int,
                 text: str):
    game = root / f"game-{index}.aag"
    policy = root / f"policy-{index}.aag"
    certificate = root / f"certificate-{index}.aag"
    game.write_text(text, encoding="utf-8")
    result = run([
        str(solver), "--semantics", "exact", "--policy", str(policy),
        "--certificate", str(certificate), str(game)
    ], (0, 1))
    return game, policy, certificate, result


def checker(checker_path: pathlib.Path, game: pathlib.Path,
            policy: pathlib.Path, certificate: pathlib.Path,
            method: str = "certificate", *extra: str):
    return run([
        str(checker_path), "--certificate", str(certificate), "--method",
        method, *extra, str(game), str(policy)
    ], (0, 1, 6))


def run_suite(solver: pathlib.Path, checker_path: pathlib.Path, games: int,
              seed: int):
    rng = random.Random(seed)
    real = unreal = explicit = 0
    rank_seed = None
    policy_seed = None
    with tempfile.TemporaryDirectory(prefix="tlsf-gr1-unreal-") as directory:
        root = pathlib.Path(directory)
        for index in range(games):
            text = differential.make_random_game(rng, index)
            parsed = differential.parse_aag(text)
            model = certificate_test.SampledGame(parsed)
            expected_real = model.reset in model.solve().winning
            game, policy, certificate, solved = solve_export(
                solver, root, index, text)
            if solved.returncode != (0 if expected_real else 1):
                raise AssertionError(
                    f"solver/oracle disagreement at game {index}: "
                    f"{solved.stderr}")
            cert_sidecar = json.loads(
                pathlib.Path(str(certificate) + ".json").read_text())
            policy_sidecar = json.loads(
                pathlib.Path(str(policy) + ".json").read_text())
            if expected_real:
                real += 1
                assert cert_sidecar["side"] == "system"
                assert policy_sidecar["side"] == "system"
                continue
            unreal += 1
            assert cert_sidecar["side"] == "environment"
            assert cert_sidecar["reduction_semantics"] == "exact"
            assert cert_sidecar["strategy_semantics"] == "moore"
            assert cert_sidecar["environment_counter_strategy_exported"] is True
            assert policy_sidecar["side"] == "environment"
            assert checker(checker_path, game, policy, certificate,
                           "both").returncode == 0
            specialized = checker(
                checker_path, game, policy, certificate, "certificate")
            oracle = checker(
                checker_path, game, policy, certificate, "certificate",
                "--test-unspecialized-policy")
            if specialized.returncode != oracle.returncode:
                raise AssertionError(
                    "environment specialized/oracle genuine mismatch:\n"
                    f"{specialized.stdout}{oracle.stdout}")
            assert environment_policy_wins_explicit(
                text, policy.read_text(), policy_sidecar)
            explicit += 1
            certificate_aag = differential.parse_aag(certificate.read_text())
            if rank_seed is None and any(
                    name.startswith("x_") and literal >= 2
                    for name, literal in zip(certificate_aag.output_names,
                                             certificate_aag.outputs)):
                rank_seed = (game, policy, certificate)
            if policy_seed is None:
                policy_text = policy.read_text()
                policy_outputs = checker_test.output_literals(policy_text)
                for name in (candidate for candidate in policy_outputs
                             if not candidate.startswith("curr_next_")):
                    for replacement in (0, 1):
                        candidate = checker_test.replace_output(
                            policy_text, name, replacement=replacement)
                        if not environment_policy_wins_explicit(
                                text, candidate, policy_sidecar):
                            policy_seed = (game, policy, certificate, text,
                                           policy_sidecar, candidate)
                            break
                    if policy_seed:
                        break

        if not real or not unreal:
            raise AssertionError("differential suite did not cover both verdicts")
        if rank_seed is None:
            raise AssertionError("no UNREAL rank mutation seed")
        if policy_seed is None:
            raise AssertionError("no explicit losing counter-strategy mutation")

        game, policy, certificate = rank_seed
        cert_text = certificate.read_text()
        cert_outputs = checker_test.output_literals(cert_text)
        mutations = [(
            "region", checker_test.replace_output(cert_text, "inv", invert=True)
        )]
        rank_mutation = None
        for rank_name in (name for name in cert_outputs
                          if name.startswith(("x_", "y_", "z_"))):
            for replacement, invert in ((0, False), (1, False), (None, True)):
                candidate = checker_test.replace_output(
                    cert_text, rank_name, replacement=replacement,
                    invert=invert)
                probe = root / "rank-probe.aag"
                probe.write_text(candidate)
                shutil.copyfile(str(certificate) + ".json",
                                str(probe) + ".json")
                if checker(checker_path, game, policy, probe).returncode == 6:
                    rank_mutation = candidate
                    break
            if rank_mutation:
                break
        if rank_mutation is None:
            raise AssertionError("no rejected dual-rank mutation")
        mutations.append(("rank", rank_mutation))
        for label, text in mutations:
            mutated = root / f"mutated-{label}.aag"
            mutated.write_text(text)
            shutil.copyfile(str(certificate) + ".json", str(mutated) + ".json")
            verdict = checker(checker_path, game, policy, mutated)
            if verdict.returncode != 6:
                raise AssertionError(
                    f"{label} mutation was not CERT_FAILED:\n{verdict.stdout}")
            oracle = checker(
                checker_path, game, policy, mutated, "certificate",
                "--test-unspecialized-policy")
            if oracle.returncode != verdict.returncode:
                raise AssertionError(
                    f"environment {label} specialized/oracle mismatch:\n"
                    f"{verdict.stdout}{oracle.stdout}")

        (game, policy, certificate, _game_text, _policy_sidecar,
         losing_mutation) = policy_seed
        mutated_policy = root / "mutated-policy.aag"
        mutated_policy.write_text(losing_mutation)
        shutil.copyfile(str(policy) + ".json", str(mutated_policy) + ".json")
        certificate_only = checker(
            checker_path, game, mutated_policy, certificate, "certificate")
        if certificate_only.returncode != 6:
            raise AssertionError("policy mutation did not produce CERT_FAILED")
        policy_oracle = checker(
            checker_path, game, mutated_policy, certificate, "certificate",
            "--test-unspecialized-policy")
        if policy_oracle.returncode != certificate_only.returncode:
            raise AssertionError(
                "environment policy specialized/oracle mismatch:\n"
                f"{certificate_only.stdout}{policy_oracle.stdout}")
        decided = checker(checker_path, game, mutated_policy, certificate,
                          "both")
        if decided.returncode != 1:
            raise AssertionError(
                f"deciding route did not REFUTE mutation:\n{decided.stdout}")

        strict_cert = root / "strict-certificate.aag"
        strict_policy = root / "strict-policy.aag"
        strict = run([
            str(solver), "--semantics", "strict", "--policy",
            str(strict_policy), "--certificate", str(strict_cert), str(game)
        ], (2,))
        assert "refusing UNREAL" in strict.stderr
        assert not strict_cert.exists() and not strict_policy.exists()

    return {
        "games": games,
        "realizable_without_environment_certificate": real,
        "unrealizable_verified": unreal,
        "explicit_scc_agreements": explicit,
        "region_mutations_cert_failed": 1,
        "rank_mutations_cert_failed": 1,
        "counterstrategy_mutations_refuted": 1,
        "strict_unreal_exports_refused": 1,
        "specialized_policy_oracle_agreements": unreal + 3,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--checker", type=pathlib.Path, required=True)
    parser.add_argument("--games", type=int, default=120)
    parser.add_argument("--seed", type=int, default=0x5A17D00D)
    args = parser.parse_args()
    summary = run_suite(args.solver.resolve(), args.checker.resolve(),
                        args.games, args.seed)
    print(" ".join(f"{key}={value}" for key, value in summary.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
