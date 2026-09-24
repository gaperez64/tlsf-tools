#!/usr/bin/env python3
"""Differential and mutation tests for the policy-free GR(1) region method."""

from __future__ import annotations

import argparse
import json
import pathlib
import random
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import test_gr1_certificate as certificate_test  # noqa: E402
import test_gr1_certcheck as certcheck_test  # noqa: E402
import test_gr1_differential as differential  # noqa: E402


def truth_table(builder: differential.AagBuilder, atoms: list[int],
                mask: int) -> int:
    """Build the Boolean function whose little-endian truth table is mask."""
    result = 0
    for assignment in range(1 << len(atoms)):
        if not (mask >> assignment) & 1:
            continue
        cube = 1
        for bit, atom in enumerate(atoms):
            literal = atom if (assignment >> bit) & 1 else atom ^ 1
            cube = builder.land(cube, literal)
        result = builder.lor(result, cube)
    return result


def enumerated_game(goal_mask: int, bad_mask: int) -> str:
    builder = differential.AagBuilder(
        ["u0", "controllable_c0"], [0])
    u, control = builder.inputs
    state = builder.latches[0]
    goal = truth_table(builder, [state], goal_mask)
    bad = truth_table(builder, [u, control], bad_mask)
    return builder.finish([control], bad, False, [goal], [])


def one_goal_game(*, bad: str = "false") -> str:
    builder = differential.AagBuilder(
        ["u0", "controllable_c0"], [0])
    _u, control = builder.inputs
    state = builder.latches[0]
    bad_lit = {"false": 0, "true": 1, "control": control}[bad]
    return builder.finish([control], bad_lit, False, [state], [])


def two_goal_game(*, break_goal_one: bool = False) -> str:
    builder = differential.AagBuilder(
        ["u0", "controllable_c0"], [0])
    _u, control = builder.inputs
    state = builder.latches[0]
    bad = builder.land(state, control ^ 1) if break_goal_one else 0
    return builder.finish(
        [control], bad, False, [state, state ^ 1], [])


def rank_shape_game() -> str:
    builder = differential.AagBuilder(
        ["u0", "controllable_c0"], [0, 0])
    first, second = builder.latches
    return builder.finish([1, first], 0, False, [second], [])


def fairness_game() -> str:
    # GF(q) is both the first assumption and the guarantee.  The second,
    # constant-true assumption forces distinct fairness-indexed X predicates:
    # q=0 may stutter only under the first disjunct when u keeps q false.
    builder = differential.AagBuilder(
        ["u0", "controllable_c0"], [0])
    uncontrollable, _control = builder.inputs
    state = builder.latches[0]
    return builder.finish(
        [uncontrollable], 0, False, [state], [state, 1])


def fairness_timing_game() -> str:
    # From reset (q0,q1)=(0,0), the deterministic transition reaches (1,0):
    # fairness is false in the current state but true in the successor, while
    # the current and successor goal are both false.
    return """\
aag 4 2 2 1 0 0 0 1 1
2
4
6 7 0
8 6 0
0
1
8
6
i0 u0
i1 controllable_c0
o0 bad
j0 justice_0
f0 fairness_0
"""


def frozen_reset_one_game() -> str:
    # The concrete reset-1 game q'=q, GF(q) is winning.  Changing only the
    # latch reset from 1 to its current-state literal 6 permits the losing
    # initial state q=0 as well.
    return """\
aag 3 2 1 1 0 0 0 1 0
2
4
6 6 1
0
1
6
i0 u0
i1 controllable_c0
o0 bad
j0 justice_0
"""


def solve_certificate(solver: pathlib.Path, root: pathlib.Path, label: str,
                      game_text: str) -> tuple[subprocess.CompletedProcess[str],
                                               pathlib.Path, pathlib.Path,
                                               pathlib.Path]:
    game = root / f"{label}-game.aag"
    certificate = root / f"{label}-certificate.aag"
    sidecar = root / f"{label}-certificate.json"
    game.write_text(game_text, encoding="utf-8")
    result = subprocess.run(
        [str(solver), "--certificate", str(certificate),
         "--certificate-json", str(sidecar), str(game)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        check=False, timeout=20)
    if result.returncode not in (0, 1):
        raise AssertionError(
            f"solver failed for {label}:\n{result.stdout}{result.stderr}")
    return result, game, certificate, sidecar


def run_region(checker: pathlib.Path, game: pathlib.Path,
               certificate: pathlib.Path, sidecar: pathlib.Path,
               *extra: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(checker), "--method", "region", "--certificate",
         str(certificate), "--certificate-json", str(sidecar), *extra,
         str(game)], text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=False, timeout=20)


def expect_region_verified(result: subprocess.CompletedProcess[str],
                           label: str) -> None:
    if (result.returncode != 0
            or result.stdout.splitlines()[-1:] != ["REGION_VERIFIED"]
            or "METHOD region REGION_VERIFIED version=gr1-region-v1"
            not in result.stdout):
        raise AssertionError(
            f"{label} did not REGION_VERIFY:\n{result.stdout}{result.stderr}")


def expect_region_failed(result: subprocess.CompletedProcess[str],
                         label: str, reason: str | None = None) -> None:
    if (result.returncode != 6
            or result.stdout.splitlines()[-1:] != ["REGION_FAILED"]
            or (reason is not None and reason not in result.stdout)):
        raise AssertionError(
            f"{label} was not rejected as a region proof:\n"
            f"{result.stdout}{result.stderr}")


def expect_invalid(result: subprocess.CompletedProcess[str], label: str,
                   reason: str) -> None:
    if (result.returncode != 4
            or result.stdout.splitlines()[-1:] != ["INVALID"]
            or reason not in result.stderr):
        raise AssertionError(
            f"{label} was not rejected as invalid:\n"
            f"{result.stdout}{result.stderr}")


def copy_mutation(root: pathlib.Path, label: str, text: str) -> pathlib.Path:
    path = root / f"mutation-{label}.aag"
    path.write_text(text, encoding="utf-8")
    return path


def differential_suite(solver: pathlib.Path, checker: pathlib.Path,
                       root: pathlib.Path, random_games: int,
                       seed: int) -> dict[str, int]:
    real = unreal = enumerated = random_checked = 0
    cases = [
        (f"enum-g{goal_mask}-b{bad_mask}",
         enumerated_game(goal_mask, bad_mask))
        for goal_mask in range(4)
        for bad_mask in range(16)
    ]
    rng = random.Random(seed)
    cases.extend(
        (f"random-{index}", differential.make_random_game(rng, index))
        for index in range(random_games)
    )
    for index, (label, game_text) in enumerate(cases):
        parsed = differential.parse_aag(game_text)
        model = certificate_test.SampledGame(parsed)
        explicit_real = model.reset in model.solve().winning
        solved, game, certificate, sidecar = solve_certificate(
            solver, root, label, game_text)
        if solved.returncode != (0 if explicit_real else 1):
            raise AssertionError(
                f"explicit/solver disagreement for {label}: "
                f"explicit_real={explicit_real}\n{solved.stderr}")
        checked = run_region(checker, game, certificate, sidecar)
        if explicit_real:
            expect_region_verified(checked, label)
            real += 1
        else:
            if checked.returncode == 0 or "REGION_VERIFIED" in checked.stdout:
                raise AssertionError(
                    f"UNREAL game {label} was region-verified:\n"
                    f"{checked.stdout}{checked.stderr}")
            unreal += 1
        enumerated += index < 64
        random_checked += index >= 64
    if not real or not unreal:
        raise AssertionError("differential family did not exercise both sides")
    return {
        "enumerated_games": enumerated,
        "random_games": random_checked,
        "real_region_verified": real,
        "unreal_never_verified": unreal,
    }


def mutation_suite(solver: pathlib.Path, checker: pathlib.Path,
                   root: pathlib.Path) -> dict[str, int]:
    mutations = 0
    _solved, game, certificate, sidecar = solve_certificate(
        solver, root, "base", one_goal_game())
    expect_region_verified(
        run_region(checker, game, certificate, sidecar), "base certificate")
    cert_text = certificate.read_text(encoding="utf-8")
    cert_json = json.loads(sidecar.read_text(encoding="utf-8"))
    literals = certcheck_test.output_literals(cert_text)

    # No safe control exists anywhere in W.
    non_total_game = root / "non-total-game.aag"
    non_total_game.write_text(one_goal_game(bad="true"), encoding="utf-8")
    expect_region_failed(
        run_region(checker, non_total_game, certificate, sidecar),
        "non-total region", "no joint control")
    mutations += 1

    # At q=0, c=0 is safe but does not progress; c=1 progresses to the goal
    # but is unsafe.  Separate existential checks would accept this mutation.
    incompatible_game = root / "incompatible-choice-game.aag"
    incompatible_game.write_text(
        one_goal_game(bad="control"), encoding="utf-8")
    expect_region_failed(
        run_region(checker, incompatible_game, certificate, sidecar),
        "incompatible control choices", "no joint control")
    mutations += 1

    inv_without_reset = certcheck_test.replace_output(
        cert_text, "inv", replacement=literals["goal_0"])
    expect_region_failed(
        run_region(checker, game,
                   copy_mutation(root, "reset", inv_without_reset), sidecar),
        "reset outside W", "reset state is outside region")
    mutations += 1

    support_violation = certcheck_test.xor_output_on_cube(
        cert_text, "inv", 0)
    expect_region_failed(
        run_region(checker, game,
                   copy_mutation(root, "support", support_violation), sidecar),
        "input-dependent proof predicate", "not state-only")
    mutations += 1

    _rank_solved, rank_game, rank_cert, rank_sidecar = solve_certificate(
        solver, root, "rank-shape", rank_shape_game())
    expect_region_verified(
        run_region(checker, rank_game, rank_cert, rank_sidecar),
        "rank-shape base")
    rank_text = rank_cert.read_text(encoding="utf-8")
    rank_json = json.loads(rank_sidecar.read_text(encoding="utf-8"))
    rank_literals = certcheck_test.output_literals(rank_text)
    counts = rank_json["counts"]["levels_per_goal"]
    rank_goal, rank_level = next(
        (goal, level)
        for goal, count in enumerate(counts)
        for level in range(count - 1)
        if rank_literals[f"y_{goal}_{level}"]
        != rank_literals[f"y_{goal}_{level + 1}"])
    swapped = certcheck_test.swap_outputs(
        rank_text, f"y_{rank_goal}_{rank_level}",
        f"y_{rank_goal}_{rank_level + 1}")
    for fairness in range(max(1, rank_json["counts"][
            "fairness_assumptions"])):
        swapped = certcheck_test.swap_outputs(
            swapped, f"x_{rank_goal}_{rank_level}_{fairness}",
            f"x_{rank_goal}_{rank_level + 1}_{fairness}")
    expect_region_failed(
        run_region(checker, rank_game,
                   copy_mutation(root, "rank-shape", swapped), rank_sidecar),
        "rank shape mutation")
    mutations += 1

    _fair_solved, fair_game, fair_cert, fair_sidecar = solve_certificate(
        solver, root, "fairness", fairness_game())
    expect_region_verified(
        run_region(checker, fair_game, fair_cert, fair_sidecar),
        "fairness timing base")
    fair_text = fair_cert.read_text(encoding="utf-8")
    fair_json = json.loads(fair_sidecar.read_text(encoding="utf-8"))
    fair_literals = certcheck_test.output_literals(fair_text)
    fair_goal, fair_level = next(
        (goal, level)
        for goal, count in enumerate(
            fair_json["counts"]["levels_per_goal"])
        for level in range(count)
        if fair_literals[f"x_{goal}_{level}_0"]
        != fair_literals[f"x_{goal}_{level}_1"])
    fairness_mutation = certcheck_test.swap_outputs(
        fair_text, f"x_{fair_goal}_{fair_level}_0",
        f"x_{fair_goal}_{fair_level}_1")
    expect_region_failed(
        run_region(checker, fair_game,
                   copy_mutation(root, "fairness", fairness_mutation),
                   fair_sidecar), "fairness-index/timing mutation",
        "no joint control")
    mutations += 1

    # Make every cumulative rank predicate constant true.  At reset the game
    # has F(current)=0, F(next)=1, and neither state is a goal.  Sampling
    # fairness in the current state would therefore admit rank stuttering;
    # the required successor sampling rejects it.
    (_timing_solved, timing_game, timing_cert,
     timing_sidecar) = solve_certificate(
         solver, root, "fairness-timing", fairness_timing_game())
    expect_region_verified(
        run_region(checker, timing_game, timing_cert, timing_sidecar),
        "fairness timing base")
    timing_text = timing_cert.read_text(encoding="utf-8")
    timing_json = json.loads(timing_sidecar.read_text(encoding="utf-8"))
    for level in range(timing_json["counts"]["levels_per_goal"][0]):
        timing_text = certcheck_test.replace_output(
            timing_text, f"y_0_{level}", replacement=1)
        timing_text = certcheck_test.replace_output(
            timing_text, f"x_0_{level}_0", replacement=1)
    expect_region_failed(
        run_region(
            checker, timing_game,
            copy_mutation(root, "fairness-current-vs-successor", timing_text),
            timing_sidecar),
        "current-vs-successor fairness discriminator", "no joint control")
    mutations += 1

    # The certificate was generated for the concrete reset-1 winning game.
    # A self-literal reset additionally permits q=0, which is permanently
    # losing and must be rejected as unsupported before any proof method runs.
    (_reset_solved, reset_game, reset_cert,
     reset_sidecar) = solve_certificate(
         solver, root, "reset-one", frozen_reset_one_game())
    expect_region_verified(
        run_region(checker, reset_game, reset_cert, reset_sidecar),
        "concrete reset-one base")
    uninitialized_game = root / "uninitialized-reset-game.aag"
    uninitialized_game.write_text(
        frozen_reset_one_game().replace("6 6 1\n", "6 6 6\n"),
        encoding="utf-8")
    expect_invalid(
        run_region(
            checker, uninitialized_game, reset_cert, reset_sidecar),
        "uninitialized game reset",
        "unsupported uninitialized game latch reset")
    mutations += 1

    # move_* is retained as interface evidence but is not a proof premise.
    ignored_move = certcheck_test.replace_output(
        cert_text, "move_0", replacement=0)
    expect_region_verified(
        run_region(checker, game,
                   copy_mutation(root, "ignored-move", ignored_move), sidecar),
        "ignored move relation")
    baseline_roots = run_region(
        checker, game, certificate, sidecar, "--stats")
    enlarged_move = certcheck_test.append_output_chain(
        cert_text, "move_0", 2048)
    enlarged_roots = run_region(
        checker, game, copy_mutation(root, "large-ignored-move", enlarged_move),
        sidecar, "--stats")
    expect_region_verified(baseline_roots, "baseline selected roots")
    expect_region_verified(enlarged_roots, "large ignored move cone")
    selected_fields = (
        "aig_gates_visited", "requested_roots", "region_game_roots",
        "region_certificate_roots")

    def selected_stats(result: subprocess.CompletedProcess[str]):
        line = next(line for line in result.stderr.splitlines()
                    if line.startswith("TLSFCERTCHECK_STATS "))
        return {
            name: int(re.search(rf"{name}=([0-9]+)", line).group(1))
            for name in selected_fields
        }

    if selected_stats(baseline_roots) != selected_stats(enlarged_roots):
        raise AssertionError(
            "region method evaluated the exclusive move cone: "
            f"baseline={selected_stats(baseline_roots)} "
            f"enlarged={selected_stats(enlarged_roots)}")

    # Goal 0 remains total while the goal-1 choice is split into incompatible
    # safe/progress controls.  Stats demonstrate separate all-zero and
    # one-hot-0 checks before the independent one-hot-1 failure.
    _two_solved, two_game, two_cert, two_sidecar = solve_certificate(
        solver, root, "two-goal", two_goal_game())
    two_mutated_game = root / "two-goal-mode-mutation.aag"
    two_mutated_game.write_text(
        two_goal_game(break_goal_one=True), encoding="utf-8")
    mode_result = run_region(
        checker, two_mutated_game, two_cert, two_sidecar, "--stats")
    expect_region_failed(
        mode_result, "per-mode mutation", "one-hot-1 rank layer")
    mode_status = {
        match.group(1): match.group(2)
        for match in re.finditer(
            r"TLSFCERTCHECK_REGION_MODE mode=([^ ]+).*status=([^\n ]+)",
            mode_result.stderr)
    }
    if mode_status != {
            "all-zero": "VERIFIED", "one-hot-0": "VERIFIED",
            "one-hot-1": "CERT_FAILED"}:
        raise AssertionError(
            f"scheduler modes were merged or skipped: {mode_status}\n"
            f"{mode_result.stderr}")
    mutations += 1

    stats_json = root / "region-result.json"
    stats_result = run_region(
        checker, game, certificate, sidecar, "--stats", "--json-out",
        str(stats_json))
    expect_region_verified(stats_result, "stats/JSON certificate")
    stats_line = next(
        (line for line in stats_result.stderr.splitlines()
         if line.startswith("TLSFCERTCHECK_STATS ")), "")
    required_stats = (
        "region_game_roots=", "region_certificate_roots=", "region_modes=2",
        "region_layers=", "region_mode_seconds=", "region_layer_seconds=",
        "policy_mode_builds=0", "final_status=REGION_VERIFIED")
    if not all(field in stats_line for field in required_stats):
        raise AssertionError(f"incomplete region stats: {stats_line}")
    payload = json.loads(stats_json.read_text(encoding="utf-8"))
    if (payload.get("format") != "tlsf-gr1-region-checkresult-v1"
            or payload.get("method") != "gr1-region-v1"
            or payload.get("verdict") != "REGION_VERIFIED"
            or payload.get("modes_checked") != 2
            or not payload.get("layers_checked")
            or not payload.get("roots", {}).get("game")
            or not payload.get("roots", {}).get("certificate")):
        raise AssertionError(f"invalid region result JSON: {payload}")

    return {
        "mutations_rejected": mutations,
        "incompatible_joint_choice_rejected": 1,
        "move_relation_not_trusted": 1,
        "all_zero_and_one_hot_zero_separate": 1,
        "stats_and_json_checked": 1,
    }


def run_suite(solver: pathlib.Path, checker: pathlib.Path, games: int,
              seed: int) -> dict[str, int]:
    # Keep test artifacts inside the configured build/work directory; this
    # suite never uses the system temporary directory.
    with tempfile.TemporaryDirectory(
            prefix="tlsf-region-", dir=pathlib.Path.cwd()) as directory:
        root = pathlib.Path(directory)
        summary = differential_suite(
            solver, checker, root, games, seed)
        summary.update(mutation_suite(solver, checker, root))
        return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--checker", type=pathlib.Path, required=True)
    parser.add_argument("--games", type=int, default=32)
    parser.add_argument("--seed", type=int, default=0xC3A7E610)
    args = parser.parse_args()
    summary = run_suite(
        args.solver.resolve(), args.checker.resolve(), args.games, args.seed)
    print(" ".join(f"{key}={value}" for key, value in summary.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
