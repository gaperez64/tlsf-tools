#!/usr/bin/env python3
"""Differential and mutation tests for tlsfcertcheck.

The explicit oracle below composes the exported combinational policy with the
sampled game and checks reachable SCCs.  It shares only the tiny random-game
generator/AAG evaluator with test_gr1_differential.py; it does not use the C
checker's BDD algorithms or certificate conditions.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import random
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import test_gr1_certificate as certificate_test  # noqa: E402
import test_gr1_differential as differential  # noqa: E402


def _sections(text: str):
    lines = text.splitlines()
    header = [int(item) for item in lines[0].split()[1:]]
    header += [0] * (9 - len(header))
    _m, ni, nl, no, na, nb, nc, nj, nf = header[:9]
    output_start = 1 + ni + nl
    position = output_start + no + nb + nc
    justice_sizes = [int(lines[position + i]) for i in range(nj)]
    position += nj + sum(justice_sizes) + nf
    gate_start = position
    symbol_start = gate_start + na
    names = {}
    for line in lines[symbol_start:]:
        if line == "c":
            break
        if line.startswith("o"):
            label, name = line.split(maxsplit=1)
            names[name] = int(label[1:])
    return lines, header, output_start, gate_start, symbol_start, names


def replace_output(text: str, name: str, replacement=None, *, invert=False) -> str:
    lines, _header, output_start, _gates, _symbols, names = _sections(text)
    index = names[name]
    literal = int(lines[output_start + index])
    if invert:
        literal ^= 1
    if replacement is not None:
        literal = replacement
    lines[output_start + index] = str(literal)
    return "\n".join(lines) + "\n"


def swap_outputs(text: str, left: str, right: str) -> str:
    lines, _header, output_start, _gates, _symbols, names = _sections(text)
    li, ri = names[left], names[right]
    lines[output_start + li], lines[output_start + ri] = (
        lines[output_start + ri], lines[output_start + li])
    return "\n".join(lines) + "\n"


def output_literals(text: str) -> dict[str, int]:
    lines, _header, output_start, _gates, _symbols, names = _sections(text)
    return {name: int(lines[output_start + index])
            for name, index in names.items()}


def xor_output_on_cube(text: str, name: str, assignment: int) -> str:
    lines, header, output_start, _gate_start, symbol_start, names = _sections(text)
    maxvar, ni, nl, _no, na = header[:5]
    if nl:
        raise AssertionError("policy mutation expects a combinational AAG")
    atoms = []
    for index in range(ni):
        literal = int(lines[1 + index])
        atoms.append(literal if (assignment >> index) & 1 else literal ^ 1)
    gates: list[str] = []

    def land(left: int, right: int) -> int:
        nonlocal maxvar
        maxvar += 1
        literal = 2 * maxvar
        gates.append(f"{literal} {left} {right}")
        return literal

    cube = 1
    for atom in atoms:
        cube = atom if cube == 1 else land(cube, atom)
    output_line = output_start + names[name]
    old = int(lines[output_line])
    left = land(old, cube ^ 1)
    right = land(old ^ 1, cube)
    xor = land(left ^ 1, right ^ 1) ^ 1
    lines[output_line] = str(xor)
    fields = lines[0].split()
    fields[1] = str(maxvar)
    fields[5] = str(na + len(gates))
    lines[0] = " ".join(fields)
    lines[symbol_start:symbol_start] = gates
    return "\n".join(lines) + "\n"


def append_output_chain(text: str, name: str, count: int, *,
                        malformed: bool = False) -> str:
    """Replace one output with an exclusive, deliberately large AND cone."""
    lines, header, output_start, _gate_start, symbol_start, names = _sections(
        text)
    maxvar, ni, _nl, _no, na = header[:5]
    seed = int(lines[1]) if ni else 1
    current = seed
    gates = []
    for index in range(count):
        maxvar += 1
        lhs = 2 * maxvar
        right = seed if index & 1 else seed ^ 1
        gates.append(f"{lhs} {current} {right}")
        current = lhs
    if malformed:
        lhs, left, _right = gates[-1].split()
        gates[-1] = f"{lhs} {left} {2 * (maxvar + 1)}"
    lines[output_start + names[name]] = str(current)
    fields = lines[0].split()
    fields[1] = str(maxvar)
    fields[5] = str(na + len(gates))
    lines[0] = " ".join(fields)
    lines[symbol_start:symbol_start] = gates
    return "\n".join(lines) + "\n"


def xor_output_in_counter_mode(text: str, name: str, mode: int) -> str:
    lines, header, output_start, _gate_start, symbol_start, names = _sections(
        text)
    maxvar, ni, nl, _no, na = header[:5]
    if nl:
        raise AssertionError("policy mutation expects a combinational AAG")
    input_names = {}
    for line in lines[symbol_start:]:
        if line == "c":
            break
        if line.startswith("i"):
            label, input_name = line.split(maxsplit=1)
            input_names[input_name] = int(label[1:])
    counters = sorted(
        ((int(input_name.removeprefix("curr_")), index)
         for input_name, index in input_names.items()
         if input_name.startswith("curr_")))
    if not counters:
        raise AssertionError("policy has no counter inputs")
    gates = []

    def land(left: int, right: int) -> int:
        nonlocal maxvar
        maxvar += 1
        literal = 2 * maxvar
        gates.append(f"{literal} {left} {right}")
        return literal

    cube = 1
    for counter, index in counters:
        literal = int(lines[1 + index])
        atom = literal if counter == mode else literal ^ 1
        cube = atom if cube == 1 else land(cube, atom)
    output_line = output_start + names[name]
    old = int(lines[output_line])
    left = land(old, cube ^ 1)
    right = land(old ^ 1, cube)
    lines[output_line] = str(land(left ^ 1, right ^ 1) ^ 1)
    fields = lines[0].split()
    fields[1] = str(maxvar)
    fields[5] = str(na + len(gates))
    lines[0] = " ".join(fields)
    lines[symbol_start:symbol_start] = gates
    return "\n".join(lines) + "\n"


def wrap_output_in_selectors(text: str, name: str, repetitions: int) -> str:
    lines, header, output_start, _gate_start, symbol_start, names = _sections(
        text)
    maxvar, _ni, _nl, _no, na = header[:5]
    input_names = {}
    for line in lines[symbol_start:]:
        if line == "c":
            break
        if line.startswith("i"):
            label, input_name = line.split(maxsplit=1)
            input_names[input_name] = int(label[1:])
    counter_name = min(name for name in input_names
                       if name.startswith("curr_"))
    selector = int(lines[1 + input_names[counter_name]])
    current = int(lines[output_start + names[name]])
    gates = []

    def land(left: int, right: int) -> int:
        nonlocal maxvar
        maxvar += 1
        literal = 2 * maxvar
        gates.append(f"{literal} {left} {right}")
        return literal

    for _ in range(repetitions):
        positive = land(current, selector)
        negative = land(current, selector ^ 1)
        current = land(positive ^ 1, negative ^ 1) ^ 1
    lines[output_start + names[name]] = str(current)
    fields = lines[0].split()
    fields[1] = str(maxvar)
    fields[5] = str(na + len(gates))
    lines[0] = " ".join(fields)
    lines[symbol_start:symbol_start] = gates
    return "\n".join(lines) + "\n"


def checker_stats(result: subprocess.CompletedProcess[str]) -> dict[str, int]:
    line = next((line for line in result.stderr.splitlines()
                 if line.startswith("TLSFCERTCHECK_STATS ")), None)
    if line is None:
        raise AssertionError(f"checker did not emit --stats output: {result}")
    integer_names = (
        "aig_gates_visited|requested_roots|peak_live_nodes_sample|"
        "policy_mode_builds|policy_counter_constants|"
        "policy_specialized_gates|policy_unspecialized_gates|"
        "successor_substitutions|successor_applications")
    return {name: int(value) for name, value in re.findall(
        rf"({integer_names})=([0-9]+)", line)}


def policy_analysis_explicit(game_text: str, policy_text: str):
    parsed = differential.parse_aag(game_text)
    model = certificate_test.SampledGame(parsed)
    policy = differential.parse_aag(policy_text)
    goals = [
        frozenset(state for state in model.states if model.source(source, state))
        for source in model.goal_sources
    ]
    fairness = [
        frozenset(state for state in model.states if model.source(source, state))
        for source in model.fair_sources
    ]
    state_names = [f"l{i}" for i in range(len(parsed.latches))]
    for kind, index, _lit in model.samples:
        if kind == "justice":
            state_names.append(f"__tlsf_gr1_sample_justice_{index}_0")
        else:
            state_names.append(f"__tlsf_gr1_sample_fairness_{index}")
    input_index = {name: i for i, name in enumerate(policy.input_names)}
    outputs = dict(zip(policy.output_names, policy.outputs))
    initial = model.reset  # all counter bits reset to zero
    reachable = {initial}
    queue = collections.deque([initial])
    adjacency: dict[int, set[int]] = collections.defaultdict(set)
    game_state_of: dict[int, int] = {initial: model.reset}
    unsafe = False
    seen_letters: set[int] = set()
    while queue:
        combined = queue.popleft()
        state_mask = (1 << model.nstate) - 1
        state = combined & state_mask
        counters = combined >> model.nstate
        for u in range(1 << len(model.nu_indices)):
            values = [False] * len(policy.inputs)
            for bit, name in enumerate(state_names):
                values[input_index[name]] = bool((state >> bit) & 1)
            for goal in range(len(goals)):
                values[input_index[f"curr_{goal}"]] = bool(
                    (counters >> goal) & 1)
            for bit, game_index in enumerate(model.nu_indices):
                values[input_index[parsed.input_names[game_index]]] = bool(
                    (u >> bit) & 1)
            letter = sum(value << bit for bit, value in enumerate(values))
            seen_letters.add(letter)
            control = 0
            for bit, game_index in enumerate(model.nc_indices):
                name = parsed.input_names[game_index]
                if policy.eval_lit(outputs[name], values, 0):
                    control |= 1 << bit
            is_bad, next_state = model.step(state, u, control)
            unsafe |= is_bad
            next_counter = 0
            for goal in range(len(goals)):
                if policy.eval_lit(outputs[f"curr_next_{goal}"], values, 0):
                    next_counter |= 1 << goal
            successor = next_state | (next_counter << model.nstate)
            adjacency[combined].add(successor)
            game_state_of[successor] = next_state
            if successor not in reachable:
                reachable.add(successor)
                queue.append(successor)
    if unsafe:
        return False, seen_letters

    for goal in goals:
        allowed = {node for node in reachable if game_state_of[node] not in goal}
        for component in differential._tarjan(allowed, adjacency):
            cyclic = (len(component) > 1
                      or component[0] in adjacency[component[0]])
            if not cyclic:
                continue
            if all(any(game_state_of[node] in fair for node in component)
                   for fair in fairness):
                return False, seen_letters
            if not fairness:
                return False, seen_letters
    return True, seen_letters


def policy_wins_explicit(game_text: str, policy_text: str) -> bool:
    return policy_analysis_explicit(game_text, policy_text)[0]


def run_checker(checker: pathlib.Path, game: pathlib.Path, policy: pathlib.Path,
                *extra: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(checker), *extra, str(game), str(policy)], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False, timeout=20)


def run_suite(solver: pathlib.Path, checker: pathlib.Path, games: int,
              seed: int) -> dict[str, int]:
    rng = random.Random(seed)
    generated = realizable = genuine = policy_mutations = agreements = 0
    winning_mutations = losing_mutations = 0
    sampled_acceptance_verified = 0
    rare_state_rejected = 0
    default_output_unchanged = 0
    successor_rebuild_agreements = 0
    rank_seed = None
    fairness_seed = None
    inv_seed = None
    with tempfile.TemporaryDirectory(prefix="tlsf-certcheck-") as directory:
        root = pathlib.Path(directory)
        for index in range(games):
            game_text = differential.make_random_game(rng, index)
            parsed = differential.parse_aag(game_text)
            model = certificate_test.SampledGame(parsed)
            expected_real = model.reset in model.solve().winning
            generated += 1
            if not expected_real:
                continue
            realizable += 1
            game = root / f"game-{index}.aag"
            policy = root / f"policy-{index}.aag"
            cert = root / f"cert-{index}.aag"
            cert_json = root / f"cert-{index}.aag.json"
            game.write_text(game_text, encoding="utf-8")
            result = subprocess.run(
                [str(solver), "--policy", str(policy), "--certificate",
                 str(cert), str(game)],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False, timeout=20)
            if result.returncode != 0:
                raise AssertionError(f"solver failed on realizable game {index}")
            if not default_output_unchanged:
                plain = subprocess.run(
                    [str(solver), str(game)], text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    check=False, timeout=20)
                if plain.returncode != 0 or plain.stdout != result.stdout:
                    raise AssertionError(
                        "--policy/--certificate changed tlsfsolve stdout")
                default_output_unchanged = 1
            checked = run_checker(
                checker, game, policy, "--certificate", str(cert),
                "--method", "both")
            if checked.returncode != 0:
                raise AssertionError(
                    f"genuine game {index} rejected:\n{checked.stdout}"
                    f"{checked.stderr}")
            genuine += 1
            cached_certificate = run_checker(
                checker, game, policy, "--certificate", str(cert),
                "--method", "certificate")
            rebuilt_certificate = run_checker(
                checker, game, policy, "--certificate", str(cert),
                "--method", "certificate", "--test-rebuild-successor")
            if cached_certificate.returncode != rebuilt_certificate.returncode:
                raise AssertionError(
                    f"successor-cache genuine status mismatch on game "
                    f"{index}:\n{cached_certificate.stdout}"
                    f"{rebuilt_certificate.stdout}")
            successor_rebuild_agreements += 1
            sampled_acceptance_verified += bool(model.samples)

            policy_text = policy.read_text(encoding="utf-8")
            controllable = parsed.input_names[model.nc_indices[0]]
            mutations = [
                ("invert-control",
                 replace_output(policy_text, controllable, invert=True)),
                ("zero-control",
                 replace_output(policy_text, controllable, replacement=0)),
            ]
            if "curr_next_1" in output_literals(policy_text):
                mutations.append((
                    "zero-curr-next-1",
                    replace_output(policy_text, "curr_next_1", replacement=0)))
            for label, corrupt_text in mutations:
                corrupt = root / f"policy-{index}-{label}.aag"
                corrupt.write_text(corrupt_text, encoding="utf-8")
                # Reuse the genuine mapping: mutations preserve the interface.
                pathlib.Path(str(corrupt) + ".json").write_text(
                    pathlib.Path(str(policy) + ".json").read_text(
                        encoding="utf-8"), encoding="utf-8")
                explicit = policy_wins_explicit(game_text, corrupt_text)
                expected = 0 if explicit else 1
                closed = run_checker(
                    checker, game, corrupt, "--method", "closed-loop")
                if closed.returncode != expected:
                    raise AssertionError(
                        f"explicit/closed-loop disagreement on game {index} "
                        f"mutation {label}: explicit={explicit}\n"
                        f"{closed.stdout}{closed.stderr}")
                certificate = run_checker(
                    checker, game, corrupt, "--certificate", str(cert),
                    "--method", "certificate")
                if certificate.returncode not in (0, 6):
                    raise AssertionError(
                        f"certificate unsoundly decided policy mutation "
                        f"{label} on game {index}:\n"
                        f"{certificate.stdout}{certificate.stderr}")
                rebuilt_certificate = run_checker(
                    checker, game, corrupt, "--certificate", str(cert),
                    "--method", "certificate", "--test-rebuild-successor")
                if certificate.returncode != rebuilt_certificate.returncode:
                    raise AssertionError(
                        "successor-cache policy-mutation status mismatch on "
                        f"game {index} mutation {label}:\n"
                        f"{certificate.stdout}{rebuilt_certificate.stdout}")
                successor_rebuild_agreements += 1
                for method in ("both", "auto"):
                    combined = run_checker(
                        checker, game, corrupt, "--certificate", str(cert),
                        "--method", method)
                    if combined.returncode != expected:
                        raise AssertionError(
                            f"{method} disagrees with explicit oracle on game "
                            f"{index} mutation {label}: explicit={explicit}\n"
                            f"{combined.stdout}{combined.stderr}")
                policy_mutations += 1
                agreements += 1
                winning_mutations += explicit
                losing_mutations += not explicit

            if not rare_state_rejected:
                _wins, reachable_letters = policy_analysis_explicit(
                    game_text, policy_text)
                for letter in sorted(reachable_letters)[:128]:
                    rare_text = xor_output_on_cube(
                        policy_text, controllable, letter)
                    if policy_wins_explicit(game_text, rare_text):
                        continue
                    rare = root / f"policy-{index}-rare.aag"
                    rare.write_text(rare_text, encoding="utf-8")
                    (root / f"policy-{index}-rare.aag.json").write_text(
                        (root / f"policy-{index}.aag.json").read_text(
                            encoding="utf-8"), encoding="utf-8")
                    rare_check = run_checker(
                        checker, game, rare, "--method", "closed-loop")
                    if rare_check.returncode != 1:
                        raise AssertionError(
                            "single-letter corruption was not refuted:\n"
                            f"{rare_check.stdout}{rare_check.stderr}")
                    rare_certificate = run_checker(
                        checker, game, rare, "--certificate", str(cert),
                        "--method", "certificate")
                    if rare_certificate.returncode not in (0, 6):
                        raise AssertionError(
                            "certificate unsoundly refuted a single-letter "
                            f"mutation:\n{rare_certificate.stdout}"
                            f"{rare_certificate.stderr}")
                    rebuilt_rare = run_checker(
                        checker, game, rare, "--certificate", str(cert),
                        "--method", "certificate",
                        "--test-rebuild-successor")
                    if rare_certificate.returncode != rebuilt_rare.returncode:
                        raise AssertionError(
                            "successor-cache rare-mutation status mismatch:\n"
                            f"{rare_certificate.stdout}{rebuilt_rare.stdout}")
                    successor_rebuild_agreements += 1
                    for method in ("both", "auto"):
                        rare_combined = run_checker(
                            checker, game, rare, "--certificate", str(cert),
                            "--method", method)
                        if rare_combined.returncode != 1:
                            raise AssertionError(
                                f"{method} missed a losing single-letter "
                                f"mutation:\n{rare_combined.stdout}"
                                f"{rare_combined.stderr}")
                    rare_state_rejected = 1
                    break
            sidecar = json.loads(cert_json.read_text(encoding="utf-8"))
            literals = output_literals(cert.read_text(encoding="utf-8"))
            distinct_rank = any(
                literals[f"y_{goal}_{level}"]
                != literals[f"y_{goal}_{level + 1}"]
                for goal, count in enumerate(
                    sidecar["counts"]["levels_per_goal"])
                for level in range(count - 1))
            distinct_fair = any(
                literals[f"x_{goal}_{level}_0"]
                != literals[f"x_{goal}_{level}_1"]
                for goal, count in enumerate(
                    sidecar["counts"]["levels_per_goal"])
                for level in range(count)
            ) if sidecar["counts"]["fairness_assumptions"] >= 2 else False
            if rank_seed is None and distinct_rank:
                rank_seed = (game, policy, cert, sidecar)
            if fairness_seed is None and distinct_fair:
                fairness_seed = (game, policy, cert, sidecar)
            if inv_seed is None and literals["inv"] != 1:
                inv_seed = (game, policy, cert, sidecar)

        if rank_seed is None:
            # A deterministic two-step chain has genuinely distinct mu levels.
            builder = differential.AagBuilder(
                ["u0", "controllable_c0"], [0, 0])
            chain_game = builder.finish(
                [1, builder.latches[0]], None, False,
                [builder.latches[1]], [])
            game = root / "rank-game.aag"
            policy = root / "rank-policy.aag"
            cert = root / "rank-cert.aag"
            cert_json = root / "rank-cert.aag.json"
            game.write_text(chain_game, encoding="utf-8")
            result = subprocess.run(
                [str(solver), "--policy", str(policy), "--certificate",
                 str(cert), str(game)],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False, timeout=20)
            if result.returncode != 0:
                raise AssertionError("solver failed on rank mutation fixture")
            sidecar = json.loads(cert_json.read_text(encoding="utf-8"))
            rank_seed = (game, policy, cert, sidecar)
        if fairness_seed is None:
            raise AssertionError("random suite did not provide a fairness seed")
        if inv_seed is None:
            raise AssertionError("random suite did not provide a nontrivial inv")
        if not rare_state_rejected:
            raise AssertionError(
                "random suite did not expose a losing single-letter mutation")

        # Keep the former post-compilation restrict path as a hidden oracle.
        # It must agree with direct constant-input compilation on a genuine
        # certificate and on an all-zero-only policy mutation.
        game, policy, cert, sidecar = rank_seed
        genuine_specialized = run_checker(
            checker, game, policy, "--certificate", str(cert), "--method",
            "certificate")
        genuine_oracle = run_checker(
            checker, game, policy, "--certificate", str(cert), "--method",
            "certificate", "--test-unspecialized-policy")
        if genuine_specialized.returncode != genuine_oracle.returncode:
            raise AssertionError(
                "specialized/unspecialized genuine status mismatch:\n"
                f"{genuine_specialized.stdout}{genuine_oracle.stdout}")
        genuine_rebuilt = run_checker(
            checker, game, policy, "--certificate", str(cert), "--method",
            "certificate", "--test-rebuild-successor")
        if genuine_specialized.returncode != genuine_rebuilt.returncode:
            raise AssertionError(
                "successor-cache rank-seed status mismatch:\n"
                f"{genuine_specialized.stdout}{genuine_rebuilt.stdout}")
        successor_rebuild_agreements += 1
        policy_text = policy.read_text(encoding="utf-8")
        policy_outputs = output_literals(policy_text)
        all_zero_agreement = 0
        for output_name in policy_outputs:
            candidate_text = xor_output_in_counter_mode(
                policy_text, output_name, -1)
            candidate = root / f"policy-all-zero-{output_name}.aag"
            candidate.write_text(candidate_text, encoding="utf-8")
            pathlib.Path(str(candidate) + ".json").write_text(
                pathlib.Path(str(policy) + ".json").read_text(
                    encoding="utf-8"), encoding="utf-8")
            specialized = run_checker(
                checker, game, candidate, "--certificate", str(cert),
                "--method", "certificate")
            oracle = run_checker(
                checker, game, candidate, "--certificate", str(cert),
                "--method", "certificate", "--test-unspecialized-policy")
            if specialized.returncode != oracle.returncode:
                raise AssertionError(
                    "all-zero specialized/oracle status mismatch for "
                    f"{output_name}:\n{specialized.stdout}{oracle.stdout}")
            rebuilt = run_checker(
                checker, game, candidate, "--certificate", str(cert),
                "--method", "certificate", "--test-rebuild-successor")
            if specialized.returncode != rebuilt.returncode:
                raise AssertionError(
                    "successor-cache all-zero status mismatch for "
                    f"{output_name}:\n{specialized.stdout}{rebuilt.stdout}")
            successor_rebuild_agreements += 1
            if oracle.returncode == 6:
                all_zero_agreement = 1
                break
        if not all_zero_agreement:
            raise AssertionError("no all-zero-only policy mutation was rejected")

        # A large semantically redundant selector stresses the policy cone.
        # The diagnostics prove every specialized build received counter
        # constants and that certificate-only checking built no full policy.
        control_name = next(name for name in policy_outputs
                            if not name.startswith("curr_next_"))
        selector = root / "policy-large-counter-selector.aag"
        selector.write_text(wrap_output_in_selectors(
            policy_text, control_name, 512), encoding="utf-8")
        pathlib.Path(str(selector) + ".json").write_text(
            pathlib.Path(str(policy) + ".json").read_text(encoding="utf-8"),
            encoding="utf-8")
        selector_result = run_checker(
            checker, game, selector, "--certificate", str(cert), "--method",
            "certificate", "--stats")
        if selector_result.returncode != 0:
            raise AssertionError(
                "equivalent large selector was not verified:\n"
                f"{selector_result.stdout}{selector_result.stderr}")
        selector_stats = checker_stats(selector_result)
        selector_rebuilt = run_checker(
            checker, game, selector, "--certificate", str(cert), "--method",
            "certificate", "--stats", "--test-rebuild-successor")
        if selector_result.returncode != selector_rebuilt.returncode:
            raise AssertionError(
                "successor-cache large-selector status mismatch:\n"
                f"{selector_result.stdout}{selector_rebuilt.stdout}")
        successor_rebuild_agreements += 1
        rebuilt_stats = checker_stats(selector_rebuilt)
        goal_count = sidecar["counts"]["goals"]
        if (selector_stats.get("policy_mode_builds") != goal_count + 1
                or selector_stats.get("policy_counter_constants")
                != (goal_count + 1) * goal_count
                or selector_stats.get("policy_unspecialized_gates") != 0):
            raise AssertionError(
                f"selector was not built from per-mode constants: "
                f"{selector_stats}")
        if (selector_stats.get("successor_substitutions") != goal_count + 1
                or rebuilt_stats.get("successor_substitutions")
                != rebuilt_stats.get("successor_applications")
                or selector_stats.get("successor_applications")
                != rebuilt_stats.get("successor_applications")
                or selector_stats.get("successor_substitutions", 0)
                >= rebuilt_stats.get("successor_substitutions", 0)):
            raise AssertionError(
                "successor substitution was not reused once per mode: "
                f"cached={selector_stats} rebuilt={rebuilt_stats}")

        # move_* remains part of the certificate interface, but fixed-policy
        # checking does not use it as a premise.  An exclusive large cone must
        # therefore add no visited gates.  Structural validation is separate:
        # corrupting that same unused cone must still be INVALID.
        game, policy, cert, _sidecar = rank_seed
        baseline_stats_result = run_checker(
            checker, game, policy, "--certificate", str(cert), "--method",
            "certificate", "--stats")
        if baseline_stats_result.returncode != 0:
            raise AssertionError(
                "genuine certificate failed stats probe:\n"
                f"{baseline_stats_result.stdout}{baseline_stats_result.stderr}")
        baseline_stats = checker_stats(baseline_stats_result)
        enlarged = root / "cert-unused-move-cone.aag"
        enlarged.write_text(append_output_chain(
            cert.read_text(encoding="utf-8"), "move_0", 2048),
            encoding="utf-8")
        enlarged_json = pathlib.Path(str(enlarged) + ".json")
        enlarged_json.write_text(
            pathlib.Path(str(cert) + ".json").read_text(encoding="utf-8"),
            encoding="utf-8")
        enlarged_result = run_checker(
            checker, game, policy, "--certificate", str(enlarged),
            "--method", "certificate", "--stats")
        if enlarged_result.returncode != 0:
            raise AssertionError(
                "unused move cone changed certificate verdict:\n"
                f"{enlarged_result.stdout}{enlarged_result.stderr}")
        if checker_stats(enlarged_result) != baseline_stats:
            raise AssertionError(
                "unused move cone was evaluated: "
                f"baseline={baseline_stats} enlarged="
                f"{checker_stats(enlarged_result)}")
        malformed = root / "cert-malformed-unused-move-cone.aag"
        malformed.write_text(append_output_chain(
            cert.read_text(encoding="utf-8"), "move_0", 8,
            malformed=True), encoding="utf-8")
        pathlib.Path(str(malformed) + ".json").write_text(
            enlarged_json.read_text(encoding="utf-8"), encoding="utf-8")
        malformed_result = run_checker(
            checker, game, policy, "--certificate", str(malformed),
            "--method", "certificate")
        if malformed_result.returncode != 4:
            raise AssertionError(
                "malformed unused move cone was not INVALID:\n"
                f"{malformed_result.stdout}{malformed_result.stderr}")

        game, policy, cert, sidecar = rank_seed
        cert_text = cert.read_text(encoding="utf-8")
        certificate_mutations = [
            ("drop-inv", replace_output(cert_text, "inv", replacement=0),
             game, policy, cert),
        ]
        literals = output_literals(cert_text)
        rank_goal, rank_level = next(
            (goal, level)
            for goal, count in enumerate(sidecar["counts"]["levels_per_goal"])
            for level in range(count - 1)
            if literals[f"y_{goal}_{level}"]
            != literals[f"y_{goal}_{level + 1}"])
        swapped_rank = swap_outputs(
            cert_text, f"y_{rank_goal}_{rank_level}",
            f"y_{rank_goal}_{rank_level + 1}")
        for fair in range(sidecar["counts"]["fairness_assumptions"]):
            swapped_rank = swap_outputs(
                swapped_rank, f"x_{rank_goal}_{rank_level}_{fair}",
                f"x_{rank_goal}_{rank_level + 1}_{fair}")
        certificate_mutations.append(
            ("swap-ranks", swapped_rank, game, policy, cert))

        zero_goal, zero_level = next(
            (goal, level)
            for goal, count in enumerate(sidecar["counts"]["levels_per_goal"])
            for level in range(count)
            if literals[f"y_{goal}_{level}"] != 0)
        zero_rank = cert_text
        fairness_count = max(
            1, sidecar["counts"]["fairness_assumptions"])
        for fair in range(fairness_count):
            zero_rank = replace_output(
                zero_rank, f"x_{zero_goal}_{zero_level}_{fair}",
                replacement=0)
        certificate_mutations.append(
            ("zero-rank", zero_rank, game, policy, cert))

        inv_game, inv_policy, inv_cert, _inv_sidecar = inv_seed
        inv_true = replace_output(
            inv_cert.read_text(encoding="utf-8"), "inv", replacement=1)
        certificate_mutations.append(
            ("inv-true", inv_true, inv_game, inv_policy, inv_cert))

        fair_game, fair_policy, fair_cert, fair_sidecar = fairness_seed
        fair_text = fair_cert.read_text(encoding="utf-8")
        fair_literals = output_literals(fair_text)
        fair_goal, fair_level = next(
            (goal, level)
            for goal, count in enumerate(
                fair_sidecar["counts"]["levels_per_goal"])
            for level in range(count)
            if fair_literals[f"x_{goal}_{level}_0"]
            != fair_literals[f"x_{goal}_{level}_1"])
        fairness_mutation = swap_outputs(
            fair_text, f"x_{fair_goal}_{fair_level}_0",
            f"x_{fair_goal}_{fair_level}_1")
        certificate_mutations.append((
            "swap-fairness", fairness_mutation, fair_game, fair_policy,
            fair_cert))
        json_checked = 0
        for label, text, mutation_game, mutation_policy, mutation_cert in (
                certificate_mutations):
            mutated = root / f"cert-{label}.aag"
            mutated.write_text(text, encoding="utf-8")
            mutated_json = root / f"cert-{label}.aag.json"
            mutated_json.write_text(
                pathlib.Path(str(mutation_cert) + ".json").read_text(
                    encoding="utf-8"),
                encoding="utf-8")
            cert_only = run_checker(
                checker, mutation_game, mutation_policy, "--certificate",
                str(mutated), "--certificate-json", str(mutated_json),
                "--method", "certificate")
            if cert_only.returncode != 6:
                raise AssertionError(
                    f"{label} did not report CERT_FAILED:\n"
                    f"{cert_only.stdout}{cert_only.stderr}")
            rebuilt = run_checker(
                checker, mutation_game, mutation_policy, "--certificate",
                str(mutated), "--certificate-json", str(mutated_json),
                "--method", "certificate", "--test-rebuild-successor")
            if cert_only.returncode != rebuilt.returncode:
                raise AssertionError(
                    f"successor-cache {label} status mismatch:\n"
                    f"{cert_only.stdout}{rebuilt.stdout}")
            successor_rebuild_agreements += 1
            cert_oracle = run_checker(
                checker, mutation_game, mutation_policy, "--certificate",
                str(mutated), "--certificate-json", str(mutated_json),
                "--method", "certificate", "--test-unspecialized-policy")
            if cert_oracle.returncode != cert_only.returncode:
                raise AssertionError(
                    f"{label} specialized/oracle status mismatch:\n"
                    f"{cert_only.stdout}{cert_oracle.stdout}")
            closed = run_checker(
                checker, mutation_game, mutation_policy,
                "--method", "closed-loop")
            if closed.returncode != 0:
                raise AssertionError(
                    f"certificate-only {label} changed the policy verdict:\n"
                    f"{closed.stdout}{closed.stderr}")
            for method in ("both", "auto"):
                extra = []
                if not json_checked and label == "zero-rank" and method == "both":
                    json_path = root / "check-result.json"
                    extra = ["--json-out", str(json_path)]
                combined = run_checker(
                    checker, mutation_game, mutation_policy, "--certificate",
                    str(mutated), "--certificate-json", str(mutated_json),
                    "--method", method, *extra)
                if combined.returncode != 0:
                    raise AssertionError(
                        f"certificate-only {label} was not VERIFIED by "
                        f"{method}:\n{combined.stdout}{combined.stderr}")
                if "METHOD certificate CERT_FAILED" not in combined.stdout:
                    raise AssertionError(
                        f"{method} hid certificate failure for {label}:\n"
                        f"{combined.stdout}")
                if extra:
                    payload = json.loads(json_path.read_text(encoding="utf-8"))
                    if (payload.get("format") != "tlsf-gr1-checkresult-v1"
                            or payload.get("verdict") != "VERIFIED"
                            or payload["methods"]["certificate"]["verdict"]
                            != "CERT_FAILED"
                            or payload["methods"]["closed_loop"]["verdict"]
                            != "VERIFIED"
                            or not isinstance(payload.get("peak_bdd_nodes"), int)
                            or payload.get("counterexample_method")
                            != "certificate"
                            or not payload.get("counterexample")
                            or not payload["methods"]["certificate"].get(
                                "counterexample")):
                        raise AssertionError(
                            f"invalid structured JSON result: {payload}")
                    assignment = payload["methods"]["certificate"][
                        "counterexample"]
                    for key in ("state", "curr", "uncontrollable_inputs",
                                "control_choice"):
                        if key not in assignment:
                            raise AssertionError(
                                f"JSON counterexample lacks {key}: {payload}")
                    json_checked = 1

        policy_text = policy.read_text(encoding="utf-8")
        broken_counter = root / "policy-broken-counter.aag"
        broken_counter.write_text(
            replace_output(policy_text, "curr_next_0", invert=True),
            encoding="utf-8")
        (root / "policy-broken-counter.aag.json").write_text(
            pathlib.Path(str(policy) + ".json").read_text(encoding="utf-8"),
            encoding="utf-8")
        broken_wins = policy_wins_explicit(
            game.read_text(encoding="utf-8"),
            broken_counter.read_text(encoding="utf-8"))
        result = run_checker(
            checker, game, broken_counter, "--certificate", str(cert),
            "--method", "both")
        if result.returncode != (0 if broken_wins else 1):
            raise AssertionError(
                "counter mutation disagreed with explicit oracle:\n"
                f"{result.stdout}{result.stderr}")
        counter_specialized = run_checker(
            checker, game, broken_counter, "--certificate", str(cert),
            "--method", "certificate")
        counter_oracle = run_checker(
            checker, game, broken_counter, "--certificate", str(cert),
            "--method", "certificate", "--test-unspecialized-policy")
        if counter_specialized.returncode != counter_oracle.returncode:
            raise AssertionError(
                "counter-update specialized/oracle status mismatch:\n"
                f"{counter_specialized.stdout}{counter_oracle.stdout}")
        counter_rebuilt = run_checker(
            checker, game, broken_counter, "--certificate", str(cert),
            "--method", "certificate", "--test-rebuild-successor")
        if counter_specialized.returncode != counter_rebuilt.returncode:
            raise AssertionError(
                "successor-cache counter-update status mismatch:\n"
                f"{counter_specialized.stdout}{counter_rebuilt.stdout}")
        successor_rebuild_agreements += 1

        # A certificate from a different state dimension must fail before any
        # proof check, even if output names happen to overlap.
        builder = differential.AagBuilder(
            ["u0", "controllable_c0"], [0, 0, 0])
        wrong_game_text = builder.finish(
            [1, builder.latches[0], builder.latches[1]], None,
            False, [builder.latches[2]], [])
        wrong_game = root / "wrong-size-game.aag"
        wrong_policy = root / "wrong-size-policy.aag"
        wrong_cert = root / "wrong-size-cert.aag"
        wrong_json = root / "wrong-size-cert.aag.json"
        wrong_game.write_text(wrong_game_text, encoding="utf-8")
        wrong_solve = subprocess.run(
            [str(solver), "--policy", str(wrong_policy), "--certificate",
             str(wrong_cert), "--certificate-json", str(wrong_json),
             str(wrong_game)], text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=False, timeout=20)
        if wrong_solve.returncode != 0:
            raise AssertionError("solver failed on wrong-size fixture")
        mismatch = run_checker(
            checker, game, policy, "--certificate", str(wrong_cert),
            "--certificate-json", str(wrong_json), "--method", "certificate")
        if mismatch.returncode != 4:
            raise AssertionError(
                f"mis-sized certificate was not INVALID:\n"
                f"{mismatch.stdout}{mismatch.stderr}")

        policy_lines = policy.read_text(encoding="utf-8").splitlines()
        for line_index, line in enumerate(policy_lines):
            if line.startswith("i0 "):
                policy_lines[line_index] = "i0 __wrong_policy_input"
                break
        bad_interface = root / "policy-bad-interface.aag"
        bad_interface.write_text("\n".join(policy_lines) + "\n",
                                 encoding="utf-8")
        (root / "policy-bad-interface.aag.json").write_text(
            pathlib.Path(str(policy) + ".json").read_text(encoding="utf-8"),
            encoding="utf-8")
        interface_result = run_checker(
            checker, game, bad_interface, "--method", "closed-loop")
        if interface_result.returncode != 4:
            raise AssertionError(
                "policy interface mismatch was not INVALID:\n"
                f"{interface_result.stdout}{interface_result.stderr}")

    return {
        "games": generated,
        "realizable": realizable,
        "genuine_both_verified": genuine,
        "sampled_acceptance_verified": sampled_acceptance_verified,
        "policy_mutations": policy_mutations,
        "winning_policy_mutations": winning_mutations,
        "losing_policy_mutations": losing_mutations,
        "explicit_agreements": agreements,
        "certificate_mutations_cert_failed": len(certificate_mutations),
        "counter_mutations_cross_checked": 1,
        "rare_state_mutations_rejected": rare_state_rejected,
        "mis_sized_certificates_invalid": 1,
        "policy_interfaces_invalid": 1,
        "default_certificate_sidecar": 1,
        "default_output_unchanged": default_output_unchanged,
        "unused_move_cones_skipped": 1,
        "malformed_unused_cones_invalid": 1,
        "specialized_policy_oracle_agreements": 8,
        "large_selector_constant_modes": 1,
        "successor_rebuild_oracle_agreements": successor_rebuild_agreements,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--checker", type=pathlib.Path, required=True)
    parser.add_argument("--games", type=int, default=80)
    parser.add_argument("--seed", type=int, default=0xC3A7C4E)
    args = parser.parse_args()
    summary = run_suite(args.solver.resolve(), args.checker.resolve(),
                        args.games, args.seed)
    print(" ".join(f"{key}={value}" for key, value in summary.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
