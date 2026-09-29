#!/usr/bin/env python3
"""U0 environment-certificate AAG-level replay and discrimination (plan
§8.1/§8.2 U0).

Both parametric generators below write ASCII AIGER games directly (via
test_gr1_differential.AagBuilder): "n" is a Python argument, not a reduced
TLSF parameter. Typed-provenance alignment across declared TLSF parameters
is test_gr1_environment_provenance.py's job; the alpha-renaming test here
renames AAG signals only.

test_gr1_unreal_certificate.py already differential-tests environment
witnesses on a random game generator (rank mutations, an oracle-guided
losing-policy search, strict-semantics export refusal, the system_winning
cone). This file adds:

  * deadline_family(n, k): a resource/cooldown family. For the fixed
    cooldown DEADLINE_COOLDOWN it is UNREAL at small n and REAL from a
    threshold on, checked against the explicit-state oracle in
    test_gr1_differential.py: the polarity reversal of plan §8.3.
  * forbidden_family(n): n lanes, each demanding (justice) a state that
    safety forbids, with one shared fairness assumption. UNREAL for every n.
  * Replay of every UNREAL valuation through --method certificate,
    closed-loop and both. The in-process C API replay is
    test/api/gr1_environment_replay.c.
  * Mutations, each pinned to the checker's exact exit status and either its
    COUNTEREXAMPLE reason or its complete INVALID diagnostic:
    a dropped/altered fairness assumption (fair_<i>), a corrupted justice
    goal (goal_<j>), a corrupted memory update (curr_next_<i>), a corrupted
    rank (z_0), a policy output that reads a smuggled controllable-named
    input (Mealy dependence), the wrong method, the wrong side, a duplicate
    JSON key, a truncated certificate, and a same-shape game with different
    safety semantics.
  * A hand-written zero-fairness witness, verified by all three methods,
    whose one-line symbol deletions pin the "unnamed game input" and
    "unnamed output" diagnostics that replaced two null-pointer crashes.
  * Alpha-renaming with crossed ownership-looking names: replay and a
    mutation behave identically, because the checker reads ownership from
    the controllable_ prefix and its own generated field names only.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import test_gr1_certcheck as checker_test  # noqa: E402
import test_gr1_differential as differential  # noqa: E402

DEADLINE_COOLDOWN = 5


# ---------------------------------------------------------------------------
# Generator 1: deadline vs. cooldown.
# ---------------------------------------------------------------------------

def deadline_family(n: int, k: int = DEADLINE_COOLDOWN, *,
                    request_name: str = "u_req",
                    grant_name: str = "controllable_grant") -> str:
    """A pending request must be granted within ~n steps of arriving; a
    grant is itself illegal within k steps of the previous one. UNREAL when
    the deadline is tighter than the cooldown, REAL once it is not."""
    names = [request_name, grant_name]
    nlatch = 1 + n + k
    builder = differential.AagBuilder(names, [0] * nlatch)
    u_req, grant = builder.inputs
    busy = builder.latches[0]
    age = builder.latches[1:1 + n]
    cool = builder.latches[1 + n:1 + n + k]
    not_grant = builder.negate(grant)
    next_busy = builder.land(builder.lor(busy, u_req), not_grant)
    next_ages = []
    previous = busy
    for slot in age:
        next_ages.append(builder.land(previous, not_grant))
        previous = slot
    next_cools = [grant] + list(cool[:-1])
    next_lits = [next_busy, *next_ages, *next_cools]
    in_cooldown = 0
    for slot in cool:
        in_cooldown = builder.lor(in_cooldown, slot)
    deadline_missed = builder.land(age[-1], builder.land(busy, not_grant))
    illegal_grant = builder.land(in_cooldown, grant)
    bad = builder.lor(deadline_missed, illegal_grant)
    justice = [grant]
    fairness = [builder.negate(u_req)]
    return builder.finish(next_lits, bad, True, justice, fairness)


# ---------------------------------------------------------------------------
# Generator 2: forbidden recurrence.
# ---------------------------------------------------------------------------

def forbidden_family(n: int, *, request_prefix: str = "u",
                     grant_prefix: str = "controllable_c",
                     conjunctive_bad: bool = False) -> str:
    """n independent lanes, each demanding (justice) a state that safety
    unconditionally forbids. UNREAL for every n >= 1 by construction."""
    names = [f"{request_prefix}{i}" for i in range(n)]
    names += [f"{grant_prefix}{i}" for i in range(n)]
    builder = differential.AagBuilder(names, [0] * n)
    triggers = builder.inputs[:n]
    grants = builder.inputs[n:]
    lanes = builder.latches
    next_lits = list(grants)
    justice = list(lanes)
    bad = 1 if conjunctive_bad else 0
    combine = builder.land if conjunctive_bad else builder.lor
    for lane in lanes:
        bad = combine(bad, lane)
    trigger = 0
    for signal in triggers:
        trigger = builder.lor(trigger, signal)
    fairness = [trigger]
    return builder.finish(next_lits, bad, True, justice, fairness)


# ---------------------------------------------------------------------------
# Shared plumbing.
# ---------------------------------------------------------------------------

def run(command: list, expected=(0,), timeout: int = 20):
    result = subprocess.run([str(c) for c in command], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            check=False, timeout=timeout)
    if result.returncode not in expected:
        raise AssertionError(
            f"command returned {result.returncode} (expected one of "
            f"{expected}): {' '.join(str(c) for c in command)}\n"
            f"{result.stdout}{result.stderr}")
    return result


def explicit_real(text: str) -> bool:
    parsed = differential.parse_aag(text)
    game = differential.ExplicitGame(parsed)
    return game.aag.initial_state() in game.solve()


def solve_export(solver: pathlib.Path, root: pathlib.Path, tag: str,
                 text: str):
    game = root / f"{tag}.aag"
    policy = root / f"{tag}-policy.aag"
    certificate = root / f"{tag}-cert.aag"
    game.write_text(text, encoding="utf-8")
    result = run([solver, "--semantics", "exact", "--policy", policy,
                 "--certificate", certificate, game], (0, 1))
    return game, policy, certificate, result


def sidecar(artifact: pathlib.Path) -> dict:
    return json.loads(pathlib.Path(str(artifact) + ".json").read_text())


def check(checker_path: pathlib.Path, game: pathlib.Path,
         policy: pathlib.Path, certificate: pathlib.Path, method: str,
         *extra: str, expected=(0,)):
    return run([checker_path, "--certificate", certificate, "--method",
               method, *extra, game, policy], expected)


def replay_verified(checker_path, game, policy, certificate):
    """Both independent verification routes must agree the witness holds."""
    check(checker_path, game, policy, certificate, "certificate")
    check(checker_path, game, policy, certificate, "closed-loop")
    check(checker_path, game, policy, certificate, "both")


def assert_certificate_cert_failed(checker_path, game, policy, certificate,
                                   reason=None):
    """A certificate or policy mutation must be rejected by the environment
    `certificate` method, which recompiles and checks the policy as well.
    `--method both` is not used: its closed-loop route never reads the
    certificate's fair_/goal_/rank outputs and would still verify against
    the unmodified policy.

    `reason`, when given, is the exact `COUNTEREXAMPLE reason=...` that
    print_counterexample must print, pinning which obligation failed. It
    prints it only when !use_input_first(ck), which holds for these small
    policies (use_input_first in gr1_check.c)."""
    result = check(checker_path, game, policy, certificate, "certificate",
                   expected=(6,))
    if "METHOD certificate CERT_FAILED" not in result.stdout:
        raise AssertionError(
            "expected 'METHOD certificate CERT_FAILED' on stdout, got:\n"
            f"{result.stdout}")
    if reason is not None and f"COUNTEREXAMPLE reason={reason}" not in result.stdout:
        raise AssertionError(
            f"expected 'COUNTEREXAMPLE reason={reason}' on stdout, got:\n"
            f"{result.stdout}")
    return result


def assert_invalid_with_message(checker_path, game, policy, certificate,
                                message, method="certificate", *extra):
    """An interface or parse rejection, before any proof work: exit 4,
    stdout exactly INVALID, and stderr exactly the checker's one-line
    diagnostic `tlsfcertcheck: <message>` (gr1_check_run in gr1_check.c).
    `message` may be a tuple of acceptable complete diagnostics, used only
    where a byte-level cut lands in a fixture-dependent section (see the
    truncation mutation)."""
    result = run([checker_path, "--certificate", certificate, "--method",
                 method, *extra, game, policy], (4,))
    candidates = message if isinstance(message, tuple) else (message,)
    if (result.stdout != "INVALID\n" or result.stderr not in
            [f"tlsfcertcheck: {candidate}\n" for candidate in candidates]):
        raise AssertionError(
            f"expected INVALID with stderr one of {candidates!r}, got "
            f"stdout {result.stdout!r} and stderr {result.stderr!r}")
    return result


def mutate_certificate(root, tag, certificate, name, **kwargs):
    text = certificate.read_text(encoding="utf-8")
    mutated_text = checker_test.replace_output(text, name, **kwargs)
    mutated = root / f"{tag}-mutated-{name}.aag"
    mutated.write_text(mutated_text, encoding="utf-8")
    (root / f"{tag}-mutated-{name}.aag.json").write_text(
        pathlib.Path(str(certificate) + ".json").read_text(encoding="utf-8"),
        encoding="utf-8")
    return mutated


def mutate_policy(root, tag, policy, name, **kwargs):
    text = policy.read_text(encoding="utf-8")
    mutated_text = checker_test.replace_output(text, name, **kwargs)
    mutated = root / f"{tag}-mutated-policy-{name}.aag"
    mutated.write_text(mutated_text, encoding="utf-8")
    (root / f"{tag}-mutated-policy-{name}.aag.json").write_text(
        pathlib.Path(str(policy) + ".json").read_text(encoding="utf-8"),
        encoding="utf-8")
    return mutated


# ---------------------------------------------------------------------------
# Suite pieces.
# ---------------------------------------------------------------------------

def replay_unreal_instance(solver, checker_path, root, tag, text):
    """Solve, export, and replay a single UNREAL valuation; return the
    exported (game, policy, certificate) triple for further mutation."""
    if explicit_real(text):
        raise AssertionError(f"{tag}: independent oracle says REAL, "
                             "generator design error")
    game, policy, certificate, solved = solve_export(solver, root, tag, text)
    if solved.returncode != 1:
        raise AssertionError(
            f"{tag}: solver disagreed with the independent oracle "
            f"(rc={solved.returncode}):\n{solved.stderr}")
    cert_sidecar = sidecar(certificate)
    policy_sidecar = sidecar(policy)
    if cert_sidecar["side"] != "environment":
        raise AssertionError(f"{tag}: certificate side is not environment")
    if policy_sidecar["side"] != "environment":
        raise AssertionError(f"{tag}: policy side is not environment")
    if cert_sidecar["reduction_semantics"] != "exact":
        raise AssertionError(f"{tag}: certificate is not exact")
    if not cert_sidecar["environment_counter_strategy_exported"]:
        raise AssertionError(f"{tag}: certificate did not export a witness")
    replay_verified(checker_path, game, policy, certificate)
    return game, policy, certificate


def replay_real_instance(solver, root, tag, text):
    if not explicit_real(text):
        raise AssertionError(f"{tag}: independent oracle says UNREAL, "
                             "generator design error")
    game, policy, certificate, solved = solve_export(solver, root, tag, text)
    if solved.returncode != 0:
        raise AssertionError(
            f"{tag}: solver disagreed with the independent oracle "
            f"(rc={solved.returncode}):\n{solved.stderr}")
    if sidecar(certificate)["side"] != "system":
        raise AssertionError(f"{tag}: certificate side is not system")


def run_generator1(solver, checker_path, root, summary):
    """Several small UNREAL valuations, plus the REAL flip at the same fixed
    cooldown (plan §8.3's polarity reversal)."""
    unreal_valuations = (1, 2, 3)
    real_valuations = (4, 6)
    fixtures = {}
    for n in unreal_valuations:
        tag = f"deadline-u{n}"
        text = deadline_family(n)
        fixtures[n] = replay_unreal_instance(solver, checker_path, root, tag,
                                             text)
        summary["deadline_unreal_valuations"] += 1
    for n in real_valuations:
        tag = f"deadline-r{n}"
        replay_real_instance(solver, root, tag, deadline_family(n))
        summary["deadline_real_valuations"] += 1
    summary["polarity_reversal_family"] = "deadline_family"
    return fixtures


def run_generator2(solver, checker_path, root, summary):
    fixtures = {}
    for n in (1, 2, 3):
        tag = f"forbidden-{n}"
        text = forbidden_family(n)
        fixtures[n] = replay_unreal_instance(solver, checker_path, root, tag,
                                             text)
        summary["forbidden_unreal_valuations"] += 1
    return fixtures


def run_discrimination(checker_path, root, tag, game, policy, certificate,
                       summary):
    cert_text = certificate.read_text(encoding="utf-8")
    cert_outputs = checker_test.output_literals(cert_text)
    policy_text = policy.read_text(encoding="utf-8")
    policy_outputs = checker_test.output_literals(policy_text)

    # 1. Dropped/altered fairness assumption. certificate method only: the
    # closed-loop route inside --method both never reads fair_* at all, so
    # it would still verify against the unmodified policy and mask this.
    fair_names = [name for name in cert_outputs if name.startswith("fair_")]
    if not fair_names:
        raise AssertionError(f"{tag}: certificate has no fair_* output")
    mutated = mutate_certificate(root, tag, certificate, fair_names[0],
                                 invert=True)
    assert_certificate_cert_failed(
        checker_path, game, policy, mutated,
        reason="certificate fairness differs from game fairness")
    summary["assumption_mutations_rejected"] += 1

    # 2. Corrupted justice index. Same reasoning, same method.
    goal_names = [name for name in cert_outputs if name.startswith("goal_")]
    if not goal_names:
        raise AssertionError(f"{tag}: certificate has no goal_* output")
    mutated = mutate_certificate(root, tag, certificate, goal_names[0],
                                 invert=True)
    assert_certificate_cert_failed(
        checker_path, game, policy, mutated,
        reason="certificate goal differs from game justice")
    summary["justice_index_mutations_rejected"] += 1

    # 3. Corrupted memory update (curr_next_*): the existing suite's
    # losing-policy search skips curr_next_* candidates.
    counter_names = [name for name in policy_outputs
                     if name.startswith("curr_next_")]
    if not counter_names:
        raise AssertionError(f"{tag}: policy has no curr_next_* output")
    mutated_policy = mutate_policy(root, tag, policy, counter_names[0],
                                   invert=True)
    # check_environment_certificate_mode accumulates the counter-update
    # mismatch and the one-step rank obligation into one violation and
    # reports both under one reason; there is no counter-specific message.
    assert_certificate_cert_failed(
        checker_path, game, mutated_policy, certificate,
        reason="dual one-step certificate obligation")
    summary["memory_update_mutations_rejected"] += 1

    # 4. Corrupted rank: invert z_0. The outer monotonicity check starts at
    # k=1, so the first relation of
    # validate_environment_certificate_predicates that z_0 enters is "Z is
    # the union of its Y regions", which the inversion breaks while every
    # y_0_j is unchanged.
    if "z_0" not in cert_outputs:
        raise AssertionError(f"{tag}: certificate has no z_0 output")
    mutated = mutate_certificate(root, tag, certificate, "z_0", invert=True)
    assert_certificate_cert_failed(
        checker_path, game, policy, mutated,
        reason="dual Z is not the union of its Y regions")
    summary["rank_mutations_rejected"] += 1

    # 5. Mealy dependence: an environment output whose cone reads a smuggled
    # input named like the game's controllable, not merely a dangling one.
    # The extra input breaks the policy arity (nstate + ncounter inputs), and
    # validate_policy_interface checks arity before names, so the exact
    # diagnostic is the arity one; reaching it also shows that aig_read_aag
    # and validate_aig_structure accepted the mutated circuit.
    controllable = next(name for name in differential.parse_aag(
        game.read_text(encoding="utf-8")).input_names
        if name.startswith("controllable_"))
    uncontrollable_output = next(
        name for name in policy_outputs
        if not name.startswith("curr_next_"))
    smuggled = add_controllable_dependent_input(
        policy_text, controllable, uncontrollable_output)
    smuggled_path = root / f"{tag}-mealy-dependent-policy.aag"
    smuggled_path.write_text(smuggled, encoding="utf-8")
    (root / f"{tag}-mealy-dependent-policy.aag.json").write_text(
        pathlib.Path(str(policy) + ".json").read_text(encoding="utf-8"),
        encoding="utf-8")
    header = [int(item) for item in policy_text.splitlines()[0].split()[1:]]
    inputs, outputs = header[1], header[3]
    assert_invalid_with_message(
        checker_path, game, smuggled_path, certificate,
        f"policy arity mismatch (inputs {inputs + 1}/{inputs}, "
        f"outputs {outputs}/{outputs})")
    summary["mealy_dependence_mutations_rejected"] += 1

    # 6. Wrong method: region-v1 is system-only and policy-free
    # (validate_region_sidecar).
    wrong_method = run([checker_path, "--method", "region", "--certificate",
                       certificate, game], (4,))
    region_message = ("tlsfcertcheck: region-v1 requires a realizable system "
                      "certificate matching this game\n")
    if wrong_method.stdout != "INVALID\n" or wrong_method.stderr != region_message:
        raise AssertionError(
            f"expected INVALID with stderr {region_message!r}, got stdout "
            f"{wrong_method.stdout!r} and stderr {wrong_method.stderr!r}")
    summary["wrong_method_rejections"] += 1

    # 7. Wrong side: the certificate sidecar claims the system side while
    # the policy sidecar, which decides the side, says environment.
    # 8. Duplicate decoded JSON key, repeating the same valid "format"
    # value, so a first- or last-wins parser would accept the document; only
    # json_unique rejects it.
    # validate_sidecars reports both with the same message: a null parse
    # root and a mismatched field share one diagnostic. Pinning it still
    # excludes every other INVALID cause, but not each other.
    sidecar_message = "certificate sidecar does not match this game"
    cert_json_path = pathlib.Path(str(certificate) + ".json")
    original_json = cert_json_path.read_text(encoding="utf-8")
    if '"side":"environment"' not in original_json:
        raise AssertionError(f"{tag}: unexpected certificate JSON formatting")
    wrong_side_json = original_json.replace(
        '"side":"environment"', '"side":"system"', 1)
    wrong_side_path = root / f"{tag}-wrong-side.aag.json"
    wrong_side_path.write_text(wrong_side_json, encoding="utf-8")
    wrong_side_cert = root / f"{tag}-wrong-side.aag"
    wrong_side_cert.write_text(cert_text, encoding="utf-8")
    assert_invalid_with_message(checker_path, game, policy, wrong_side_cert,
                                sidecar_message)
    summary["wrong_side_rejections"] += 1

    if '"format":"tlsf-gr1-certificate-v1"' not in original_json:
        raise AssertionError(f"{tag}: unexpected certificate JSON formatting")
    duplicated = original_json.replace(
        "{", '{"format":"tlsf-gr1-certificate-v1",', 1)
    duplicate_path = root / f"{tag}-duplicate-key.aag"
    duplicate_path.write_text(cert_text, encoding="utf-8")
    pathlib.Path(str(duplicate_path) + ".json").write_text(
        duplicated, encoding="utf-8")
    assert_invalid_with_message(checker_path, game, policy, duplicate_path,
                                sidecar_message)
    summary["duplicate_key_rejections"] += 1

    # 9. Truncated certificate, cut to half its length. Depending on the
    # fixture's size the cut lands in the gate section, which aig_read_aag
    # rejects, or in the symbol table, which it accepts with an output left
    # unnamed. Both complete diagnostics are pinned; the unnamed case also
    # has the deterministic regression in run_hand_written_witness.
    truncated_path = root / f"{tag}-truncated.aag"
    truncated_path.write_text(cert_text[:len(cert_text) // 2],
                              encoding="utf-8")
    pathlib.Path(str(truncated_path) + ".json").write_text(
        cert_json_path.read_text(encoding="utf-8"), encoding="utf-8")
    assert_invalid_with_message(
        checker_path, game, policy, truncated_path,
        (f"malformed ASCII AIGER '{truncated_path}'", "unnamed output"))
    summary["truncated_artifact_rejections"] += 1


# A hand-written UNREAL game with state-based acceptance and no fairness
# assumption: justice asks for `granted` infinitely often, and `granted` is
# bad. It has two inputs, so validate_game_names compares names pairwise.
ZERO_FAIRNESS_GAME = """aag 3 2 1 0 0 1 0 1 0
2
4
6 4 0
6
1
6
i0 request
i1 controllable_grant
l0 granted
"""

# The environment's policy: never request (any choice wins), and the single
# fairness counter (the synthetic always-true disjunct) always advances to
# itself.
ZERO_FAIRNESS_POLICY = """aag 2 2 0 2 0
2
4
0
1
i0 granted
i1 curr_0
o0 request
o1 curr_next_0
"""

ZERO_FAIRNESS_POLICY_JSON = {
    "format": "tlsf-gr1-policy-v1", "side": "environment",
    "reduction_semantics": "exact", "system_strategy_semantics": "mealy",
    "strategy_semantics": "moore", "duality_delay_steps": 1,
    "counts": {"game_state_variables": 1, "goals": 1,
               "fairness_counters": 1}}

# The dual certificate: outer level 0 is `granted` (already bad), level 1 is
# every state. From a state outside level 0, any response either keeps
# goal_0 false or enters level 0, so each rank obligation holds; y and z
# are the matching unions and intersections, and inv is the last z.
ZERO_FAIRNESS_CERTIFICATE = """aag 3 3 0 10 0
2
4
6
1
0
2
1
2
1
2
1
2
1
i0 granted
i1 request
i2 controllable_grant
o0 inv
o1 system_winning
o2 goal_0
o3 move_0
o4 z_0
o5 z_1
o6 y_0_0
o7 y_1_0
o8 x_0_0_0_0
o9 x_1_0_0_0
"""

ZERO_FAIRNESS_CERTIFICATE_JSON = {
    "format": "tlsf-gr1-certificate-v1", "status": "unrealizable",
    "side": "environment", "reduction_semantics": "exact",
    "system_strategy_semantics": "mealy", "strategy_semantics": "moore",
    "duality_delay_steps": 1, "environment_counter_strategy_exported": True,
    "counts": {"state_variables": 1, "goals": 1, "fairness_assumptions": 0}}


def without_line(text: str, line: str) -> str:
    lines = text.splitlines()
    if lines.count(line) != 1:
        raise AssertionError(f"fixture has no unique line {line!r}")
    lines.remove(line)
    return "\n".join(lines) + "\n"


def run_hand_written_witness(checker_path, root, summary):
    """The hand-written witness must verify under every environment method,
    so each regression below differs from a verified input by one deleted
    symbol line, and the diagnostic is the one that deletion causes."""
    if explicit_real(ZERO_FAIRNESS_GAME):
        raise AssertionError("hand-written game is REAL per the oracle")
    game = root / "hand-game.aag"
    policy = root / "hand-policy.aag"
    certificate = root / "hand-cert.aag"
    for path, text, sidecar_json in (
            (game, ZERO_FAIRNESS_GAME, None),
            (policy, ZERO_FAIRNESS_POLICY, ZERO_FAIRNESS_POLICY_JSON),
            (certificate, ZERO_FAIRNESS_CERTIFICATE,
             ZERO_FAIRNESS_CERTIFICATE_JSON)):
        path.write_text(text, encoding="utf-8")
        if sidecar_json is not None:
            pathlib.Path(str(path) + ".json").write_text(
                json.dumps(sidecar_json), encoding="utf-8")
    for method in ("certificate", "closed-loop", "both"):
        check(checker_path, game, policy, certificate, method)
        summary["hand_written_witness_verified"] += 1

    # validate_game_names used to strcmp a missing game input name.
    for index, line in enumerate(("i0 request", "i1 controllable_grant")):
        mutated = root / f"hand-game-unnamed-{index}.aag"
        mutated.write_text(without_line(ZERO_FAIRNESS_GAME, line),
                           encoding="utf-8")
        assert_invalid_with_message(checker_path, mutated, policy,
                                    certificate, f"unnamed game input {index}")
        summary["unnamed_game_input_regressions"] += 1

    # duplicate_inputs_or_outputs used to strcmp a missing output name. The
    # policy interface is checked before the certificate interface, so the
    # certificate cases reach the certificate check only because the policy
    # is intact. Deleting the first output hits the outer null check;
    # deleting the last one first passes through the inner comparison.
    for label, path, text, sidecar_json, lines in (
            ("policy", policy, ZERO_FAIRNESS_POLICY,
             ZERO_FAIRNESS_POLICY_JSON, ("o0 request", "o1 curr_next_0")),
            ("cert", certificate, ZERO_FAIRNESS_CERTIFICATE,
             ZERO_FAIRNESS_CERTIFICATE_JSON, ("o0 inv", "o9 x_1_0_0_0"))):
        for line in lines:
            mutated = root / f"hand-{label}-without-{line.split()[0]}.aag"
            mutated.write_text(without_line(text, line), encoding="utf-8")
            pathlib.Path(str(mutated) + ".json").write_text(
                json.dumps(sidecar_json), encoding="utf-8")
            if label == "policy":
                assert_invalid_with_message(checker_path, game, mutated,
                                            certificate, "unnamed output")
            else:
                assert_invalid_with_message(checker_path, game, policy,
                                            mutated, "unnamed output")
            summary["unnamed_output_regressions"] += 1


def add_controllable_dependent_input(text: str, name: str,
                                     output_name: str) -> str:
    """Insert an extra input named `name` (the game's controllable signal)
    and XOR it into `output_name`'s cone, so the output really depends on
    it. Section boundaries come from the header counts, as in
    test_gr1_certcheck.py's _sections(), so this works on exported AAG
    text."""
    lines = text.splitlines()
    header = [int(item) for item in lines[0].split()[1:]]
    header += [0] * (9 - len(header))
    maxvar, ninputs, nlatches, noutputs, nands, nbad, nconstraints, \
        njustice, nfairness = header[:9]
    new_input_lit = 2 * (maxvar + 1)
    lines.insert(1 + ninputs, str(new_input_lit))
    maxvar += 1
    ninputs += 1

    output_start = 1 + ninputs + nlatches
    position = output_start + noutputs + nbad + nconstraints
    justice_sizes = [int(lines[position + i]) for i in range(njustice)]
    position += njustice + sum(justice_sizes) + nfairness
    gate_start = position
    symbol_start = gate_start + nands

    names = {}
    for line in lines[symbol_start:]:
        if line.startswith("o"):
            label, sym_name = line.split(maxsplit=1)
            names[sym_name] = int(label[1:])
    if output_name not in names:
        raise AssertionError(f"policy has no output named '{output_name}'")
    output_index = names[output_name]
    a = int(lines[output_start + output_index])
    b = new_input_lit

    # XOR(a, b) via three AND gates (De Morgan), matching
    # test_gr1_differential.AagBuilder.lxor's construction so a genuine
    # dependence on b (not a spuriously-simplified constant) results.
    gate_lines = []
    v = maxvar
    v += 1
    gate1 = 2 * v
    gate_lines.append(f"{gate1} {a} {b ^ 1}")
    v += 1
    gate2 = 2 * v
    gate_lines.append(f"{gate2} {a ^ 1} {b}")
    v += 1
    gate3 = 2 * v
    gate_lines.append(f"{gate3} {gate1 ^ 1} {gate2 ^ 1}")
    xor_lit = gate3 ^ 1
    maxvar = v

    lines[output_start + output_index] = str(xor_lit)
    for offset, gate_line in enumerate(gate_lines):
        lines.insert(gate_start + nands + offset, gate_line)
    header[0] = maxvar
    header[1] = ninputs
    header[4] = nands + len(gate_lines)
    lines[0] = "aag " + " ".join(str(value) for value in header)
    lines.insert(symbol_start + len(gate_lines), f"i{ninputs - 1} {name}")
    return "\n".join(lines) + "\n"


def run_wrong_game_same_shape(solver, checker_path, root, summary):
    """A game of the same declared shape with different safety semantics
    must reject the original witness. This is the checker-level counterpart
    of the plan's wrong-game mutation: the sidecars carry no hash, so only
    the game's content can bind the witness (docs/gr1-environment-
    certificate.md, gap 5).

    Justice and fairness are unchanged, so the goal and fairness equality
    checks pass. The twin's bad is the conjunction of the lanes instead of
    their disjunction, a strict subset, so some state that the rank
    argument covered only by being bad is now uncovered, and the one-step
    obligation fails when recompiled against the twin's own bad and
    next-state functions."""
    original_text = forbidden_family(2, conjunctive_bad=False)
    twin_text = forbidden_family(2, conjunctive_bad=True)
    original_parsed = differential.parse_aag(original_text)
    twin_parsed = differential.parse_aag(twin_text)
    if (len(original_parsed.inputs), len(original_parsed.latches),
        len(original_parsed.justice), len(original_parsed.fairness)) != (
            len(twin_parsed.inputs), len(twin_parsed.latches),
            len(twin_parsed.justice), len(twin_parsed.fairness)):
        raise AssertionError("wrong-game fixture shapes diverged")
    game, policy, certificate = replay_unreal_instance(
        solver, checker_path, root, "wrong-game-original", original_text)
    twin_game = root / "wrong-game-twin.aag"
    twin_game.write_text(twin_text, encoding="utf-8")
    assert_certificate_cert_failed(
        checker_path, twin_game, policy, certificate,
        reason="dual one-step certificate obligation")
    summary["wrong_game_same_shape_rejections"] += 1


def run_alpha_renaming(solver, checker_path, root, summary):
    """Same family, same n/k, crossed ownership-looking names: an
    uncontrollable input named with output-sounding words, and a
    controllable input (still mandatorily `controllable_`-prefixed) named
    with input-sounding words. Replay and a representative mutation must
    behave identically to the plainly named baseline."""
    baseline_text = deadline_family(1)
    renamed_text = deadline_family(
        1, request_name="grant_watch_by_environment",
        grant_name="controllable_request_sensor_feed")
    if explicit_real(baseline_text) or explicit_real(renamed_text):
        raise AssertionError("alpha-renaming fixtures must stay UNREAL")

    baseline = replay_unreal_instance(solver, checker_path, root,
                                      "alpha-baseline", baseline_text)
    renamed = replay_unreal_instance(solver, checker_path, root,
                                     "alpha-renamed", renamed_text)

    for tag, (game, policy, certificate) in (("alpha-baseline", baseline),
                                             ("alpha-renamed", renamed)):
        policy_text = policy.read_text(encoding="utf-8")
        counter_name = next(name for name in checker_test.output_literals(
            policy_text) if name.startswith("curr_next_"))
        mutated_policy = mutate_policy(root, tag, policy, counter_name,
                                       invert=True)
        assert_certificate_cert_failed(
            checker_path, game, mutated_policy, certificate,
            reason="dual one-step certificate obligation")
        summary["alpha_renaming_mutations_rejected"] += 1
    summary["alpha_renaming_pairs"] += 1


def run_suite(solver: pathlib.Path, checker_path: pathlib.Path) -> dict:
    summary = {
        "deadline_unreal_valuations": 0,
        "deadline_real_valuations": 0,
        "forbidden_unreal_valuations": 0,
        "polarity_reversal_family": "",
        "assumption_mutations_rejected": 0,
        "justice_index_mutations_rejected": 0,
        "memory_update_mutations_rejected": 0,
        "rank_mutations_rejected": 0,
        "mealy_dependence_mutations_rejected": 0,
        "wrong_method_rejections": 0,
        "wrong_side_rejections": 0,
        "duplicate_key_rejections": 0,
        "truncated_artifact_rejections": 0,
        "hand_written_witness_verified": 0,
        "unnamed_game_input_regressions": 0,
        "unnamed_output_regressions": 0,
        "wrong_game_same_shape_rejections": 0,
        "alpha_renaming_pairs": 0,
        "alpha_renaming_mutations_rejected": 0,
    }
    with tempfile.TemporaryDirectory(prefix="tlsf-gr1-env-replay-") as directory:
        root = pathlib.Path(directory)
        deadline_fixtures = run_generator1(solver, checker_path, root, summary)
        forbidden_fixtures = run_generator2(solver, checker_path, root, summary)
        game, policy, certificate = deadline_fixtures[1]
        run_discrimination(checker_path, root, "deadline-u1", game, policy,
                           certificate, summary)
        game, policy, certificate = forbidden_fixtures[2]
        run_discrimination(checker_path, root, "forbidden-2", game, policy,
                           certificate, summary)
        run_hand_written_witness(checker_path, root, summary)
        run_wrong_game_same_shape(solver, checker_path, root, summary)
        run_alpha_renaming(solver, checker_path, root, summary)

    for key, value in summary.items():
        if not value:
            raise AssertionError(f"{key} was never exercised")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--checker", type=pathlib.Path, required=True)
    args = parser.parse_args()
    summary = run_suite(args.solver.resolve(), args.checker.resolve())
    print(" ".join(f"{key}={value}" for key, value in summary.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
