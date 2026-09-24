#!/usr/bin/env python3
"""Direct (non-pytest) tests for per-conjunct GR(1) monitor games."""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import random
import subprocess
import sys
import tempfile


HERE = pathlib.Path(__file__).resolve().parent
TLSF_ROOT = HERE.parent
ACACIA_ROOT = next(
    (candidate for candidate in (
        TLSF_ROOT.parent / "acacia-bonsai",
        TLSF_ROOT.parents[1],
    ) if (candidate / "benchmarking/param-lift-20260922/m0-census.py").is_file()),
    TLSF_ROOT.parents[1],
)
sys.path.insert(0, str(TLSF_ROOT / "scripts"))

import gr1_monitor_game as game  # noqa: E402
import verify_strategy_explicit as explicit  # noqa: E402


def run(command, expected=None, **kwargs):
    proc = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=False, **kwargs)
    if expected is not None and proc.returncode != expected:
        raise AssertionError(
            f"expected exit {expected}, got {proc.returncode}: {' '.join(map(str, command))}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}")
    return proc


def tool_args(args):
    return ["--tlsf2ltl", args.tlsf2ltl, "--tlsf2tlsf", args.tlsf2tlsf,
            "--tlsfinfo", args.tlsfinfo]


def assert_gr1_layout(text, expected_bad=None):
    lines = text.splitlines()
    fields = [int(value) for value in lines[0].split()[1:]]
    fields += [0] * (9 - len(fields))
    _maxvar, ni, nl, no, _na, nb, nc, nj, _nf = fields[:9]
    assert no == 1 and nb == 0 and nc == 0 and nj > 0
    assert "o0 bad" in lines
    if expected_bad is not None:
        assert int(lines[1 + ni + nl]) == expected_bad


def test_split_rule(args, spot):
    census_path = ACACIA_ROOT / "benchmarking/param-lift-20260922/m0-census.py"
    spec = importlib.util.spec_from_file_location("m0_census", census_path)
    census = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(census)
    tlsf = ACACIA_ROOT / "tlsf-corpus/arbiter_pb_2_pe_.tlsf"
    lowered = run([args.tlsf2ltl, "--format", "ltl", str(tlsf)], 0).stdout
    formula = spot.formula(lowered)
    assumptions, guarantees = game.split_objective(formula, spot)
    if formula.kind() == spot.op_Implies:
        reference_a = list(census.conjuncts(formula[0]))
        reference_g = list(census.conjuncts(formula[1]))
    else:
        reference_a = []
        reference_g = list(census.conjuncts(formula))
    assert [str(f) for f in assumptions] == [str(f) for f in reference_a]
    assert [str(f) for f in guarantees] == [str(f) for f in reference_g]

    synthetic = spot.formula("(a & G(b & c)) -> G(d & (e & f))")
    left, right = game.split_objective(synthetic, spot)
    assert [str(f) for f in left] == ["a", "Gb", "Gc"]
    assert [str(f) for f in right] == ["Gd", "Ge", "Gf"]


def eval_boolean(formula, valuation, spot):
    kind = formula.kind()
    if formula.is_tt():
        return True
    if formula.is_ff():
        return False
    if kind == spot.op_ap:
        return valuation[str(formula)]
    if kind == spot.op_Not:
        return not eval_boolean(formula[0], valuation, spot)
    if kind == spot.op_And:
        return all(eval_boolean(child, valuation, spot) for child in formula)
    if kind == spot.op_Or:
        return any(eval_boolean(child, valuation, spot) for child in formula)
    if kind == spot.op_Xor:
        return (eval_boolean(formula[0], valuation, spot)
                != eval_boolean(formula[1], valuation, spot))
    if kind == spot.op_Implies:
        return (not eval_boolean(formula[0], valuation, spot)
                or eval_boolean(formula[1], valuation, spot))
    if kind == spot.op_Equiv:
        return (eval_boolean(formula[0], valuation, spot)
                == eval_boolean(formula[1], valuation, spot))
    raise AssertionError(f"unexpected Boolean kind {formula}")


def automaton_step(monitor, state, valuation, spot):
    matches = []
    for edge in monitor.automaton.out(state):
        condition = spot.formula(spot.bdd_format_formula(
            monitor.automaton.get_dict(), edge.cond))
        if eval_boolean(condition, valuation, spot):
            matches.append(edge.dst)
    assert len(matches) == 1
    return matches[0]


def lasso_accepts_monitor(monitor, prefix, loop, spot):
    state = monitor.automaton.get_init_state_number()
    for valuation in prefix:
        state = automaton_step(monitor, state, valuation, spot)
    seen = {}
    states = []
    position = 0
    while (state, position) not in seen:
        seen[state, position] = len(states)
        states.append(state)
        state = automaton_step(monitor, state, loop[position], spot)
        position = (position + 1) % len(loop)
    cycle = states[seen[state, position]:]
    return any(monitor.accepting[candidate] for candidate in cycle)


def lasso_accepts_encoded(monitor, aag_text, signal_names, prefix, loop):
    circuit = explicit.parse_aag(aag_text)
    state = circuit.initial_state()
    name_to_bit = {name: index for index, name in enumerate(circuit.input_names)}

    def step(current, valuation):
        bits = 0
        for name in signal_names:
            external = game.CONTROLLABLE_PREFIX + name
            bit = name_to_bit.get(name, name_to_bit.get(external))
            assert bit is not None
            if valuation[name]:
                bits |= 1 << bit
        return circuit.simulate(current, bits)[0]

    for valuation in prefix:
        state = step(state, valuation)
    seen = {}
    states = []
    position = 0
    while (state, position) not in seen:
        seen[state, position] = len(states)
        states.append(state)
        state = step(state, loop[position])
        position = (position + 1) % len(loop)
    cycle = states[seen[state, position]:]
    acceptance_mask = sum(
        1 << index for index, accepted in enumerate(monitor.accepting) if accepted)
    return any(candidate & acceptance_mask for candidate in cycle)


def test_monitor_encoding(args, spot):
    rng = random.Random(0x20260922)
    real_instances = [
        ACACIA_ROOT / "tlsf-corpus/arbiter_pb_2_pe_.tlsf",
        ACACIA_ROOT / "tlsf-corpus/arbiter_on_inpchange_pb_2_pe_.tlsf",
    ]
    checked = 0
    parity_fallback_checked = 0
    for tlsf in real_instances:
        lowered = run([args.tlsf2ltl, "--format", "ltl", str(tlsf)], 0).stdout
        formula = spot.formula(lowered)
        assumptions, guarantees = game.split_objective(formula, spot)
        for side, conjunct in ([*(('assumption', f) for f in assumptions),
                                *(('guarantee', f) for f in guarantees)][:8]):
            monitor = game.build_monitor(conjunct, side, spot)
            assert spot.are_equivalent(monitor.automaton, conjunct), conjunct
            preferred = spot.translate(
                conjunct, "BA", "complete", "state-based", "deterministic")
            if not spot.is_deterministic(preferred):
                parity_fallback_checked += 1
            aps = sorted(str(ap) for ap in spot.atomic_prop_collect(conjunct))
            # Treat every AP as uncontrollable here; monitor logic is identical
            # regardless of the game partition.
            aag, _builder, _violated = game.encode_game(
                [monitor], aps, [], "exact", spot)
            assert_gr1_layout(aag, expected_bad=0)
            for _ in range(80):
                prefix = [dict(zip(aps, bits)) for bits in (
                    [rng.choice((False, True)) for _ in aps]
                    for _ in range(rng.randrange(5)))]
                loop = [dict(zip(aps, bits)) for bits in (
                    [rng.choice((False, True)) for _ in aps]
                    for _ in range(rng.randrange(1, 6)))]
                expected = lasso_accepts_monitor(
                    monitor, prefix, loop, spot)
                encoded = lasso_accepts_encoded(
                    monitor, aag, aps, prefix, loop)
                assert encoded == expected, (conjunct, prefix, loop)
            checked += 1
    assert checked >= 6
    assert parity_fallback_checked >= 1


def test_symmetric_signature(spot):
    buses = game._bus_inventory(
        ["g_0", "g_1", "g_2", "r_0", "r_1", "s"])
    mutex = spot.formula("G(!(g_0 & g_1) & !(g_0 & g_2) & !(g_1 & g_2))")
    assert game._symmetric_signature(mutex, buses, spot) == {"g": [0, 1]}

    scalar_dependent = spot.formula("G(s | (!(g_0 & g_1) & !(g_0 & g_2) & !(g_1 & g_2)))")
    assert game._symmetric_signature(scalar_dependent, buses, spot) is False

    related_counts = spot.formula(
        "G((g_0 & g_1 & g_2) <-> (r_0 & r_1))")
    assert game._symmetric_signature(related_counts, buses, spot) is False


def build_provenance(args, directory, tlsf):
    output = directory / (tlsf.stem + ".aag")
    provenance = directory / (tlsf.stem + ".json")
    run([args.python, args.builder, *tool_args(args),
         "--output", str(output), "--provenance-out", str(provenance),
         str(tlsf)], 0)
    return json.loads(provenance.read_text())


def test_cross_n_provenance(args, directory):
    families = {
        "arbiter": range(2, 5),
        "round_robin_arbiter_unreal2": range(2, 4),
    }
    expected_local = "G(!r_i0 | Fg_i0)"
    for family, sizes in families.items():
        for size in sizes:
            tlsf = (ACACIA_ROOT / "tlsf-corpus" /
                    f"{family}_pb_{size}_pe_.tlsf")
            data = build_provenance(args, directory, tlsf)
            assert data["schema"].endswith(".v2")
            assert data["source_origin_metadata"]["available"] is False
            mutexes = [
                monitor for monitor in data["monitors"]
                if monitor.get("symmetric_signature") == {"g": [0, 1]}
            ]
            assert mutexes, (family, size)
            for mutex in mutexes:
                assert mutex["arity_kind"] == "bus_wide"
                assert mutex["support"]["buses"]["g"] == list(range(size))
                assert mutex["symmetric"] is True
                assert mutex["source_origin"] is None
            local_templates = {
                monitor["template"] for monitor in data["monitors"]
                if monitor["arity_kind"] == "local"
            }
            assert expected_local in local_templates, (family, size)


def tiny_tlsf(semantics, assumptions, guarantees):
    return f'''INFO
{{
  TITLE: "monitor test"
  DESCRIPTION: "generated test"
  SEMANTICS: {semantics}
  TARGET: {semantics}
}}
MAIN
{{
  INPUTS {{ i; }}
  OUTPUTS {{ o; }}
  ASSUMPTIONS {{ {assumptions} }}
  GUARANTEES {{ {guarantees} }}
}}
'''


def test_rejections_and_semantics(args, directory):
    persistence = directory / "persistence.tlsf"
    persistence.write_text(tiny_tlsf("Mealy", "true;", "F G o;"))
    proc = run([args.python, args.builder, *tool_args(args), str(persistence)], 3)
    assert "not dba-reducible" in proc.stderr and "FG" in proc.stderr

    moore = directory / "moore.tlsf"
    moore.write_text(tiny_tlsf("Moore", "true;", "G o;"))
    proc = run([args.python, args.builder, *tool_args(args), str(moore)], 3)
    assert "non-Mealy" in proc.stderr

    # Exact is realizable by holding o=false, thereby violating the liveness
    # assumption GF(o) and excusing the uncontrollable safety guarantee G(i).
    # Strict mode deliberately permits only a *safety* assumption violation to
    # excuse bad, so the environment can choose i=false and strict is unreal.
    difference = directory / "exact-vs-strict.tlsf"
    difference.write_text(tiny_tlsf("Mealy", "G F o;", "G i;"))
    verdicts = {}
    for semantics in ("exact", "strict"):
        game_path = directory / f"difference-{semantics}.aag"
        build = run([args.python, args.builder, *tool_args(args),
                     "--semantics", semantics, "--output", str(game_path),
                     str(difference)], 0)
        if semantics == "strict":
            assert "REAL-sound only" in build.stderr
        text = game_path.read_text()
        assert_gr1_layout(
            text, expected_bad=0 if semantics == "exact" else None)
        solved = run([args.solver, str(game_path)])
        verdicts[semantics] = solved.returncode
    assert verdicts == {"exact": 0, "strict": 1}, verdicts

    liveness = directory / "liveness-only.tlsf"
    liveness.write_text(tiny_tlsf("Mealy", "true;", "G F o;"))
    game_path = directory / "liveness-only.aag"
    run([args.python, args.builder, *tool_args(args), "--semantics", "strict",
         "--output", str(game_path), str(liveness)], 0)
    assert_gr1_layout(game_path.read_text(), expected_bad=0)
    run([args.solver, "--game-profile=gr1", str(game_path)], 0)


def mutate_first_output(text):
    lines = text.splitlines()
    header = [int(value) for value in lines[0].split()[1:]]
    _m, ni, nl, no, _na = header[:5]
    assert no > 0
    position = 1 + ni + nl
    lines[position] = str(int(lines[position]) ^ 1)
    return "\n".join(lines) + "\n"


def mutate_first_latch(text):
    lines = text.splitlines()
    header = [int(value) for value in lines[0].split()[1:]]
    _m, ni, nl, _no, _na = header[:5]
    assert nl > 0
    position = 1 + ni
    fields = lines[position].split()
    fields[1] = str(int(fields[1]) ^ 1)
    lines[position] = " ".join(fields)
    return "\n".join(lines) + "\n"


def test_explicit_checker(args, directory):
    controller = (ACACIA_ROOT /
                  "benchmarking/witness-lifting-20260918/families/seeds/"
                  "arbiter/controllers/arbiter_n2.aag")
    tlsf = ACACIA_ROOT / "tlsf-corpus/arbiter_pb_2_pe_.tlsf"
    base = [args.python, args.verifier, "--tlsf2ltl", args.tlsf2ltl,
            "--tlsf2tlsf", args.tlsf2tlsf, "--tlsfinfo", args.tlsfinfo,
            "--tlsf", str(tlsf), "--strategy"]
    good = run([*base, str(controller)], 0)
    assert good.stdout.strip() == "VERIFIED"

    old = run([args.python, args.old_verifier, "--tlsf2ltl", args.tlsf2ltl,
               "--tlsf", str(tlsf), "--aiger", str(controller)], 0)
    assert old.stdout.strip() == "verified"

    original = controller.read_text()
    for name, mutation in (("output", mutate_first_output),
                           ("latch", mutate_first_latch)):
        mutated = directory / f"mutated-{name}.aag"
        mutated.write_text(mutation(original))
        result = run([*base, str(mutated)], 1)
        assert result.stdout.startswith("REFUTED\nCOUNTEREXAMPLE ")

    capped = run([*base, str(controller), "--state-cap", "1"], 3)
    assert capped.stdout.strip() == "UNKNOWN(state cap)"


def write_aag(path, text):
    path.write_text(text)
    return path


def test_explicit_checker_interface(args, directory):
    tlsf = directory / "partition.tlsf"
    tlsf.write_text(tiny_tlsf("Mealy", "true;", "G i; G o;"))
    base = [args.python, args.verifier, "--tlsf2ltl", args.tlsf2ltl,
            "--tlsf2tlsf", args.tlsf2tlsf, "--tlsfinfo", args.tlsfinfo,
            "--tlsf", str(tlsf), "--strategy"]

    cases = {
        # Reviewer's construction: both TLSF signals are falsely declared as
        # controllable constant-one outputs, so the old AP-only check passed.
        "partition-swap": (
            "aag 0 0 0 2 0\n1\n1\n"
            "o0 controllable_i\no1 controllable_o\n",
            "missing strategy inputs: i"),
        "overlap": (
            "aag 1 1 0 2 0\n2\n1\n1\n"
            "i0 i\no0 controllable_i\no1 controllable_o\n",
            "strategy input/output overlap: i"),
        "missing-output": (
            "aag 1 1 0 0 0\n2\ni0 i\n",
            "missing strategy outputs: o"),
        "controllable-input": (
            "aag 1 1 0 1 0\n2\n1\n"
            "i0 controllable_i\no0 controllable_o\n",
            "missing strategy inputs: i"),
        "duplicate-output": (
            "aag 1 1 0 2 0\n2\n1\n1\n"
            "i0 i\no0 o\no1 controllable_o\n",
            "duplicate strategy outputs: o"),
    }
    for name, (text, reason) in cases.items():
        strategy = write_aag(directory / f"{name}.aag", text)
        result = run([*base, str(strategy)], 4)
        assert result.stdout.strip() == "INVALID"
        assert reason in result.stderr


def parse_args(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--builder", required=True)
    parser.add_argument("--verifier", required=True)
    parser.add_argument("--old-verifier", required=True)
    parser.add_argument("--tlsf2ltl", required=True)
    parser.add_argument("--tlsf2tlsf", required=True)
    parser.add_argument("--tlsfinfo", required=True)
    parser.add_argument("--solver", required=True)
    return parser.parse_args(argv)


def main(argv):
    args = parse_args(argv)
    import spot
    test_split_rule(args, spot)
    test_monitor_encoding(args, spot)
    test_symmetric_signature(spot)
    with tempfile.TemporaryDirectory(prefix="gr1-monitor-test-") as temp:
        directory = pathlib.Path(temp)
        test_rejections_and_semantics(args, directory)
        test_explicit_checker(args, directory)
        test_explicit_checker_interface(args, directory)
        test_cross_n_provenance(args, directory)
    print("gr1 monitor game tests: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
