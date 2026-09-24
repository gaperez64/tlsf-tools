#!/usr/bin/env python3
"""Explicitly verify an AAG strategy against the original lowered TLSF LTL.

This checker deliberately does not use Spot's AIGER reader or any monitor-game
artifact.  It parses and simulates the strategy circuit itself, enumerates all
reachable latch valuations by BFS over every uncontrollable input valuation,
and builds a Spot automaton for the resulting closed-loop traces.  Every edge
is labelled with the full input/output letter and every state is accepting.
Language inclusion is checked by taking the product with an automaton for the
negation of the original formula. The lowered formula shares the canonical AP
tokenizer with the monitor builder so legal TLSF identifiers parse in Spot.

Results and exit codes are ``VERIFIED`` (0), ``REFUTED`` (1), tool/runtime
``ERROR`` (2), ``UNKNOWN(state cap)`` (3), and ``INVALID`` (4).  INVALID means
the strategy is malformed or its declared input/output partition is not
exactly the expanded TLSF interface.  The construction is independent of
monitor-game artifacts and is intended for strategies that Spot's AIGER reader
cannot ingest because of its latch-count or structural assertions.
"""

from __future__ import annotations

import argparse
import dataclasses
import pathlib
import subprocess
import sys
from collections import deque

from gr1_monitor_game import canonical_signals, parse_canonical_ltl, tlsf_formula


CONTROLLABLE_PREFIX = "controllable_"
EXIT_VERIFIED = 0
EXIT_REFUTED = 1
EXIT_ERROR = 2
EXIT_UNKNOWN = 3
EXIT_INVALID = 4


class InvalidStrategy(ValueError):
    pass


def default_tool(name: str) -> str:
    """Prefer the sibling build-oxidd tool, falling back to PATH."""
    candidate = pathlib.Path(__file__).resolve().parent.parent / "build-oxidd" / name
    return str(candidate) if candidate.is_file() else name


@dataclasses.dataclass
class ParsedAag:
    maxvar: int
    inputs: list[int]
    input_names: list[str]
    latches: list[tuple[int, int, int]]
    latch_names: list[str]
    outputs: list[int]
    output_names: list[str]
    gates: list[tuple[int, int, int]]

    def initial_state(self) -> int:
        state = 0
        for index, (current, _next_lit, reset) in enumerate(self.latches):
            if reset == 1:
                state |= 1 << index
            elif reset != 0:
                raise ValueError(
                    f"unsupported latch reset {reset} for literal {current}")
        return state

    @staticmethod
    def _lit_value(lit: int, values: list[bool]) -> bool:
        if lit < 2:
            return lit == 1
        value = values[lit // 2]
        return not value if lit & 1 else value

    def simulate(self, state: int, input_bits: int):
        values = [False] * (self.maxvar + 1)
        for index, lit in enumerate(self.inputs):
            values[lit // 2] = bool((input_bits >> index) & 1)
        for index, (current, _next_lit, _reset) in enumerate(self.latches):
            values[current // 2] = bool((state >> index) & 1)
        for lhs, rhs0, rhs1 in self.gates:
            values[lhs // 2] = (self._lit_value(rhs0, values)
                                and self._lit_value(rhs1, values))
        next_state = 0
        for index, (_current, next_lit, _reset) in enumerate(self.latches):
            if self._lit_value(next_lit, values):
                next_state |= 1 << index
        output_values = [self._lit_value(lit, values) for lit in self.outputs]
        input_values = [bool((input_bits >> index) & 1)
                        for index in range(len(self.inputs))]
        return next_state, input_values, output_values


def parse_aag(text: str) -> ParsedAag:
    lines = text.splitlines()
    if lines and lines[0] in ("REALIZABLE", "UNREALIZABLE"):
        lines = lines[1:]
    if not lines or not lines[0].startswith("aag "):
        raise ValueError("missing ASCII AIGER header")
    fields = [int(value) for value in lines[0].split()[1:]]
    if len(fields) < 5:
        raise ValueError("short ASCII AIGER header")
    fields += [0] * (9 - len(fields))
    maxvar, ni, nl, no, na, nb, nc, nj, nf = fields[:9]
    position = 1

    def take() -> str:
        nonlocal position
        if position >= len(lines):
            raise ValueError("truncated ASCII AIGER file")
        line = lines[position]
        position += 1
        return line

    inputs = [int(take().split()[0]) for _ in range(ni)]
    latches: list[tuple[int, int, int]] = []
    for _ in range(nl):
        latch = [int(value) for value in take().split()]
        if len(latch) < 2:
            raise ValueError("malformed ASCII AIGER latch")
        latches.append((latch[0], latch[1], latch[2] if len(latch) > 2 else 0))
    outputs = [int(take().split()[0]) for _ in range(no)]
    for _ in range(nb + nc):
        take()
    justice_sizes = [int(take().split()[0]) for _ in range(nj)]
    for size in justice_sizes:
        for _ in range(size):
            take()
    for _ in range(nf):
        take()
    gates = []
    for _ in range(na):
        gate = [int(value) for value in take().split()]
        if len(gate) != 3:
            raise ValueError("malformed ASCII AIGER AND gate")
        gates.append(tuple(gate))

    input_names = [f"i{index}" for index in range(ni)]
    latch_names = [f"l{index}" for index in range(nl)]
    output_names = [f"o{index}" for index in range(no)]
    while position < len(lines):
        line = take()
        if line == "c":
            break
        if len(line) < 3 or line[0] not in "ilo":
            continue
        label, name = line.split(maxsplit=1)
        try:
            index = int(label[1:])
        except ValueError:
            continue
        if label[0] == "i" and index < ni:
            input_names[index] = name
        elif label[0] == "l" and index < nl:
            latch_names[index] = name
        elif label[0] == "o" and index < no:
            output_names[index] = name
    return ParsedAag(maxvar, inputs, input_names, latches, latch_names,
                     outputs, output_names, gates)


def _run(command: list[str], *, input_text: str | None = None) -> str:
    proc = subprocess.run(
        command, input=input_text, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=False)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise RuntimeError(
            f"{pathlib.Path(command[0]).name} failed with exit {proc.returncode}")
    return proc.stdout.strip()


def _run_formula(tlsf2ltl: str, tlsf: str, params: list[str]) -> str:
    options = [item for value in params for item in ("--param", value)]
    return _run([tlsf2ltl, "--format", "ltl", *options, tlsf])


def _tlsf_interface(tlsf2tlsf: str, tlsfinfo: str, tlsf: str,
                    params: list[str]) -> tuple[list[str], list[str]]:
    options = [item for value in params for item in ("--param", value)]
    basic = _run([tlsf2tlsf, "--basic", *options, tlsf])

    def signals(selection: str) -> list[str]:
        text = _run([tlsfinfo, selection], input_text=basic)
        return [name.strip() for name in text.split(",") if name.strip()]

    return signals("--expanded-ins"), signals("--expanded-outs")


def reachable_graph(circuit: ParsedAag, state_cap: int):
    initial = circuit.initial_state()
    states = {initial: 0}
    queue = deque([initial])
    transitions: list[list[tuple[int, list[bool], list[bool]]]] = []
    while queue:
        state = queue.popleft()
        state_id = states[state]
        while len(transitions) <= state_id:
            transitions.append([])
        for input_bits in range(1 << len(circuit.inputs)):
            next_state, input_values, output_values = circuit.simulate(
                state, input_bits)
            if next_state not in states:
                if len(states) >= state_cap:
                    return None
                states[next_state] = len(states)
                queue.append(next_state)
            transitions[state_id].append(
                (states[next_state], input_values, output_values))
    return transitions


def _canonical_outputs(names: list[str], expected: list[str]) -> list[str]:
    # Standalone controllers use TLSF names. Older strategy producers may
    # retain game prefixes; choose one interpretation for the whole interface.
    if set(names) == set(expected):
        return names
    return [name[len(CONTROLLABLE_PREFIX):]
            if name.startswith(CONTROLLABLE_PREFIX) else name
            for name in names]


def _duplicates(names: list[str]) -> list[str]:
    seen: set[str] = set()
    duplicate: set[str] = set()
    for name in names:
        if name in seen:
            duplicate.add(name)
        seen.add(name)
    return sorted(duplicate)


def validate_interface(circuit: ParsedAag, expected_inputs: list[str],
                       expected_outputs: list[str]) -> list[str]:
    """Require the strategy declarations to exactly match the TLSF partition."""
    actual_inputs = circuit.input_names
    actual_outputs = _canonical_outputs(circuit.output_names, expected_outputs)
    problems: list[str] = []

    for label, names in (("TLSF inputs", expected_inputs),
                         ("TLSF outputs", expected_outputs),
                         ("strategy inputs", actual_inputs),
                         ("strategy outputs", actual_outputs)):
        duplicate = _duplicates(names)
        if duplicate:
            problems.append(f"duplicate {label}: {','.join(duplicate)}")

    expected_overlap = sorted(set(expected_inputs) & set(expected_outputs))
    if expected_overlap:
        raise RuntimeError(
            "expanded TLSF input/output overlap: " + ",".join(expected_overlap))
    overlap = sorted(set(actual_inputs) & set(actual_outputs))
    if overlap:
        problems.append("strategy input/output overlap: " + ",".join(overlap))

    for label, expected, actual in (
            ("inputs", set(expected_inputs), set(actual_inputs)),
            ("outputs", set(expected_outputs), set(actual_outputs))):
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        if missing:
            problems.append(f"missing strategy {label}: {','.join(missing)}")
        if extra:
            problems.append(f"extra strategy {label}: {','.join(extra)}")
    if problems:
        raise InvalidStrategy("; ".join(problems))
    return actual_outputs


def verify(circuit: ParsedAag, formula, state_cap: int, spot_module,
           buddy_module, output_names: list[str]):
    graph = reachable_graph(circuit, state_cap)
    if graph is None:
        return "unknown", None

    input_names = circuit.input_names
    available = set(input_names) | set(output_names)
    formula_aps = {ap.ap_name() for ap in spot_module.atomic_prop_collect(formula)}
    missing = sorted(formula_aps - available)
    if missing:
        raise ValueError("formula APs missing from strategy symbols: "
                         + ",".join(missing))

    dictionary = spot_module.make_bdd_dict()
    translator = spot_module.translator(dictionary)
    negated = translator.run(spot_module.formula.Not(formula))
    dictionary = negated.get_dict()
    system = spot_module.make_twa_graph(dictionary)
    system.new_states(len(graph))
    system.set_init_state(0)
    system.set_buchi()
    all_names = input_names + output_names
    variables = {name: system.register_ap(name) for name in all_names}

    for src, outgoing in enumerate(graph):
        grouped = {}
        for dst, input_values, output_values in outgoing:
            values = input_values + output_values
            cube = buddy_module.bddtrue
            for name, value in zip(all_names, values):
                atom = buddy_module.bdd_ithvar(variables[name])
                cube &= atom if value else -atom
            grouped[dst] = grouped.get(dst, buddy_module.bddfalse) | cube
        for dst, condition in grouped.items():
            system.new_edge(src, dst, condition, spot_module.mark_t([0]))
    system.prop_state_acc(True)

    product = spot_module.product(system, negated)
    if product.is_empty():
        return "verified", None
    try:
        counterexample = product.accepting_word()
    except RuntimeError:
        counterexample = None
    return "refuted", counterexample


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Explicitly verify an AAG strategy against original TLSF LTL.",
        epilog=(
            "Exit codes: 0 VERIFIED, 1 REFUTED, 2 tool/runtime error, "
            "3 UNKNOWN(state cap), 4 INVALID strategy/interface."))
    parser.add_argument("--strategy", "--aiger", dest="strategy", required=True,
                        help="strategy AAG from tlsfsolve or another Mealy solver")
    parser.add_argument("--tlsf", required=True, help="original TLSF instance")
    parser.add_argument("--tlsf2ltl", default=default_tool("tlsf2ltl"))
    parser.add_argument("--tlsf2tlsf", default=default_tool("tlsf2tlsf"))
    parser.add_argument("--tlsfinfo", default=default_tool("tlsfinfo"))
    parser.add_argument("--param", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--state-cap", type=int, default=100000,
                        help="maximum reachable latch valuations (default: 100000)")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.state_cap < 1:
        sys.stderr.write("verify-strategy-explicit: --state-cap must be positive\n")
        return EXIT_ERROR
    try:
        import buddy
        import spot
    except ImportError as exc:
        sys.stderr.write(
            f"verify-strategy-explicit: Spot Python bindings required: {exc}\n")
        return EXIT_ERROR
    try:
        with open(args.strategy, encoding="utf-8") as stream:
            circuit = parse_aag(stream.read())
    except (OSError, ValueError) as exc:
        print("INVALID")
        sys.stderr.write(f"verify-strategy-explicit: {exc}\n")
        return EXIT_INVALID
    try:
        expected_inputs, expected_outputs = _tlsf_interface(
            args.tlsf2tlsf, args.tlsfinfo, args.tlsf, args.param)
        output_names = validate_interface(circuit, expected_inputs,
                                          expected_outputs)
        symbols = canonical_signals(expected_inputs, expected_outputs)
        formula = tlsf_formula(parse_canonical_ltl(
            _run_formula(args.tlsf2ltl, args.tlsf, args.param), symbols, spot),
            symbols, spot)
        result, counterexample = verify(
            circuit, formula, args.state_cap, spot, buddy, output_names)
    except InvalidStrategy as exc:
        print("INVALID")
        sys.stderr.write(f"verify-strategy-explicit: {exc}\n")
        return EXIT_INVALID
    except (OSError, RuntimeError, ValueError) as exc:
        sys.stderr.write(f"verify-strategy-explicit: {exc}\n")
        return EXIT_ERROR

    if result == "verified":
        print("VERIFIED")
        return EXIT_VERIFIED
    if result == "unknown":
        print("UNKNOWN(state cap)")
        return EXIT_UNKNOWN
    print("REFUTED")
    if counterexample is not None:
        print(f"COUNTEREXAMPLE {counterexample}")
    return EXIT_REFUTED


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
