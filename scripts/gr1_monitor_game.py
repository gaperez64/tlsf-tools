#!/usr/bin/env python3
"""Build an exact per-conjunct deterministic-Buchi GR(1) game from TLSF.

The lowered objective is split as ``A -> G`` and then flattened exactly like
the param-lift M0 census: top-level conjunctions are flattened, a conjunction
immediately below ``G`` is distributed, and ``true`` conjuncts are dropped.
Every remaining conjunct must be in Manna--Pnueli class B/G/S/O/R.  It is
translated independently to a complete deterministic state-based Buchi
automaton; the script never constructs an automaton for the whole objective.

Monitor states use a one-hot encoding (one latch per automaton state).  The
latch reset vector selects the automaton's initial state, next-state logic reads
the current Mealy letter, and the acceptance literal is the OR of the latches
for accepting states.  Consequently each monitor contributes only its own
small state machine and the total construction is linear in the number of
top-level conjuncts when their shapes are bounded.

``--semantics exact`` emits every assumption acceptance as AIGER fairness and
every guarantee acceptance as singleton justice, with a constant-false safety
output.  This is exactly the lowered implication.  ``--semantics strict``
follows tlsf-tools' strict GR(1) convention: B/S assumption monitors set a
sticky ``violated`` latch on reaching a rejecting sink, B/S guarantee monitors
drive ``bad`` until that violation, and other monitors remain fairness/justice.
A strict REALIZABLE result implies realizability of the plain implication, but
a strict UNREALIZABLE result is not a sound unrealizability result.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import itertools
import json
import pathlib
import re
import subprocess
import sys
import tempfile
from collections.abc import Iterable


EXIT_UNSUPPORTED = 3
DBA_CLASSES = frozenset("BGSOR")
SAFETY_CLASSES = frozenset("BS")
CONTROLLABLE_PREFIX = "controllable_"
UNCONTROLLABLE_PREFIX = "uncontrollable_"
_LTL_TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|[A-Za-z_@][A-Za-z0-9_\'@]*')


def canonical_signals(inputs: list[str], outputs: list[str]) -> dict[str, str]:
    """Assign names from the expanded interface order, independent of spelling."""
    names = [*inputs, *outputs]
    if len(names) != len(set(names)):
        raise ValueError("expanded TLSF signal names are not unique")
    return {**{name: f"uncontrollable_i{index}"
               for index, name in enumerate(inputs)},
            **{name: f"controllable_o{index}"
               for index, name in enumerate(outputs)}}


def canonicalize_ltl(text: str, symbols: dict[str, str]) -> str:
    """Rewrite complete lexer tokens, including TLSF's @ and prime identifiers.

    The lowering tool emits LTL syntax around bare TLSF AP tokens.  A quoted
    AP is handled as one token as well, so neither substrings nor quoted text
    can be accidentally changed.  Spot's AP inventory is checked after parse.
    """
    def replace(match: re.Match[str]) -> str:
        token = match.group()
        if token.startswith('"'):
            name = json.loads(token)
            return symbols.get(name, token)
        return symbols.get(token, token)

    return _LTL_TOKEN.sub(replace, text)


def canonical_formula_text(formula, spot_module) -> str:
    """Print commutative operands in lexical order, independent of Spot IDs."""
    kind = formula.kind()
    if kind in (spot_module.op_And, spot_module.op_Or):
        operator = " & " if kind == spot_module.op_And else " | "
        return "(" + operator.join(sorted(
            canonical_formula_text(child, spot_module) for child in formula)) + ")"
    for operator, name in ((spot_module.op_G, "G"),
                           (spot_module.op_F, "F"),
                           (spot_module.op_X, "X"),
                           (spot_module.op_Not, "!")):
        if kind == operator:
            return name + "(" + canonical_formula_text(formula[0], spot_module) + ")"
    for operator, name in ((spot_module.op_Xor, "xor"),
                           (spot_module.op_Implies, "->"),
                           (spot_module.op_Equiv, "<->"),
                           (spot_module.op_U, "U"),
                           (spot_module.op_R, "R"),
                           (spot_module.op_W, "W"),
                           (spot_module.op_M, "M")):
        if kind == operator:
            children = [canonical_formula_text(formula[index], spot_module)
                        for index in (0, 1)]
            if kind in (spot_module.op_Xor, spot_module.op_Equiv):
                children.sort()
            return "(" + (" " + name + " ").join(children) + ")"
    return str(formula)


def parse_canonical_ltl(text: str, symbols: dict[str, str], spot_module):
    formula = spot_module.formula(canonicalize_ltl(text, symbols))
    aps = {ap.ap_name() for ap in spot_module.atomic_prop_collect(formula)}
    unknown = aps - set(symbols.values())
    if unknown:
        raise ValueError(f"lowered formula has undeclared APs: {sorted(unknown)}")
    return formula


def default_tool(name: str) -> str:
    """Prefer the sibling build-oxidd tool, falling back to PATH."""
    candidate = pathlib.Path(__file__).resolve().parent.parent / "build-oxidd" / name
    return str(candidate) if candidate.is_file() else name


def conjuncts(formula, spot_module):
    """Yield conjuncts using the exact M0 census splitting rule."""
    if formula.kind() == spot_module.op_And:
        for child in formula:
            yield from conjuncts(child, spot_module)
    elif (formula.kind() == spot_module.op_G
          and formula[0].kind() == spot_module.op_And):
        for child in formula[0]:
            yield from conjuncts(spot_module.formula.G(child), spot_module)
    elif not formula.is_tt():
        yield formula


def split_objective(formula, spot_module):
    if formula.kind() == spot_module.op_Implies:
        assume, guarantee = formula[0], formula[1]
    else:
        assume, guarantee = spot_module.formula.tt(), formula
    return (list(conjuncts(assume, spot_module)),
            list(conjuncts(guarantee, spot_module)))


@dataclasses.dataclass
class Monitor:
    side: str
    formula: object
    mp_class: str
    automaton: object
    accepting: tuple[bool, ...]
    rejecting: tuple[bool, ...]
    latch_literals: list[int] = dataclasses.field(default_factory=list)
    role: str = ""


def _state_acceptance(aut) -> tuple[bool, ...]:
    result: list[bool] = []
    for state in range(aut.num_states()):
        marks = {bool(edge.acc) for edge in aut.out(state)}
        if len(marks) != 1:
            raise RuntimeError(
                "Spot did not produce state-based acceptance for monitor")
        result.append(marks.pop())
    return tuple(result)


def _rejecting_states(aut, accepting: tuple[bool, ...]) -> tuple[bool, ...]:
    """Return states whose residual Buchi language is empty.

    A state is live iff it can reach a cyclic SCC containing an accepting
    state.  For a safety-language DBA, the complement is precisely the
    rejecting sink region used by strict semantics.
    """
    count = aut.num_states()
    succ = [set() for _ in range(count)]
    pred = [set() for _ in range(count)]
    for src in range(count):
        for edge in aut.out(src):
            succ[src].add(edge.dst)
            pred[edge.dst].add(src)

    # Tarjan is kept local to avoid depending on implementation-specific Spot
    # SCC bindings in this small standalone script.
    index = 0
    indices = [-1] * count
    lowlink = [0] * count
    stack: list[int] = []
    on_stack = [False] * count
    components: list[list[int]] = []

    def visit(node: int) -> None:
        nonlocal index
        indices[node] = lowlink[node] = index
        index += 1
        stack.append(node)
        on_stack[node] = True
        for dst in succ[node]:
            if indices[dst] < 0:
                visit(dst)
                lowlink[node] = min(lowlink[node], lowlink[dst])
            elif on_stack[dst]:
                lowlink[node] = min(lowlink[node], indices[dst])
        if lowlink[node] == indices[node]:
            component: list[int] = []
            while True:
                member = stack.pop()
                on_stack[member] = False
                component.append(member)
                if member == node:
                    break
            components.append(component)

    for state in range(count):
        if indices[state] < 0:
            visit(state)

    live = set()
    for component in components:
        cyclic = len(component) > 1 or component[0] in succ[component[0]]
        if cyclic and any(accepting[state] for state in component):
            live.update(component)
    pending = list(live)
    while pending:
        state = pending.pop()
        for parent in pred[state]:
            if parent not in live:
                live.add(parent)
                pending.append(parent)
    return tuple(state not in live for state in range(count))


def build_monitor(formula, side: str, spot_module) -> Monitor:
    mp_class = spot_module.mp_class(formula)
    if mp_class not in DBA_CLASSES:
        raise ValueError(f"not dba-reducible ({mp_class}): {formula}")

    aut = spot_module.translate(
        formula, "BA", "complete", "state-based", "deterministic")
    if not spot_module.is_deterministic(aut):
        # MP class <= recurrence guarantees that a DBA exists.  Spot's normal
        # translation treats determinism as a preference.  Determinization to
        # parity is language preserving; because this language is known to be
        # DBA-realizable, Spot's Rabin-like -> Buchi conversion then preserves
        # both the language and determinism.  This route avoids the potentially
        # very expensive post-hoc equivalence check in tba_determinize_check().
        parity = spot_module.tgba_determinize(aut)
        deterministic = spot_module.rabin_to_buchi_if_realizable(parity)
        if deterministic is None:
            deterministic = spot_module.rabin_to_buchi_maybe(parity)
        if deterministic is None:
            raise RuntimeError(
                f"Spot could not construct recurrence DBA monitor: {formula}")
        aut = deterministic
    aut = spot_module.complete(spot_module.sbacc(aut))
    if not spot_module.is_deterministic(aut):
        raise RuntimeError(f"Spot failed to determinize DBA monitor: {formula}")
    if not spot_module.is_complete(aut):
        raise RuntimeError(f"Spot produced incomplete DBA monitor: {formula}")
    accepting = _state_acceptance(aut)
    rejecting = _rejecting_states(aut, accepting)
    if mp_class in SAFETY_CLASSES:
        for state, rejected in enumerate(rejecting):
            if rejected and any(not rejecting[e.dst] for e in aut.out(state)):
                raise RuntimeError(
                    f"non-sticky rejecting region in safety monitor: {formula}")
    return Monitor(side, formula, mp_class, aut, accepting, rejecting)


class AagBuilder:
    """Small strashed ASCII-AIGER builder with fixed input/latch ordering."""

    def __init__(self, input_names: list[str]):
        self.input_names = input_names
        self.game_input_literals = {
            name: 2 * (index + 1) for index, name in enumerate(input_names)
        }
        self.input_literals = self.game_input_literals.copy()
        self._next_var = len(input_names)
        self.latches: list[list[int | str]] = []  # current, next, reset, name
        self.ands: list[tuple[int, int, int]] = []
        self._and_cache: dict[tuple[int, int], int] = {}

    def add_latch(self, reset: int, name: str) -> int:
        self._next_var += 1
        lit = 2 * self._next_var
        self.latches.append([lit, 0, reset, name])
        return lit

    def set_latch_next(self, current: int, next_lit: int) -> None:
        for latch in self.latches:
            if latch[0] == current:
                latch[1] = next_lit
                return
        raise KeyError(f"unknown latch literal {current}")

    @staticmethod
    def negate(lit: int) -> int:
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
        key = tuple(sorted((left, right)))
        if key in self._and_cache:
            return self._and_cache[key]
        self._next_var += 1
        result = 2 * self._next_var
        self.ands.append((result, key[0], key[1]))
        self._and_cache[key] = result
        return result

    def lor(self, left: int, right: int) -> int:
        return self.negate(self.land(self.negate(left), self.negate(right)))

    def land_all(self, literals: Iterable[int]) -> int:
        result = 1
        for lit in literals:
            result = self.land(result, lit)
        return result

    def lor_all(self, literals: Iterable[int]) -> int:
        result = 0
        for lit in literals:
            result = self.lor(result, lit)
        return result

    def compile_boolean(self, formula, spot_module) -> int:
        kind = formula.kind()
        if formula.is_tt():
            return 1
        if formula.is_ff():
            return 0
        if kind == spot_module.op_ap:
            name = str(formula)
            if name not in self.input_literals:
                raise RuntimeError(f"monitor refers to undeclared signal {name!r}")
            return self.input_literals[name]
        if kind == spot_module.op_Not:
            return self.negate(self.compile_boolean(formula[0], spot_module))
        if kind == spot_module.op_And:
            return self.land_all(
                self.compile_boolean(child, spot_module) for child in formula)
        if kind == spot_module.op_Or:
            return self.lor_all(
                self.compile_boolean(child, spot_module) for child in formula)
        if kind == spot_module.op_Xor:
            left = self.compile_boolean(formula[0], spot_module)
            right = self.compile_boolean(formula[1], spot_module)
            return self.lor(self.land(left, self.negate(right)),
                            self.land(self.negate(left), right))
        if kind == spot_module.op_Implies:
            left = self.compile_boolean(formula[0], spot_module)
            right = self.compile_boolean(formula[1], spot_module)
            return self.lor(self.negate(left), right)
        if kind == spot_module.op_Equiv:
            left = self.compile_boolean(formula[0], spot_module)
            right = self.compile_boolean(formula[1], spot_module)
            return self.lor(self.land(left, right),
                            self.land(self.negate(left), self.negate(right)))
        raise RuntimeError(f"non-Boolean monitor transition label: {formula}")

    def render(self, bad: int | None, justice: list[int], fairness: list[int]) -> str:
        if any(int(latch[1]) == 0 and latch[3] == "" for latch in self.latches):
            raise RuntimeError("unset AIGER latch next-state")
        bad_lit = 0 if bad is None else bad
        justice_lits = justice or [1]
        lines = [
            f"aag {self._next_var} {len(self.input_names)} {len(self.latches)} "
            f"1 {len(self.ands)} 0 0 {len(justice_lits)} {len(fairness)}"
        ]
        lines.extend(str(self.game_input_literals[name])
                     for name in self.input_names)
        for current, next_lit, reset, _name in self.latches:
            lines.append(f"{current} {next_lit} {reset}")
        lines.append(str(bad_lit))
        lines.extend("1" for _ in justice_lits)
        lines.extend(str(lit) for lit in justice_lits)
        lines.extend(str(lit) for lit in fairness)
        lines.extend(f"{lhs} {rhs0} {rhs1}" for lhs, rhs0, rhs1 in self.ands)
        lines.extend(f"i{index} {name}"
                     for index, name in enumerate(self.input_names))
        lines.extend(f"l{index} {latch[3]}"
                     for index, latch in enumerate(self.latches))
        lines.append("o0 bad")
        lines.extend(f"j{index} guarantee_monitor_{index}"
                     for index in range(len(justice_lits)))
        lines.extend(f"f{index} assumption_monitor_{index}"
                     for index in range(len(fairness)))
        lines.append("c")
        lines.append("generated by gr1_monitor_game.py; one-hot DBA monitors")
        return "\n".join(lines) + "\n"


def _transition_formula(aut, edge, spot_module):
    return spot_module.formula(
        spot_module.bdd_format_formula(aut.get_dict(), edge.cond))


def encode_game(monitors: list[Monitor], inputs: list[str], outputs: list[str],
                semantics: str, spot_module,
                symbols: dict[str, str] | None = None):
    raw_monitor_aps = symbols is None
    symbols = symbols or canonical_signals(inputs, outputs)
    game_inputs = [symbols[name] for name in [*inputs, *outputs]]
    builder = AagBuilder(game_inputs)
    # Direct callers can pass monitors over raw APs.  The CLI path parses
    # canonical APs, so aliases there could overwrite a different signal.
    if raw_monitor_aps:
        for name, symbol in symbols.items():
            builder.input_literals[name] = builder.game_input_literals[symbol]
    for monitor_index, monitor in enumerate(monitors):
        initial = monitor.automaton.get_init_state_number()
        monitor.latch_literals = [
            builder.add_latch(
                int(state == initial), f"monitor_{monitor_index}_state_{state}")
            for state in range(monitor.automaton.num_states())
        ]

    strict_safety_assumptions = [
        monitor for monitor in monitors
        if semantics == "strict" and monitor.side == "assumption"
        and monitor.mp_class in SAFETY_CLASSES
    ]
    violated_lit = None
    if strict_safety_assumptions:
        violated_lit = builder.add_latch(0, "assumption_safety_violated")

    for monitor in monitors:
        incoming: list[list[int]] = [
            [] for _ in range(monitor.automaton.num_states())]
        for src in range(monitor.automaton.num_states()):
            for edge in monitor.automaton.out(src):
                condition = builder.compile_boolean(
                    _transition_formula(monitor.automaton, edge, spot_module),
                    spot_module)
                incoming[edge.dst].append(
                    builder.land(monitor.latch_literals[src], condition))
        for state, latch in enumerate(monitor.latch_literals):
            builder.set_latch_next(latch, builder.lor_all(incoming[state]))

    accepting_lits = {
        id(monitor): builder.lor_all(
            lit for lit, accepting in zip(monitor.latch_literals,
                                          monitor.accepting)
            if accepting)
        for monitor in monitors
    }
    rejecting_lits = {
        id(monitor): builder.lor_all(
            lit for lit, rejecting in zip(monitor.latch_literals,
                                          monitor.rejecting)
            if rejecting)
        for monitor in monitors
    }

    release = violated_lit if violated_lit is not None else 0
    if violated_lit is not None:
        current_violation = builder.lor_all(
            rejecting_lits[id(monitor)]
            for monitor in strict_safety_assumptions)
        release = builder.lor(violated_lit, current_violation)
        builder.set_latch_next(violated_lit, release)

    justice: list[int] = []
    fairness: list[int] = []
    bad_terms: list[int] = []
    for monitor in monitors:
        acceptance = accepting_lits[id(monitor)]
        if semantics == "exact":
            if monitor.side == "assumption":
                monitor.role = "fairness"
                fairness.append(acceptance)
            else:
                monitor.role = "justice"
                justice.append(acceptance)
        elif monitor.mp_class in SAFETY_CLASSES:
            if monitor.side == "assumption":
                monitor.role = "violated"
            else:
                monitor.role = "bad"
                bad_terms.append(rejecting_lits[id(monitor)])
        elif monitor.side == "assumption":
            monitor.role = "fairness"
            fairness.append(acceptance)
        else:
            monitor.role = "justice"
            justice.append(builder.lor(acceptance, release))

    bad = None
    if semantics == "strict" and bad_terms:
        bad = builder.land(builder.lor_all(bad_terms), builder.negate(release))
    return builder.render(bad, justice, fairness), builder, violated_lit


_INDEXED_AP = re.compile(r"\b([A-Za-z][A-Za-z0-9]*?(?:_[A-Za-z][A-Za-z0-9]*)*)((?:_\d+)+)\b")


def split_signal_index(name: str) -> tuple[str, list[int]]:
    match = re.match(r"^(.*?)(_(?:\d+)(?:_\d+)*)$", name)
    if not match:
        return name, []
    return match.group(1), [int(value) for value in match.group(2).split("_")[1:]]


def index_template(text: str) -> tuple[str, list[int]]:
    """Abstract numeric AP suffixes by first-occurrence equality pattern.

    Each distinct concrete index is assigned ``i0``, ``i1``, ... on first
    occurrence while scanning the canonical Spot formula string left-to-right.
    Repeated equal indices reuse the same symbol.  ``index_tuple`` stores the
    corresponding concrete values in symbol order.  This makes, for example,
    ``G(r_0 -> F(g_0))`` and ``G(r_7 -> F(g_7))`` share a template while
    retaining respectively ``[0]`` and ``[7]`` as their concrete tuples.
    """
    positions: dict[int, int] = {}
    concrete: list[int] = []

    def replace(match: re.Match[str]) -> str:
        suffix = match.group(2)
        symbolic = []
        for raw in suffix.split("_")[1:]:
            value = int(raw)
            if value not in positions:
                positions[value] = len(concrete)
                concrete.append(value)
            symbolic.append(f"i{positions[value]}")
        return match.group(1) + "_" + "_".join(symbolic)

    return _INDEXED_AP.sub(replace, text), concrete


def _bus_inventory(signals: list[str]) -> dict[str, list[tuple[str, tuple[int, ...]]]]:
    buses: dict[str, list[tuple[str, tuple[int, ...]]]] = {}
    for name in signals:
        base, indices = split_signal_index(name)
        if indices:
            buses.setdefault(base, []).append((name, tuple(indices)))
    for members in buses.values():
        members.sort(key=lambda member: member[1])
    return buses


def _frontend_bus_inventory(signals: list[dict]) -> dict[str, list[tuple[str, tuple[int, ...]]]]:
    buses: dict[str, list[tuple[str, tuple[int, ...]]]] = {}
    for signal in signals:
        if signal["dimensions"]:
            buses.setdefault(signal["source_name"], []).append(
                (signal["name"], tuple(signal["index_tuple"])))
    for members in buses.values():
        members.sort(key=lambda member: member[1])
    return buses


def _structural_template(formula, signals: dict[str, dict], spot_module) -> str:
    names = {ap.ap_name() for ap in spot_module.atomic_prop_collect(formula)}
    ordered = sorted((signals[name] for name in names),
                     key=lambda item: (item["direction"],
                                       item["declaration_id"],
                                       item["index_tuple"]))
    coordinates: dict[int, int] = {}
    replacements = {}
    for signal in ordered:
        direction, ordinal = signal["declaration_id"].split(":")
        alias = f"s_{direction}_{ordinal}"
        for value in signal["index_tuple"]:
            coordinates.setdefault(value, len(coordinates))
            alias += f"_i{coordinates[value]}"
        replacements[signal["name"]] = spot_module.formula.ap(alias)
    return canonical_formula_text(
        _replace_aps(formula, replacements, spot_module), spot_module)


def _display_indices(indices: list[tuple[int, ...]]) -> list:
    if all(len(index) == 1 for index in indices):
        return [index[0] for index in indices]
    return [list(index) for index in indices]


def _monitor_support(formula, buses, spot_module) -> tuple[dict, str]:
    aps = {ap.ap_name() for ap in spot_module.atomic_prop_collect(formula)}
    supported: dict[str, list[tuple[int, ...]]] = {}
    bus_aps: set[str] = set()
    bus_wide = False
    for base, members in buses.items():
        present = [(name, index) for name, index in members if name in aps]
        if not present:
            continue
        supported[base] = [index for _name, index in present]
        bus_aps.update(name for name, _index in present)
        if len(present) == len(members):
            bus_wide = True
    support = {
        "buses": {
            base: _display_indices(indices)
            for base, indices in sorted(supported.items())
        },
        "scalars": sorted(aps - bus_aps),
    }
    return support, "bus_wide" if bus_wide else "local"


def _replace_aps(formula, replacements: dict[str, object], spot_module):
    mapping = spot_module.relabeling_map()
    for source, target in replacements.items():
        mapping[spot_module.formula.ap(source)] = target
    return spot_module.relabel_apply(formula, mapping)


def tlsf_formula(formula, symbols: dict[str, str], spot_module):
    return _replace_aps(
        formula, {canonical: spot_module.formula.ap(original)
                  for original, canonical in symbols.items()}, spot_module)


def _eval_boolean(formula, valuation: dict[str, bool], spot_module) -> bool:
    kind = formula.kind()
    if formula.is_tt():
        return True
    if formula.is_ff():
        return False
    if kind == spot_module.op_ap:
        return valuation[formula.ap_name()]
    if kind == spot_module.op_Not:
        return not _eval_boolean(formula[0], valuation, spot_module)
    if kind == spot_module.op_And:
        return all(_eval_boolean(child, valuation, spot_module)
                   for child in formula)
    if kind == spot_module.op_Or:
        return any(_eval_boolean(child, valuation, spot_module)
                   for child in formula)
    if kind == spot_module.op_Xor:
        return (_eval_boolean(formula[0], valuation, spot_module)
                != _eval_boolean(formula[1], valuation, spot_module))
    if kind == spot_module.op_Implies:
        return (not _eval_boolean(formula[0], valuation, spot_module)
                or _eval_boolean(formula[1], valuation, spot_module))
    if kind == spot_module.op_Equiv:
        return (_eval_boolean(formula[0], valuation, spot_module)
                == _eval_boolean(formula[1], valuation, spot_module))
    raise RuntimeError(f"non-propositional symmetric monitor body: {formula}")


def _symmetric_signature(formula, buses, spot_module):
    """Return a per-bus count signature, or None if it is not well-defined.

    Adjacent transpositions establish invariance under every permutation of
    each bus.  A signature is emitted only when the truth set is a Cartesian
    product of per-bus count sets; this avoids inventing independent count
    sets for formulas that relate the counts of two buses.
    """
    if formula.kind() != spot_module.op_G or not formula[0].is_boolean():
        return None
    body = formula[0]
    aps = {ap.ap_name() for ap in spot_module.atomic_prop_collect(body)}
    relevant = {
        base: members for base, members in buses.items()
        if any(name in aps for name, _index in members)
    }
    if not relevant:
        return None

    for members in relevant.values():
        for (left, _), (right, _) in zip(members, members[1:]):
            swapped = _replace_aps(
                body,
                {left: spot_module.formula.ap(right),
                 right: spot_module.formula.ap(left)},
                spot_module)
            if not spot_module.are_equivalent(body, swapped):
                return False

    bus_names = {name for members in relevant.values()
                 for name, _index in members}
    for scalar in aps - bus_names:
        when_false = _replace_aps(
            body, {scalar: spot_module.formula.ff()}, spot_module)
        when_true = _replace_aps(
            body, {scalar: spot_module.formula.tt()}, spot_module)
        if not spot_module.are_equivalent(when_false, when_true):
            return False

    ordered = sorted(relevant.items())
    true_counts: set[tuple[int, ...]] = set()
    ranges = [range(len(members) + 1) for _base, members in ordered]
    for counts in itertools.product(*ranges):
        valuation = {name: False for name in aps}
        for (_base, members), count in zip(ordered, counts):
            for name, _index in members[:count]:
                valuation[name] = True
        if _eval_boolean(body, valuation, spot_module):
            true_counts.add(counts)

    allowed = [sorted({counts[pos] for counts in true_counts})
               for pos in range(len(ordered))]
    represented = set(itertools.product(*allowed)) if allowed else {()}
    if represented != true_counts:
        return False
    return {base: counts for (base, _members), counts in zip(ordered, allowed)}


def provenance(monitors: list[Monitor], inputs: list[str], outputs: list[str],
               semantics: str, violated_lit: int | None, spot_module,
               frontend: dict | None = None,
               frontend_error: str | None = None,
               symbols: dict[str, str] | None = None) -> dict:
    if symbols is None:
        try:
            symbols = canonical_signals(inputs, outputs)
        except ValueError:
            # Direct provenance audits can inspect malformed inventories;
            # the game builder itself rejects these before this point.
            symbols = {name: f"uncontrollable_i{index}"
                       for index, name in enumerate(inputs)}
            symbols.update({name: f"controllable_o{index}"
                            for index, name in enumerate(outputs)})
    frontend_signals = {}
    semantic_candidates: list[tuple[object, dict]] = []
    frontend_valid = False
    if frontend is not None:
        signal_names = [item["name"] for item in frontend["signals"]]
        conjunct_keys = [
            (item["source_formula_id"], item["generated_position"])
            for item in frontend["conjuncts"]]
        frontend_valid = (
            frontend.get("schema") == "tlsf-tools.frontend-provenance.v1"
            and frontend.get("ambiguous") is False
            and len(signal_names) == len(set(signal_names))
            and len(conjunct_keys) == len(set(conjunct_keys))
            and all(isinstance(item["generated_position"], int)
                    and item["generated_position"] >= 0
                    for item in frontend["conjuncts"])
            and [item["name"] for item in frontend["signals"]
                 if item["direction"] == "input"] == inputs
            and [item["name"] for item in frontend["signals"]
                 if item["direction"] == "output"] == outputs
        )
        if frontend_valid:
            frontend_signals = {item["name"]: item
                                for item in frontend["signals"]}
            for item in frontend["conjuncts"]:
                parsed = tlsf_formula(
                    parse_canonical_ltl(item["formula"], symbols, spot_module),
                    symbols, spot_module)
                if item["block"] in ("REQUIRE", "ASSERT"):
                    parsed = spot_module.formula.G(parsed)
                semantic_candidates.append((parsed, item))

    def signal_record(name: str) -> dict:
        base, indices = split_signal_index(name)
        record = {"name": name, "base_name": base, "index_tuple": indices,
                  "provenance_source": "suffix-heuristic"}
        record["game_symbol"] = symbols[name]
        if frontend_valid:
            record.update(frontend_signals[name])
            record["base_name"] = record["source_name"]
            record["provenance_source"] = "frontend"
        return record

    buses = (_frontend_bus_inventory(frontend["signals"])
             if frontend_valid else _bus_inventory([*inputs, *outputs]))
    monitor_records = []
    for index, monitor in enumerate(monitors):
        text = canonical_formula_text(monitor.formula, spot_module)
        template, indices = index_template(text)
        if frontend_valid:
            template = _structural_template(
                monitor.formula, frontend_signals, spot_module)
        support, arity_kind = _monitor_support(
            monitor.formula, buses, spot_module)
        record = {
            "monitor": index,
            "side": monitor.side,
            "mp_class": monitor.mp_class,
            "conjunct": text,
            "template": template,
            "template_source": ("frontend" if frontend_valid
                                else "suffix-heuristic"),
            "index_tuple": indices,
            "support": support,
            "arity_kind": arity_kind,
            "state_count": monitor.automaton.num_states(),
            "latch_literals": monitor.latch_literals,
            "role": monitor.role,
            "source_origin": None,
            "provenance_source": "suffix-heuristic",
        }
        if frontend_valid:
            candidates = []
            for candidate, item in semantic_candidates:
                if (str(candidate) == text or spot_module.are_equivalent(
                        candidate, monitor.formula)):
                    candidates.append(item)
                    if len(candidates) > 1:
                        break
            if len(candidates) == 1:
                origin = candidates[0]
                bindings = origin["bindings"]
                record["source_origin"] = {
                    "block": origin["block"],
                    "source_formula_id": origin["source_formula_id"],
                    "source_node_id": origin["source_node_id"],
                    "generated_position": origin["generated_position"],
                    "bindings": bindings,
                    "index_tuple": [binding["value"] for binding in bindings],
                    "signals": origin["signals"],
                }
                record["index_tuple"] = record["source_origin"]["index_tuple"]
                record["provenance_source"] = "frontend"
        if (arity_kind == "bus_wide"
                and monitor.formula.kind() == spot_module.op_G
                and monitor.formula[0].is_boolean()):
            signature = _symmetric_signature(
                monitor.formula, buses, spot_module)
            record["symmetric"] = isinstance(signature, dict)
            if isinstance(signature, dict):
                record["symmetric_signature"] = signature
        monitor_records.append(record)
    available = frontend_valid and all(
        item["provenance_source"] == "frontend" for item in monitor_records)
    if available:
        reason = None
    elif frontend_error:
        reason = frontend_error
    elif frontend is None:
        reason = "frontend provenance was not requested"
    elif not frontend_valid:
        reason = "frontend provenance is ambiguous or signal inventory differs"
    else:
        reason = "expanded monitor has no unique source conjunct"
    return {
        "schema": "tlsf-tools.gr1-monitor-game.provenance.v3",
        "provenance_source": ("frontend" if available
                              else "suffix-heuristic"),
        "semantics": semantics,
        "latch_encoding": "one-hot",
        "inputs": [signal_record(name) for name in inputs],
        "outputs": [signal_record(name) for name in outputs],
        "source_parameters": (frontend["parameters"]
                              if frontend_valid else []),
        "source_conjuncts": (frontend["conjuncts"]
                             if frontend_valid else []),
        "monitors": monitor_records,
        "violated_latch_literal": violated_lit,
        "source_origin_metadata": {
            "available": available,
            "provenance_source": ("frontend" if available
                                  else "suffix-heuristic"),
            "reason": reason,
            "source_sha256": (frontend.get("source_sha256")
                              if frontend_valid else None),
        },
    }


def load_frontend_provenance(args, params: list[str], snapshot: pathlib.Path,
                             snapshot_sha256: str) -> dict:
    destination = pathlib.Path(args.provenance_out)
    with tempfile.TemporaryDirectory(dir=destination.parent) as directory:
        path = pathlib.Path(directory) / "frontend.json"
        _run([args.tlsf2tlsf, *params, "--provenance-out", str(path),
              "--output", "/dev/null", str(snapshot)])
        data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("source_sha256") != snapshot_sha256:
        raise RuntimeError("frontend source SHA-256 mismatch")
    return data


def write_symbol_map(output: str, aag: str, inputs: list[str],
                     outputs: list[str], symbols: dict[str, str]) -> None:
    """Write the export map alongside a game, bound to its exact AAG bytes."""
    lines = ["tlsf-tools.game-symbol-map.v1",
             hashlib.sha256(aag.encode("utf-8")).hexdigest()]
    lines += [f"I\t{symbols[name]}\t{name}" for name in inputs]
    lines += [f"O\t{symbols[name]}\t{name}" for name in outputs]
    pathlib.Path(output + ".symbols").write_text(
        "\n".join(lines) + "\n", encoding="utf-8")


def _run(command: list[str], *, input_text: str | None = None) -> str:
    proc = subprocess.run(command, input=input_text, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=False)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise RuntimeError(
            f"command failed with exit {proc.returncode}: {' '.join(command)}")
    return proc.stdout.strip()


def _tool_info(tool: str, selection: str, basic_tlsf: str) -> str:
    return _run([tool, selection], input_text=basic_tlsf)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build a per-conjunct deterministic-Buchi GR(1) AIGER game.",
        epilog=(
            "Exact mode preserves the lowered TLSF implication.  Strict mode "
            "is REAL-sound only: strict REALIZABLE implies the plain objective "
            "is realizable, but strict UNREALIZABLE is not a sound UNREAL claim."))
    parser.add_argument("tlsf", help="expanded TLSF instance")
    parser.add_argument("--param", action="append", default=[], metavar="NAME=VALUE",
                        help="parameter override passed through (repeatable)")
    parser.add_argument("--semantics", choices=("strict", "exact"),
                        default="exact", help="game reduction semantics")
    parser.add_argument("--output", help="write AAG to FILE instead of stdout")
    parser.add_argument("--provenance-out", metavar="FILE",
                        help="write deterministic monitor/signal provenance JSON")
    parser.add_argument("--tlsf2ltl", default=default_tool("tlsf2ltl"))
    parser.add_argument("--tlsf2tlsf", default=default_tool("tlsf2tlsf"))
    parser.add_argument("--tlsfinfo", default=default_tool("tlsfinfo"))
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        import spot
    except ImportError as exc:
        sys.stderr.write(f"gr1-monitor-game: Spot Python bindings required: {exc}\n")
        return 2

    try:
        source_bytes = pathlib.Path(args.tlsf).read_bytes()
    except OSError as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return 2
    snapshot_sha256 = hashlib.sha256(source_bytes).hexdigest()
    destination = pathlib.Path(args.provenance_out or args.output or ".")
    snapshot_parent = destination.parent if destination.name != "." else destination
    with tempfile.TemporaryDirectory(dir=snapshot_parent) as directory:
        snapshot = pathlib.Path(directory) / "source.tlsf"
        snapshot.write_bytes(source_bytes)
        return _build_snapshot(args, spot, snapshot, snapshot_sha256)


def _build_snapshot(args, spot, snapshot: pathlib.Path,
                    snapshot_sha256: str) -> int:
    params = [item for value in args.param for item in ("--param", value)]
    try:
        basic = _run([args.tlsf2tlsf, "--basic", *params, str(snapshot)])
        source_semantics = _tool_info(args.tlsfinfo, "--semantics", basic)
        target = _tool_info(args.tlsfinfo, "--target", basic)
        inputs_text = _tool_info(args.tlsfinfo, "--expanded-ins", basic)
        outputs_text = _tool_info(args.tlsfinfo, "--expanded-outs", basic)
        lowered = _run(
            [args.tlsf2ltl, "--format", "ltl", *params, str(snapshot)])
    except (OSError, RuntimeError) as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return 2

    if source_semantics.lower() != "mealy" or target.lower() != "mealy":
        sys.stderr.write(
            "gr1-monitor-game: unsupported non-Mealy SEMANTICS/TARGET: "
            f"{source_semantics}/{target}\n")
        return EXIT_UNSUPPORTED
    if args.semantics == "strict":
        sys.stderr.write(
            "gr1-monitor-game: warning: strict mode is REAL-sound only; a "
            "strict UNREALIZABLE result is not a sound UNREAL claim for the "
            "plain implication\n")

    inputs = [name for name in inputs_text.split(",") if name]
    outputs = [name for name in outputs_text.split(",") if name]
    try:
        symbols = canonical_signals(inputs, outputs)
        formula = parse_canonical_ltl(lowered, symbols, spot)
    except ValueError as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return EXIT_UNSUPPORTED
    except RuntimeError as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return 2
    assume, guarantee = split_objective(formula, spot)
    monitors: list[Monitor] = []
    try:
        for side, formulas in (("assumption", assume),
                               ("guarantee", guarantee)):
            for conjunct in formulas:
                monitors.append(build_monitor(conjunct, side, spot))
    except ValueError as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return EXIT_UNSUPPORTED
    except RuntimeError as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return 2

    try:
        aag, _builder, violated = encode_game(
            monitors, inputs, outputs, args.semantics, spot, symbols)
    except ValueError as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return EXIT_UNSUPPORTED
    except RuntimeError as exc:
        sys.stderr.write(f"gr1-monitor-game: {exc}\n")
        return 2


    if args.output:
        pathlib.Path(args.output).write_text(aag, encoding="utf-8")
        write_symbol_map(args.output, aag, inputs, outputs, symbols)
    else:
        sys.stdout.write(aag)
    if args.provenance_out:
        frontend = None
        frontend_error = None
        try:
            frontend = load_frontend_provenance(
                args, params, snapshot, snapshot_sha256)
        except (OSError, RuntimeError, ValueError, KeyError) as exc:
            frontend_error = f"frontend provenance unavailable: {exc}"
        data = provenance(
            [dataclasses.replace(monitor, formula=tlsf_formula(
                monitor.formula, symbols, spot)) for monitor in monitors],
            inputs, outputs, args.semantics, violated, spot,
            frontend, frontend_error, symbols)
        pathlib.Path(args.provenance_out).write_text(
            json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
