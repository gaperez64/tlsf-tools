#!/usr/bin/env python3
"""U0 typed-provenance alignment of environment witnesses across valuations.

test_gr1_environment_replay.py replays hand-built AAG games, where "n" is
only a Python argument. This file takes the declared-parameter path: a TLSF
fixture with a real `PARAMETERS` declaration is reduced through gr1_reduction
by `test/api/gr1_environment_reduce`, which, unlike `native_reduction`,
supplies `TlsfPipelineOptions.source_sha256`. That is what makes the pipeline
capture frontend expansion provenance, so every monitor carries a
`source_origin` (its source conjunct `source_formula_id` and the generator
lane `index_tuple`). Without it every monitor falls back to
`"provenance_source": "suffix-heuristic"` and the test fails.

For n=1, n=2 and an alpha-renamed n=1 and n=2, the test:
  1. compares every monitor, keyed by (source_formula_id, index_tuple),
     against `expected_alignment(n)`: the side, role, Manna-Pnueli class and
     justice or fairness ordinal each monitor must get, derived only from
     the structure `forbidden_tlsf` writes;
  2. links each monitor to the reduced game: the justice or fairness record
     at its ordinal must read only that monitor's latches, and the
     monitor's transitions must read exactly the bus element of its lane
     (identified by the signal's typed direction and index, never by name);
  3. solves (UNREAL is mandatory), replays the certificate and policy
     through tlsfcertcheck, and links each monitor to the witness: the
     certificate's `goal_<j>`/`fair_<k>` must read only that monitor's
     latches, and at fairness mode k the policy's `curr_next_*` update must
     be a nonconstant function of the mapped fairness monitor's state alone
     (inside the certificate's `inv`);
  4. rejects an inverted `goal_<j>`, with `j` taken from the alignment.

Negative controls corrupt the parsed n=2 provenance and require the
intended check to be the one that fails: a sibling swap of justice indices,
of monitor lane labels, or of fairness order is caught by the metadata
comparison; a sibling swap of two output signals' lane labels passes the
metadata comparison and is caught by the lane binding; a sibling swap of
two monitors' latches passes the metadata comparison and is caught by the
game-record link and, separately, by each witness link (certificate goal,
certificate fairness, policy mode).
"""

from __future__ import annotations

import argparse
import copy
import dataclasses
import itertools
import json
import pathlib
import subprocess
import sys
import tempfile


def run(command: list, expected=(0,), timeout: int = 60):
    result = subprocess.run([str(c) for c in command], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            check=False, timeout=timeout)
    if result.returncode not in expected:
        raise AssertionError(
            f"command returned {result.returncode} (expected one of "
            f"{expected}): {' '.join(str(c) for c in command)}\n"
            f"{result.stdout}{result.stderr}")
    return result


class AlignmentMismatch(AssertionError):
    """An alignment failure tagged with the check that found it, so a
    negative control can require the intended check to fire."""

    def __init__(self, check: str, detail: str):
        super().__init__(f"[{check}] {detail}")
        self.check = check


def forbidden_tlsf(n: int, *, param_name: str = "n",
                   trigger_name: str = "trig",
                   grant_name: str = "grant") -> str:
    """n lanes; UNREAL for every n >= 1 at the specification level:

      GUARANTEE = (AND_i GF grant[i]) AND (AND_i G !grant[i])

    is satisfied by no play (GF grant[0] and G !grant[0] contradict), while

      ASSUME = AND_i GF trig[i]

    is satisfiable, so no system strategy realizes ASSUME -> GUARANTEE. An
    exact reduction preserves the lowered implication
    (include/tlsf/gr1_reduction.h), so the reduced game must be UNREAL.
    ASSUME is generator-expanded per lane, like the guarantees, so every
    monitor has a lane."""
    return f"""INFO {{
  TITLE:       "u0-provenance-forbidden"
  DESCRIPTION: "n lanes; justice demands what safety forbids"
  SEMANTICS:   Mealy
  TARGET:      Mealy
}}
GLOBAL {{
  PARAMETERS {{ {param_name} = {n}; }}
}}
MAIN {{
  INPUTS {{ {trigger_name}[0..{param_name}-1]; }}
  OUTPUTS {{ {grant_name}[0..{param_name}-1]; }}
  ASSUME {{
    &&[0 <= i < {param_name}] G F ({trigger_name}[i]);
  }}
  GUARANTEE {{
    &&[0 <= i < {param_name}] G F ({grant_name}[i]);
    &&[0 <= i < {param_name}] G (!{grant_name}[i]);
  }}
}}
"""


def expected_alignment(n: int) -> dict:
    """What each monitor of forbidden_tlsf(n) must be, keyed by
    (source_formula_id, index_tuple).

    source_formula_id is `BLOCK:ordinal`, with the 1-based ordinal of the
    top-level conjunct inside its block (src/lib/provenance.c,
    emit_conjunct). forbidden_tlsf writes one ASSUME conjunct (GF, class R)
    and two GUARANTEE conjuncts (GF, class R; then G, class S), each
    expanded over lanes 0..n-1. Exact semantics makes every assumption a
    fairness record and every guarantee a justice record
    (gr1_reduction.cc, encode), numbered per role in declaration order,
    lanes ascending: the first guarantee gets justice 0..n-1 and the second
    n..2n-1. Assumption monitors read the lane's element of the input bus,
    guarantee monitors the lane's element of the output bus.

    A one-element generator range records no binding (expand_quantifier
    returns its sole term without an AND node, src/lib/expand.c), so at n=1
    the lane key is () while the signal read is still element 0."""
    lanes = [()] if n == 1 else [(i,) for i in range(n)]
    table = {}
    for k, lane in enumerate(lanes):
        element = lane[0] if lane else 0
        table[("ASSUME:1", lane)] = {
            "side": "assumption", "role": "fairness", "mp_class": "R",
            "ordinal": k, "reads": ("inputs", element)}
        table[("GUARANTEE:1", lane)] = {
            "side": "guarantee", "role": "justice", "mp_class": "R",
            "ordinal": k, "reads": ("outputs", element)}
        table[("GUARANTEE:2", lane)] = {
            "side": "guarantee", "role": "justice", "mp_class": "S",
            "ordinal": n + k, "reads": ("outputs", element)}
    return table


def monitor_key(monitor: dict):
    if monitor["provenance_source"] != "frontend":
        raise AssertionError(
            f"monitor {monitor['monitor']} has provenance_source="
            f"{monitor['provenance_source']!r}, not 'frontend'")
    origin = monitor["source_origin"]
    if list(origin["index_tuple"]) != list(monitor["index_tuple"]):
        raise AssertionError(
            f"monitor {monitor['monitor']}: source_origin.index_tuple "
            f"{origin['index_tuple']} differs from index_tuple "
            f"{monitor['index_tuple']}")
    return (origin["source_formula_id"], tuple(monitor["index_tuple"]))


def align_monitors(provenance: dict) -> dict:
    """The observed table, keyed like expected_alignment(). The justice
    ordinal is the reduction's `justice_index`. Provenance has no fairness
    index, so the fairness ordinal is the monitor's rank among fairness
    monitors in `monitors` order, which is the order encode() pushes
    fairness records in; check_game_linkage() verifies it against the game
    rather than trusting it."""
    table = {}
    fairness = 0
    for monitor in provenance["monitors"]:
        key = monitor_key(monitor)
        if key in table:
            raise AssertionError(f"duplicate monitor key {key}")
        entry = {"side": monitor["side"], "role": monitor["role"],
                 "mp_class": monitor["mp_class"],
                 "latches": frozenset(lit // 2
                                      for lit in monitor["latch_literals"])}
        if monitor["role"] == "justice":
            entry["ordinal"] = monitor["justice_index"]
        elif monitor["role"] == "fairness":
            entry["ordinal"] = fairness
            fairness += 1
        else:
            raise AssertionError(f"monitor {key} has role {monitor['role']!r}")
        table[key] = entry
    return table


def typed_fields(table: dict) -> dict:
    return {key: (entry["side"], entry["role"], entry["mp_class"],
                  entry["ordinal"]) for key, entry in table.items()}


def check_metadata(observed: dict, n: int, tag: str) -> int:
    expected = expected_alignment(n)
    if set(observed) != set(expected):
        raise AlignmentMismatch(
            "metadata", f"{tag}: monitor keys {sorted(observed)}, expected "
            f"{sorted(expected)}")
    for key, want in expected.items():
        got = observed[key]
        for field in ("side", "role", "mp_class", "ordinal"):
            if got[field] != want[field]:
                raise AlignmentMismatch(
                    "metadata", f"{tag}: {key} has {field}={got[field]!r}, "
                    f"expected {want[field]!r}")
    return len(expected)


@dataclasses.dataclass
class Circuit:
    """A parsed ASCII AIGER file, enough to evaluate literals and compute
    their structural cone."""
    inputs: list[int]
    latches: list[tuple[int, int]]
    outputs: list[int]
    justice: list[list[int]]
    fairness: list[int]
    gates: dict[int, tuple[int, int]]
    input_names: dict[int, str]
    latch_names: dict[int, str]
    output_names: dict[int, str]

    def output(self, name: str) -> int:
        found = [k for k, value in self.output_names.items() if value == name]
        if len(found) != 1:
            raise AssertionError(f"no unique output named {name!r}")
        return self.outputs[found[0]]

    def input_var(self, name: str) -> int:
        found = [k for k, value in self.input_names.items() if value == name]
        if len(found) != 1:
            raise AssertionError(f"no unique input named {name!r}")
        return self.inputs[found[0]] // 2

    def latch_name(self, var: int) -> str:
        for k, (current, _next) in enumerate(self.latches):
            if current // 2 == var:
                return self.latch_names.get(k, f"l{k}")
        raise AssertionError(f"variable {var} is not a latch")

    def support(self, lit: int) -> frozenset[int]:
        seen, stack, leaves = set(), [lit // 2], set()
        while stack:
            var = stack.pop()
            if var == 0 or var in seen:
                continue
            seen.add(var)
            if var in self.gates:
                stack.extend(rhs // 2 for rhs in self.gates[var])
            else:
                leaves.add(var)
        return frozenset(leaves)

    def value(self, lit: int, assignment: dict[int, bool]) -> bool:
        memo: dict[int, bool] = {}

        def var_value(var: int) -> bool:
            if var == 0:
                return False
            if var not in memo:
                if var in self.gates:
                    left, right = self.gates[var]
                    memo[var] = lit_value(left) and lit_value(right)
                else:
                    memo[var] = assignment[var]
            return memo[var]

        def lit_value(literal: int) -> bool:
            return var_value(literal // 2) != bool(literal & 1)

        return lit_value(lit)


def parse_circuit(text: str) -> Circuit:
    lines = text.splitlines()
    header = [int(word) for word in lines[0].split()[1:]]
    header += [0] * (9 - len(header))
    _maxvar, ni, nl, no, na, nb, nc, nj, nf = header[:9]
    position = 1
    inputs = [int(lines[position + k]) for k in range(ni)]
    position += ni
    latches = []
    for k in range(nl):
        fields = [int(word) for word in lines[position + k].split()]
        latches.append((fields[0], fields[1]))
    position += nl
    outputs = [int(lines[position + k]) for k in range(no)]
    position += no + nb + nc
    sizes = [int(lines[position + k]) for k in range(nj)]
    position += nj
    justice = []
    for size in sizes:
        justice.append([int(lines[position + k]) for k in range(size)])
        position += size
    fairness = [int(lines[position + k]) for k in range(nf)]
    position += nf
    gates = {}
    for k in range(na):
        lhs, left, right = (int(word) for word in lines[position + k].split())
        gates[lhs // 2] = (left, right)
    position += na
    names = {"i": {}, "l": {}, "o": {}}
    for line in lines[position:]:
        if line == "c":
            break
        if line[:1] in names:
            label, name = line.split(maxsplit=1)
            names[line[0]][int(label[1:])] = name
    return Circuit(inputs, latches, outputs, justice, fairness, gates,
                   names["i"], names["l"], names["o"])


def check_game_linkage(observed: dict, n: int, game: Circuit,
                       provenance: dict, tag: str) -> tuple[int, int]:
    """Tie each monitor's claimed ordinal and lane to the reduced game."""
    expected = expected_alignment(n)
    latch_vars = {current // 2 for current, _next in game.latches}
    input_vars = {lit // 2 for lit in game.inputs}
    owned = [var for entry in observed.values() for var in entry["latches"]]
    if len(owned) != len(set(owned)) or set(owned) != latch_vars:
        raise AssertionError(f"{tag}: monitor latches do not partition the "
                             "game's latches")
    next_state = {current // 2: nxt for current, nxt in game.latches}
    records = lanes = 0
    for key, entry in observed.items():
        ordinal = entry["ordinal"]
        if entry["role"] == "justice":
            if ordinal >= len(game.justice) or len(game.justice[ordinal]) != 1:
                raise AlignmentMismatch(
                    "game-record", f"{tag}: {key}: no single-literal justice "
                    f"record {ordinal}")
            literal = game.justice[ordinal][0]
        else:
            if ordinal >= len(game.fairness):
                raise AlignmentMismatch(
                    "game-record", f"{tag}: {key}: no fairness record "
                    f"{ordinal}")
            literal = game.fairness[ordinal]
        support = game.support(literal)
        if not support or not support <= entry["latches"]:
            raise AlignmentMismatch(
                "game-record", f"{tag}: {key}: {entry['role']} record "
                f"{ordinal} reads {sorted(support)}, not only the monitor's "
                f"latches {sorted(entry['latches'])}")
        records += 1

        direction, element = expected[key]["reads"]
        signals = [signal for signal in provenance[direction]
                   if list(signal["index_tuple"]) == [element]]
        if len(signals) != 1:
            raise AssertionError(f"{tag}: no unique {direction} signal with "
                                 f"index_tuple [{element}]")
        signal_var = signals[0]["game_literal"] // 2
        transition = frozenset().union(
            *(game.support(next_state[var]) for var in entry["latches"]))
        if ((transition & input_vars) != {signal_var}
                or not (transition & latch_vars) <= entry["latches"]):
            raise AlignmentMismatch(
                "lane-binding", f"{tag}: {key}: transitions read "
                f"{sorted(transition)}; expected {direction} element "
                f"{element} (variable {signal_var}) and the monitor's own "
                "latches")
        lanes += 1
    return records, lanes


def one_hot_states(observed: dict):
    """Every state with exactly one active latch per monitor."""
    monitors = [sorted(entry["latches"]) for entry in observed.values()]
    for choice in itertools.product(*monitors):
        active = set(choice)
        yield {var: var in active for latches in monitors for var in latches}


def check_witness_linkage(observed: dict, game: Circuit, certificate: Circuit,
                          policy: Circuit, tag: str,
                          modes_only: bool = False) -> tuple[int, int, int]:
    """Tie each monitor to the witness fields at its ordinal. Certificate and
    policy inputs are bound to game latches by the game's latch names, as
    tlsfcertcheck binds them."""
    cert_var = {var: certificate.input_var(game.latch_name(var))
                for entry in observed.values() for var in entry["latches"]}
    policy_var = {var: policy.input_var(game.latch_name(var))
                  for entry in observed.values() for var in entry["latches"]}
    goals = fairs = modes = 0
    if not modes_only:
        for key, entry in observed.items():
            prefix = "goal" if entry["role"] == "justice" else "fair"
            name = f"{prefix}_{entry['ordinal']}"
            support = certificate.support(certificate.output(name))
            mapped = {cert_var[var] for var in entry["latches"]}
            if not support or not support <= mapped:
                raise AlignmentMismatch(
                    f"witness-{prefix}", f"{tag}: {key}: certificate {name} "
                    f"reads {sorted(support)}, not only the monitor's latches "
                    f"{sorted(mapped)}")
            if prefix == "goal":
                goals += 1
            else:
                fairs += 1

    fairness = sorted((entry["ordinal"], key, entry)
                      for key, entry in observed.items()
                      if entry["role"] == "fairness")
    count = len(fairness)
    if count < 2:
        return goals, fairs, modes  # one counter never advances
    inv = certificate.output("inv")
    game_inputs = {certificate.input_var(name)
                   for name in game.input_names.values()}
    if certificate.support(inv) & game_inputs:
        raise AssertionError(f"{tag}: certificate inv reads game inputs")
    counters = [policy.input_var(f"curr_{q}") for q in range(count)]
    updates = [policy.output(f"curr_next_{q}") for q in range(count)]
    states = list(one_hot_states(observed))
    for k, key, entry in fairness:
        encodings = [[q == k for q in range(count)]]
        if k == 0:
            encodings.append([False] * count)  # all-zero also means mode 0
        advanced = (k + 1) % count
        by_monitor_state: dict[tuple, set] = {}
        for encoding in encodings:
            for state in states:
                cert_assignment = {cert_var[var]: value
                                   for var, value in state.items()}
                cert_assignment.update({var: False for var in game_inputs})
                if not certificate.value(inv, cert_assignment):
                    continue
                assignment = {policy_var[var]: value
                              for var, value in state.items()}
                assignment.update(zip(counters, encoding))
                nxt = [policy.value(lit, assignment) for lit in updates]
                if sum(nxt) != 1 or not (nxt[k] or nxt[advanced]):
                    raise AssertionError(
                        f"{tag}: mode {k} update {nxt} is not one-hot at "
                        f"{k} or {advanced}")
                monitor_state = tuple(state[var]
                                      for var in sorted(entry["latches"]))
                by_monitor_state.setdefault(monitor_state, set()).add(
                    nxt[advanced])
        values = set().union(*by_monitor_state.values())
        if (any(len(seen) != 1 for seen in by_monitor_state.values())
                or values != {False, True}):
            raise AlignmentMismatch(
                "witness-mode", f"{tag}: {key}: at mode {k} the policy's "
                f"advance to {advanced} is not a nonconstant function of the "
                f"mapped monitor's state: {by_monitor_state}")
        modes += 1
    return goals, fairs, modes


def reduce_tlsf(reduction: pathlib.Path, root: pathlib.Path, tag: str,
                text: str):
    source = root / f"{tag}.tlsf"
    source.write_text(text, encoding="utf-8")
    prefix = root / tag
    run([reduction, source, "exact", prefix])
    provenance = json.loads((root / f"{tag}.json").read_text())
    metadata = json.loads((root / f"{tag}.metadata.json").read_text())
    if metadata["semantics"] != "exact":
        raise AssertionError(f"{tag}: reduction was not exact")
    origin = provenance.get("source_origin_metadata", {})
    if not origin.get("available"):
        raise AssertionError(f"{tag}: frontend provenance is not available: "
                             f"{origin!r}")
    return prefix.with_suffix(".aag"), provenance


def assert_source_parameter(provenance: dict, name: str, value: int, tag: str):
    matching = [p for p in provenance.get("source_parameters", [])
                if p.get("name") == name]
    if len(matching) != 1 or matching[0].get("value") != value:
        raise AssertionError(f"{tag}: source_parameters does not record "
                             f"{name}={value}: "
                             f"{provenance.get('source_parameters')}")


def solve_and_replay(solver: pathlib.Path, checker: pathlib.Path,
                     root: pathlib.Path, tag: str, game: pathlib.Path):
    policy = root / f"{tag}-policy.aag"
    certificate = root / f"{tag}-cert.aag"
    solved = run([solver, "--semantics", "exact", "--policy", policy,
                  "--certificate", certificate, game], (0, 1))
    if solved.returncode != 1:
        raise AssertionError(f"{tag}: expected UNREAL, solver returned "
                             f"{solved.returncode}:\n{solved.stdout}"
                             f"{solved.stderr}")
    run([checker, "--certificate", certificate, "--method", "certificate",
         game, policy])
    return policy, certificate


def assert_goal_mutation_rejected(checker: pathlib.Path, root: pathlib.Path,
                                  tag: str, game: pathlib.Path,
                                  policy: pathlib.Path,
                                  certificate: pathlib.Path,
                                  justice_index: int):
    """Invert goal_<justice_index>, with the index taken from the alignment,
    and require the certificate/game justice-equality rejection
    (check_environment_certificate_mode in gr1_check.c)."""
    text = certificate.read_text(encoding="utf-8")
    circuit = parse_circuit(text)
    lines = text.splitlines()
    name = f"goal_{justice_index}"
    index = [k for k, value in circuit.output_names.items() if value == name]
    if len(index) != 1:
        raise AssertionError(f"{tag}: certificate has no unique {name}")
    header = [int(word) for word in lines[0].split()[1:]]
    row = 1 + header[1] + header[2] + index[0]
    lines[row] = str(int(lines[row]) ^ 1)
    mutated = root / f"{tag}-mutated-{name}.aag"
    mutated.write_text("\n".join(lines) + "\n", encoding="utf-8")
    pathlib.Path(str(mutated) + ".json").write_text(
        pathlib.Path(str(certificate) + ".json").read_text(encoding="utf-8"),
        encoding="utf-8")
    result = run([checker, "--certificate", mutated, "--method",
                  "certificate", game, policy], (6,))
    for line in ("METHOD certificate CERT_FAILED",
                 "COUNTEREXAMPLE reason=certificate goal differs from game "
                 "justice"):
        if line not in result.stdout:
            raise AssertionError(f"{tag}: expected {line!r} on stdout, got:\n"
                                 f"{result.stdout}")


def expect_mismatch(check: str, function, *args):
    try:
        function(*args)
    except AlignmentMismatch as error:
        if error.check != check:
            raise AssertionError(
                f"negative control caught by {error.check!r}, expected "
                f"{check!r}: {error}") from error
        return
    raise AssertionError(f"negative control: corruption not detected by "
                         f"{check!r}")


def monitor_at(provenance: dict, key: tuple) -> int:
    found = [k for k, monitor in enumerate(provenance["monitors"])
             if monitor_key(monitor) == key]
    if len(found) != 1:
        raise AssertionError(f"no unique monitor {key}")
    return found[0]


def run_negative_controls(provenance: dict, game: Circuit,
                          certificate: Circuit, policy: Circuit) -> int:
    """Corrupt the parsed n=2 provenance and require the intended check to
    fail. Each corruption swaps two siblings of one source formula."""
    justice = (("GUARANTEE:1", (0,)), ("GUARANTEE:1", (1,)))
    fairness = (("ASSUME:1", (0,)), ("ASSUME:1", (1,)))
    controls = 0

    corrupt = copy.deepcopy(provenance)
    a, b = (monitor_at(corrupt, key) for key in justice)
    monitors = corrupt["monitors"]
    monitors[a]["justice_index"], monitors[b]["justice_index"] = (
        monitors[b]["justice_index"], monitors[a]["justice_index"])
    expect_mismatch("metadata", check_metadata, align_monitors(corrupt), 2,
                    "swapped justice_index")
    controls += 1

    corrupt = copy.deepcopy(provenance)
    a, b = (monitor_at(corrupt, key) for key in justice)
    first, second = corrupt["monitors"][a], corrupt["monitors"][b]
    for left, right in ((first, second),
                        (first["source_origin"], second["source_origin"])):
        left["index_tuple"], right["index_tuple"] = (right["index_tuple"],
                                                     left["index_tuple"])
    expect_mismatch("metadata", check_metadata, align_monitors(corrupt), 2,
                    "swapped lane labels")
    controls += 1

    corrupt = copy.deepcopy(provenance)
    a, b = (monitor_at(corrupt, key) for key in fairness)
    monitors = corrupt["monitors"]
    monitors[a], monitors[b] = monitors[b], monitors[a]
    expect_mismatch("metadata", check_metadata, align_monitors(corrupt), 2,
                    "swapped fairness order")
    controls += 1

    # Swapping the lane labels of two output-bus signals leaves every monitor
    # consistent with its game record; only the lane binding can catch it.
    corrupt = copy.deepcopy(provenance)
    signals = [signal for signal in corrupt["outputs"]
               if list(signal["index_tuple"]) in ([0], [1])]
    if len(signals) != 2:
        raise AssertionError("n=2 has no two output-bus elements")
    first, second = signals
    first["index_tuple"], second["index_tuple"] = (second["index_tuple"],
                                                   first["index_tuple"])
    table = align_monitors(corrupt)
    check_metadata(table, 2, "swapped signal lanes")
    expect_mismatch("lane-binding", check_game_linkage, table, 2, game,
                    corrupt, "swapped signal lanes")
    controls += 1

    # Swapping the latches two siblings claim keeps every typed field the
    # metadata comparison sees, so it must pass; the links to the game and
    # to the witness must each catch it on their own. For the fairness
    # pair the policy mode check also runs alone, without the certificate
    # fair_<k> check that would otherwise fire first.
    for pair, witness_checks in (
            (justice, (("witness-goal", False),)),
            (fairness, (("witness-fair", False), ("witness-mode", True)))):
        corrupt = copy.deepcopy(provenance)
        a, b = (monitor_at(corrupt, key) for key in pair)
        monitors = corrupt["monitors"]
        monitors[a]["latch_literals"], monitors[b]["latch_literals"] = (
            monitors[b]["latch_literals"], monitors[a]["latch_literals"])
        table = align_monitors(corrupt)
        check_metadata(table, 2, "swapped latches")
        expect_mismatch("game-record", check_game_linkage, table, 2, game,
                        corrupt, "swapped latches")
        controls += 1
        for check, modes_only in witness_checks:
            expect_mismatch(check, check_witness_linkage, table, game,
                            certificate, policy, "swapped latches", modes_only)
            controls += 1
    return controls


def run_suite(reduction: pathlib.Path, solver: pathlib.Path,
              checker: pathlib.Path) -> dict:
    summary = dict.fromkeys((
        "valuations_reduced", "monitors_matched_expected",
        "game_records_linked", "lanes_bound", "unreal_replays",
        "certificate_goals_linked", "certificate_fairness_linked",
        "policy_modes_linked", "renamed_tables_equal",
        "goal_mutations_rejected", "negative_controls"), 0)
    cases = [(f"n{n}", n, forbidden_tlsf(n), "n") for n in (1, 2)]
    # Rename the parameter and cross ownership-looking names: the input bus
    # sounds like an output and the output bus like an input, and their
    # sort order is the reverse of the plain names'.
    cases += [(f"n{n}-renamed", n,
               forbidden_tlsf(n, param_name="deadlineWindow",
                              trigger_name="grantAcknowledged",
                              grant_name="triggerSensor"), "deadlineWindow")
              for n in (1, 2)]
    tables = {}
    with tempfile.TemporaryDirectory(prefix="tlsf-gr1-provenance-") as directory:
        root = pathlib.Path(directory)
        for tag, n, text, parameter in cases:
            game_path, provenance = reduce_tlsf(reduction, root, tag, text)
            assert_source_parameter(provenance, parameter, n, tag)
            summary["valuations_reduced"] += 1
            observed = align_monitors(provenance)
            summary["monitors_matched_expected"] += check_metadata(
                observed, n, tag)
            game = parse_circuit(game_path.read_text(encoding="utf-8"))
            records, lanes = check_game_linkage(observed, n, game, provenance,
                                                tag)
            summary["game_records_linked"] += records
            summary["lanes_bound"] += lanes

            policy_path, certificate_path = solve_and_replay(
                solver, checker, root, tag, game_path)
            summary["unreal_replays"] += 1
            certificate = parse_circuit(
                certificate_path.read_text(encoding="utf-8"))
            policy = parse_circuit(policy_path.read_text(encoding="utf-8"))
            goals, fairs, modes = check_witness_linkage(
                observed, game, certificate, policy, tag)
            summary["certificate_goals_linked"] += goals
            summary["certificate_fairness_linked"] += fairs
            summary["policy_modes_linked"] += modes

            first = observed[("GUARANTEE:1", (() if n == 1 else (0,)))]
            assert_goal_mutation_rejected(checker, root, tag, game_path,
                                          policy_path, certificate_path,
                                          first["ordinal"])
            summary["goal_mutations_rejected"] += 1

            tables[tag] = typed_fields(observed)
            if tag == "n2":
                summary["negative_controls"] += run_negative_controls(
                    provenance, game, certificate, policy)

        for n in (1, 2):
            if tables[f"n{n}-renamed"] != tables[f"n{n}"]:
                raise AssertionError(
                    f"n={n}: renamed alignment differs:\n"
                    f"{tables[f'n{n}-renamed']}\nvs\n{tables[f'n{n}']}")
            summary["renamed_tables_equal"] += 1
        if {key[0] for key in tables["n1"]} != {key[0] for key in tables["n2"]}:
            raise AssertionError("n=1 and n=2 have different source formulas")

    for key, value in summary.items():
        if value == 0:
            raise AssertionError(f"{key} was never exercised")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reduction", type=pathlib.Path, required=True)
    parser.add_argument("--solver", type=pathlib.Path, required=True)
    parser.add_argument("--checker", type=pathlib.Path, required=True)
    args = parser.parse_args()
    summary = run_suite(args.reduction.resolve(), args.solver.resolve(),
                        args.checker.resolve())
    print(" ".join(f"{key}={value}" for key, value in summary.items()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
