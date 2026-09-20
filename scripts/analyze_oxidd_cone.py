#!/usr/bin/env python3
"""Analyze a legacy-safety AAG cone and conservative conjunction fusion."""

import argparse
import collections
import hashlib
import json
from pathlib import Path


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_aag(path):
    lines = path.read_text().splitlines()
    header = lines[0].split()
    if not header or header[0] != "aag" or len(header) not in (6, 10):
        raise ValueError("expected an ASCII AIGER 1.0/1.9 file")
    values = [int(value) for value in header[1:]] + [0] * (9 - len(header[1:]))
    maximum, ni, nl, no, na, nb, nc, nj, nf = values
    cursor = 1
    inputs = [int(lines[cursor + i].split()[0]) for i in range(ni)]
    cursor += ni
    latches = [list(map(int, lines[cursor + i].split())) for i in range(nl)]
    cursor += nl
    outputs = [int(lines[cursor + i].split()[0]) for i in range(no)]
    cursor += no
    bad = [int(lines[cursor + i].split()[0]) for i in range(nb)]
    cursor += nb + nc
    justice_sizes = [int(lines[cursor + i].split()[0]) for i in range(nj)]
    cursor += nj + nf + sum(justice_sizes)
    gates = [tuple(map(int, lines[cursor + i].split())) for i in range(na)]
    if any(len(gate) != 3 for gate in gates):
        raise ValueError("malformed AAG AND section")
    return {
        "header": {"M": maximum, "I": ni, "L": nl, "O": no, "A": na,
                   "B": nb, "C": nc, "J": nj, "F": nf},
        "inputs": inputs,
        "latches": latches,
        "outputs": outputs,
        "bad": bad,
        "gates": gates,
    }


def support_classes(aag):
    classes = {0: "constant"}
    for literal in aag["inputs"]:
        classes[literal // 2] = "primary-input-only"
    for latch in aag["latches"]:
        classes[latch[0] // 2] = "state-only"
    for lhs, left, right in aag["gates"]:
        operands = {classes[left // 2], classes[right // 2]} - {"constant"}
        classes[lhs // 2] = (next(iter(operands)) if len(operands) == 1
                             else "constant" if not operands else "mixed")
    return classes


def relevant_graph(aag, roots):
    by_variable = {lhs // 2: index for index, (lhs, _, _) in enumerate(aag["gates"])}
    relevant = set()
    stack = list(roots)
    while stack:
        literal = stack.pop()
        gate_index = by_variable.get(literal // 2)
        if gate_index is None or gate_index in relevant:
            continue
        relevant.add(gate_index)
        _, left, right = aag["gates"][gate_index]
        stack.extend((right, left))
    uses = collections.Counter(literal // 2 for literal in roots if literal > 1)
    root_uses = collections.Counter(literal // 2 for literal in roots if literal > 1)
    fanouts = collections.defaultdict(list)
    for index in sorted(relevant):
        _, left, right = aag["gates"][index]
        for position, literal in (("left", left), ("right", right)):
            if literal > 1:
                uses[literal // 2] += 1
                fanouts[literal // 2].append({
                    "consumer_gate_index": index,
                    "position": position,
                    "literal": literal,
                    "polarity": "negative" if literal & 1 else "positive",
                })
    return by_variable, relevant, uses, root_uses, fanouts


def barrier(literal, parent_class, by_variable, classes, uses, root_uses):
    variable = literal // 2
    if variable not in by_variable:
        return "leaf"
    if literal & 1:
        return "negative_edge"
    if root_uses[variable]:
        return "root"
    if uses[variable] != 1:
        return "shared"
    if parent_class == "mixed" and classes[variable] == "primary-input-only":
        return "input_only_barrier"
    return None


def grouping(target_index, aag, by_variable, classes, uses, root_uses):
    factors = []
    absorbed = []

    def visit(literal, parent_class):
        reason = barrier(literal, parent_class, by_variable, classes, uses,
                         root_uses)
        if reason is not None:
            factors.append({"literal": literal, "support": classes[literal // 2],
                            "barrier": reason})
            return
        index = by_variable[literal // 2]
        absorbed.append(index)
        _, left, right = aag["gates"][index]
        node_class = classes[literal // 2]
        visit(left, node_class)
        visit(right, node_class)

    lhs, left, right = aag["gates"][target_index]
    parent_class = classes[lhs // 2]
    visit(left, parent_class)
    visit(right, parent_class)
    return {"absorbed_gate_indices": absorbed, "stable_factors": factors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--gate-index", type=int)
    target.add_argument("--lhs", type=int, help="positive AIG literal")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    aag = parse_aag(args.input)
    if aag["header"]["O"] != 1 or any(aag["header"][key]
                                      for key in ("B", "C", "J", "F")):
        parser.error("analysis currently requires a legacy-safety AAG")
    roots = [aag["outputs"][0]] + [latch[1] for latch in aag["latches"]]
    classes = support_classes(aag)
    by_variable, relevant, uses, root_uses, fanouts = relevant_graph(aag, roots)
    if args.gate_index is not None:
        target_index = args.gate_index
    else:
        target_index = by_variable.get(args.lhs // 2, -1)
    if target_index < 0 or target_index >= len(aag["gates"]):
        parser.error("target gate is not present")
    lhs, left, right = aag["gates"][target_index]
    target_variable = lhs // 2
    report = {
        "schema": 1,
        "input": str(args.input.resolve()),
        "input_sha256": sha256(args.input),
        "profile": "legacy-safety",
        "header": aag["header"],
        "roots": roots,
        "relevant_gate_count": len(relevant),
        "target": {
            "source_gate_index": target_index,
            "parser_normalized_gate_index": target_index,
            "source_normalized_indices_equal": True,
            "lhs_literal": lhs,
            "left_literal": left,
            "right_literal": right,
            "support": classes[target_variable],
            "relevant": target_index in relevant,
            "root_occurrences": root_uses[target_variable],
            "consumer_occurrences": uses[target_variable] - root_uses[target_variable],
            "fanouts": fanouts[target_variable],
            "children": [
                {"literal": literal, "support": classes[literal // 2],
                 "occurrences": uses[literal // 2],
                 "root_occurrences": root_uses[literal // 2],
                 "fusion_barrier": barrier(literal, classes[target_variable],
                                           by_variable, classes, uses, root_uses)}
                for literal in (left, right)
            ],
            "proposed_conservative_grouping": grouping(
                target_index, aag, by_variable, classes, uses, root_uses),
        },
    }
    text = json.dumps(report, indent=2) + "\n"
    if args.out:
        args.out.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
