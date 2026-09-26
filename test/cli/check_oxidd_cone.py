#!/usr/bin/env python3
"""Small structural regression for the offline OxiDD cone analyzer."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))

import analyze_oxidd_cone as cone


def main():
    game = cone.parse_aag(Path(__file__).parents[1] / "fixtures" / "cases" / "solve_real.aag")
    classes = cone.support_classes(game)
    roots = [game["outputs"][0]]
    by_variable, relevant, uses, root_uses, fanouts = cone.relevant_graph(
        game, roots)
    assert relevant == {0}
    assert classes[3] == "primary-input-only"
    assert uses[3] == 1 and root_uses[3] == 1 and fanouts[3] == []
    plan = cone.grouping(0, game, by_variable, classes, uses, root_uses)
    assert plan["absorbed_gate_indices"] == []
    assert [factor["literal"] for factor in plan["stable_factors"]] == [2, 5]
    assert all(factor["barrier"] == "leaf" for factor in plan["stable_factors"])


if __name__ == "__main__":
    main()
