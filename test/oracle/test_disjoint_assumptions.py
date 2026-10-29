"""Disjoint, jointly inconsistent assumptions must survive residual extraction."""
import subprocess
import sys

import spot

convert, residual, compose, fixture = sys.argv[1:]


def output(tool, *options):
    return subprocess.check_output([tool, *options, fixture], text=True)


original = spot.formula(output(convert))
assert spot.are_equivalent(original, spot.formula("1"))
# The former, assumption-free cluster denotes false.
assert spot.are_equivalent(spot.formula("G F p & F G !p"), spot.formula("0"))
for tool in (residual, compose):
    text = output(tool)
    assert "c cluster 0 outs=p ins=q\n" in text, text
    formulas = [line for line in text.splitlines() if not line.startswith("c ")]
    assert len(formulas) == 1, text
    assert "G F q" in formulas[0] and "F G !q" in formulas[0], text
    assert spot.are_equivalent(original, spot.formula(formulas[0])), text
