"""Preserve inconsistent assumptions, checked as goldens and a native game."""
import itertools
import subprocess
import sys

from golden import Golden

convert, residual, compose, fixture = sys.argv[1:]
gold = Golden("disjoint-assumptions")


def output(tool):
    return subprocess.check_output([tool, fixture], text=True, timeout=30)


original = output(convert).strip()
assert gold.verdict(original, "q", "p")
assert not gold.verdict("G F p & F G !p", "", "p")
gold.check("original", original)
for tool in (residual, compose):
    text = output(tool)
    assert "c cluster 0 outs=p ins=q\n" in text, text
    formulas = [line for line in text.splitlines() if not line.startswith("c ")]
    assert len(formulas) == 1, text
    assert "G F q" in formulas[0] and "F G !q" in formulas[0], text
    gold.check("residual", text)
    assert gold.verdict(formulas[0], "q", "p")
words = [[list(prefix), list(loop)] for length in range(1, 4)
         for loop in itertools.product(range(4), repeat=length)
         for prefix in [(), (0,), (1,), (2,), (3,)]]
actual = ""
for prefix, loop in words:
    # GF q and FG !q depend only on the repeating part; finite prefixes
    # cannot make these assumptions jointly satisfiable.
    assumption = any(bits & 1 for bits in loop) and all(not bits & 1 for bits in loop)
    guarantee = any(bits & 2 for bits in loop) and all(not bits & 2 for bits in loop)
    actual += "1" if not assumption or guarantee else "0"
gold.language(original, ["q", "p"], words, actual)
gold.finish()
