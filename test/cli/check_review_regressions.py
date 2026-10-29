"""Keep the reviewed coupled game and finite weak-next objective intact."""
import csv
import subprocess
import sys

convert, residual, compose, normalize, definition, finite = sys.argv[1:]


def output(tool, *args, source=None):
    result = subprocess.run([tool, *args], input=source, text=True,
                            capture_output=True, check=True)
    return result.stdout.strip()


# The original is realizable: p=false falsifies G p. Eliminating p=q used to
# yield G q -> false, which the environment refutes by choosing q=true.
original = output(convert, definition)
for tool in (residual, compose):
    text = output(tool, definition)
    assert "c cluster 0 outs=p ins=q" in text, text
    formulas = [line for line in text.splitlines() if not line.startswith("c ")]
    assert formulas == [original], text

# Weak next false holds precisely at the last position of a nonempty word.
for flags in ([], ["--weak-simplify"], ["--strong-simplify"]):
    assert output(convert, *flags, finite) == "X false"
text = output(compose, finite)
assert [line for line in text.splitlines() if not line.startswith("c ")] == ["X false"], text
for flags in (["--pre-passes", "pre-weak"], ["--passes", "weak"],
              ["--passes", "nnf"]):
    normalized = output(normalize, *flags, finite)
    assert output(convert, source=normalized) == "X false", normalized

# Infinite words always have a successor: X false folds, exposing safety.
source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { OUTPUTS { p; } "
          "GUARANTEES { X false || G(p <-> X p); } }")
assert output(convert, "--weak-simplify", source=source) == "G (p <-> X p)"
for flags in (["--pre-passes", "pre-weak"], ["--passes", "weak"]):
    normalized = output(normalize, *flags, source=source)
    assert output(convert, source=normalized) == "G (p <-> X p)", normalized
route, = csv.DictReader(output(compose, "--route-stats", source=source).splitlines(),
                        delimiter="\t")
assert (route["gr_level"], route["route"], route["backend"], route["uses_oxidd"]) == (
    "0", "direct-safety", "OxiDD", "1"), route

# NNF output must also reparse in its original semantics. On finite words,
# negating next swaps weak and strong; infinite TLSF must keep ordinary X.
for semantics in ("Mealy", "Mealy,Finite"):
    for operator in (["X", "X[!]"] if "Finite" in semantics else ["X"]):
        source = (f"INFO {{ SEMANTICS: {semantics} TARGET: Mealy }} "
                  f"MAIN {{ OUTPUTS {{ p; }} GUARANTEES {{ ! {operator} p; }} }}")
        normalized = output(normalize, "--passes", "nnf", source=source)
        text = output(convert, source=normalized)
        expected = "X[!] !p" if semantics == "Mealy,Finite" and operator == "X" else "X !p"
        assert text == expected, (semantics, operator, normalized, text)
