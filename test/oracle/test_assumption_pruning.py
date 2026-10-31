"""Exercise the EnvSat, locality, game-shape and resource guards on emitted LTL."""
import re
import subprocess
import sys

convert, residual, compose, ltlsynt = sys.argv[1:]


def source(sections, semantics="Mealy", target="Mealy"):
    return (f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} MAIN {{ "
            "INPUTS { q; r; s; t; } OUTPUTS { p; } " + sections + " }")


def output(tool, text):
    return subprocess.check_output([tool], input=text, text=True, timeout=10)


def cluster(tool, text):
    emitted = output(tool, text)
    formulas = [line for line in emitted.splitlines()
                if not line.startswith(("c ", "ctl "))]
    assert len(formulas) == 1, emitted
    interface = re.search(r"^c cluster 0 outs=(\S*) ins=(\S*)$", emitted, re.M)
    assert interface, emitted
    return emitted, formulas[0], interface.group(2), interface.group(1)


def verdict(formula, inputs, outputs):
    result = subprocess.run([ltlsynt, "--realizability", f"--ins={inputs}",
                             f"--outs={outputs}", "-f", formula],
                            text=True, capture_output=True, timeout=10)
    assert result.returncode in (0, 1), result
    expected = "REALIZABLE" if result.returncode == 0 else "UNREALIZABLE"
    assert result.stdout.strip() == expected, result
    return expected == "REALIZABLE"


for semantics in ("Mealy", "Mealy,Strict"):
    text = source("ASSUMPTIONS { G F q; F G !q; } "
                  "GUARANTEES { G F p; F G !p; }", semantics)
    assert verdict(output(convert, text), "q,r,s,t", "p")
    for tool in (residual, compose):
        emitted, formula, inputs, outputs = cluster(tool, text)
        assert "G F q" in formula and "F G !q" in formula, emitted
        assert "q" in inputs.split(","), emitted
        assert verdict(formula, inputs, outputs), emitted
        print(f"#79 {semantics}: {formula} => REALIZABLE (both assumptions kept)")

    # Both a losing and a winning unsolved core: pruning must preserve the game.
    for guarantee, expected in (("G(p <-> X r)", False),
                                ("G(p <-> X p)", True)):
        text = source("ASSUMPTIONS { G F q; } GUARANTEES { " + guarantee + "; }",
                      semantics)
        original = output(convert, text)
        assert verdict(original, "q,r,s,t", "p") == expected
        for tool in (residual, compose):
            emitted, formula, inputs, outputs = cluster(tool, text)
            assert "q" not in inputs.split(","), emitted
            assert not re.search(r"\bq\b", formula), emitted
            assert verdict(formula, inputs, outputs) == expected, emitted
            print(f"{semantics} {tool.rsplit('/', 1)[-1]}: {formula} => "
                  f"{'REALIZABLE' if expected else 'UNREALIZABLE'}")

    core = "GUARANTEES { G(p <-> X r); }"
    text = source("INITIALLY { q; } REQUIRE { q; } ASSUMPTIONS { G F q; }" + core,
                  semantics)
    assert not verdict(output(convert, text), "q,r,s,t", "p")
    for tool in (residual, compose):
        emitted, formula, inputs, outputs = cluster(tool, text)
        assert not re.search(r"\bq\b", formula), emitted
        assert not verdict(formula, inputs, outputs), emitted
    # A transient prefix and a nonconstant loop both need genuine infinite
    # witnesses; constant valuations alone cannot certify these groups.
    for environment in (
            "INITIALLY { q; } REQUIRE { X !q; } ASSUMPTIONS { F !q; }",
            "REQUIRE { q <-> X !q; } ASSUMPTIONS { G F q; G F !q; }"):
        text = source(environment + core, semantics)
        assert not verdict(output(convert, text), "q,r,s,t", "p")
        for tool in (residual, compose):
            emitted, formula, inputs, outputs = cluster(tool, text)
            assert not re.search(r"\bq\b", formula), emitted
            assert not verdict(formula, inputs, outputs), emitted

    # Satisfiable, but no lasso of at most four positions can witness it.
    # UNKNOWN keeps the assumptions and still preserves the game's verdict.
    text = source("ASSUMPTIONS { !q; X !q; X X !q; X X X !q; F q; }" + core,
                  semantics)
    assert not verdict(output(convert, text), "q,r,s,t", "p")
    for tool in (residual, compose):
        emitted, formula, inputs, outputs = cluster(tool, text)
        assert "q" in inputs.split(","), emitted
        assert not verdict(formula, inputs, outputs), emitted

    for environment in (
            "ASSUMPTIONS { G F q; F G !q; }",
            # INITIALLY and G REQUIRE must participate in the *joint* check.
            "INITIALLY { q; } REQUIRE { !q; }",
            "REQUIRE { !q; } ASSUMPTIONS { F q; }"):
        text = source(environment + core, semantics)
        assert verdict(output(convert, text), "q,r,s,t", "p")
        for tool in (residual, compose):
            emitted, formula, inputs, outputs = cluster(tool, text)
            assert "q" in inputs.split(","), emitted

            assert verdict(formula, inputs, outputs), emitted

    # Transitive closure through two environment entries must keep q and s;
    # the unrelated satisfiable t component may be pruned.
    text = source("ASSUMPTIONS { G(r -> q); G(q -> s); G F t; }" + core,
                  semantics)
    for tool in (residual, compose):
        emitted, formula, inputs, outputs = cluster(tool, text)
        assert set(inputs.split(",")) == {"r", "q", "s"}, emitted
        assert not re.search(r"\bt\b", formula), emitted

    # The kept PRESET and strict ASSERT supports are part of the cone too.
    for role in ("PRESET", "ASSERT"):
        text = source(f"{role} {{ p <-> q; }} ASSUMPTIONS {{ G F q; }}" + core,
                      semantics)
        for tool in (residual, compose):
            emitted, _, inputs, _ = cluster(tool, text)
            assert "q" in inputs.split(","), emitted


text = source("REQUIRE { q; } ASSUMPTIONS { G F q; } ASSERT { p; } "
              "GUARANTEES { G(p <-> X p); }", "Mealy,Strict")
assert verdict(output(convert, text), "q,r,s,t", "p")
for tool in (residual, compose):
    emitted, formula, inputs, outputs = cluster(tool, text)
    assert "q" not in inputs.split(","), emitted
    assert verdict(formula, inputs, outputs), emitted
    print(f"strict REQUIRE pruning: {formula} => REALIZABLE")

# Finite games and Moore move order are outside prune_realizable's scope.
for semantics, target in (("Mealy,Finite", "Mealy"),
                          ("Moore,Finite", "Moore"),
                          ("Moore", "Moore"), ("Mealy", "Moore")):
    text = source("ASSUMPTIONS { G F q; } GUARANTEES { G(p <-> X r); }",
                  semantics, target)
    for tool in (residual, compose):
        emitted, formula, inputs, _ = cluster(tool, text)
        assert "q" in inputs.split(","), emitted
        assert "q" in formula, emitted
        print(f"{semantics}/{target}: retained G F q")

# Exceed the syntax budget with a satisfiable D: uncertainty must retain it.
text = source("ASSUMPTIONS { " + "X " * 130 + "q; } "
              "GUARANTEES { G(p <-> X r); }")
for tool in (residual, compose):
    emitted, _, inputs, _ = cluster(tool, text)
    assert "q" in inputs.split(","), emitted
print("EnvSat inconsistent / syntax budget: retained D")
