"""Exercise every EnvSat guard against frozen exports and reference verdicts."""
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

from golden import Golden

convert, residual, compose = sys.argv[1:]
gold = Golden("assumption-pruning")


def source(sections, semantics="Mealy", target="Mealy"):
    return (f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} MAIN {{ "
            "INPUTS { q; r; s; t; } OUTPUTS { p; } " + sections + " }")


def output(tool, text):
    emitted = subprocess.check_output([tool], input=text, text=True, timeout=10)
    gold.check(Path(tool).name, [text, emitted])
    return emitted


def cluster(tool, text):
    emitted = output(tool, text)
    formulas = [line for line in emitted.splitlines()
                if not line.startswith(("c ", "ctl "))]
    assert len(formulas) == 1, emitted
    interface = re.search(r"^c cluster 0 outs=(\S*) ins=(\S*)$", emitted, re.M)
    assert interface, emitted
    return emitted, formulas[0], interface.group(2), interface.group(1)


def verdict(formula, inputs, outputs):
    return gold.verdict(formula, inputs, outputs)


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
gold.finish()

# Frozen before the ResidualPlan migration: true occupies a cluster, definitions
# and accepted reaction controllers disappear, and --single retains assumptions.
core = "G (p <-> X r) && G (u <-> X s)"
reaction = " && G (q -> X w)"
definition = " && G (v <-> t)"
for semantics, target, counts, clusters, outs, ins, formula in (
        ("Mealy", "Mealy", (4, 33, 2),
         [("", "", "true"), ("p", "r", "G (p <-> X r)"),
          ("u", "s", "G (u <-> X s)")],
         "p,u", "q,r,s", "G F q -> true && " + core),
        ("Mealy,Strict", "Mealy", (4, 33, 2),
         [("", "", "true"), ("p", "r", "G (p <-> X r)"),
          ("u", "s", "G (u <-> X s)")],
         "p,u", "q,r,s", "G F q -> true && " + core),
        ("Mealy,Finite", "Mealy", (5, 17, 1),
         [("p,u,w", "q,r,s", "G F q -> true && " + core + reaction)],
         "p,u,w", "q,r,s", "G F q -> true && " + core + reaction),
        ("Moore", "Moore", (5, 17, 1),
         [("", "q", "G F q -> true"),
          ("p", "q,r", "G F q -> G (p <-> X r)"),
          ("u", "q,s", "G F q -> G (u <-> X s)"),
          ("v", "q,t", "G F q -> G (v <-> t)")],
         "p,u,v", "q,r,s,t", "G F q -> true && " + core + definition),
        ("Moore,Finite", "Moore", (6, 0, 0),
         [("p,u,v,w", "q,r,s,t",
           "G F q -> true && " + core + definition + reaction)],
         "p,u,v,w", "q,r,s,t", "G F q -> true && " + core + definition + reaction)):
    text = (f"INFO {{ SEMANTICS: {semantics} TARGET: {target} }} MAIN {{ "
            "INPUTS { q; r; s; t; } OUTPUTS { p; u; v; w; } "
            "ASSUMPTIONS { G F q; } GUARANTEES { true; G(p <-> X r); "
            "G(u <-> X s); G(v <-> t); G(q -> X w); } }")
    remaining, eliminated, owned = counts
    banner = (f"c composition: residual={remaining}/6 constraints "
              f"({eliminated}% eliminated), outputs owned={owned}, conflicts=0\n")

    def run_residual(*options):
        result = subprocess.run([residual, *options], input=text, text=True,
                                capture_output=True, timeout=10)
        assert result.returncode == 0 and not result.stderr, result
        return result.stdout

    expected = banner + f"c clusters {len(clusters)}\n"
    for k, (outputs, inputs, ltl) in enumerate(clusters):
        expected += f"c cluster {k} outs={outputs} ins={inputs}\n{ltl}\n"
    assert run_residual() == expected, semantics
    assert run_residual("--single") == (
        banner + f"c outs={outs}\nc ins={ins}\n{formula}\n"), semantics
    with TemporaryDirectory() as directory:
        expected = banner + f"c clusters {len(clusters)}\n"
        artifacts = {}
        for k, (outputs, inputs, ltl) in enumerate(clusters):
            name = f"residual.{k}.ltl"
            artifacts[name] = f"c outs={outputs}\nc ins={inputs}\n{ltl}\n"
            expected += f"c cluster {k} file={name} outs={outputs} ins={inputs}\n"
        assert run_residual("--output-dir", directory) == expected, semantics
        assert {p.name: p.read_text() for p in Path(directory).iterdir()} == artifacts
    print(f"ResidualPlan {semantics}: exact residuals, interfaces and filenames")

# This spelling must survive: tlsfresidual has never requested weak rewrites.
text = source("GUARANTEES { p R false; }")
assert run_residual() == (
    "c composition: residual=1/1 constraints (0% eliminated), "
    "outputs owned=0, conflicts=0\nc clusters 1\nc cluster 0 outs=p ins=\np R false\n")

# Empty and fully discharged plans still export no files and a single true.
for sections in ("", "GUARANTEES { G(q -> X p); }"):
    text = source(sections)
    assert run_residual() == "c composition: fully-solved\nc clusters 0\n"
    assert run_residual("--single") == (
        "c composition: fully-solved\nc outs=\nc ins=\ntrue\n")
    with TemporaryDirectory() as directory:
        assert run_residual("--output-dir", directory) == run_residual()
        assert not list(Path(directory).iterdir())
