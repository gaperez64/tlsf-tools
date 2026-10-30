"""Check conservative elimination, section, finite-next, and target guards."""
import csv
import io
from pathlib import Path
import re
import subprocess
import sys
import tempfile

convert, residual, compose, templates, benchgraph, phase_b_probe, cases, name = sys.argv[1:]


def output(tool, *args, source=None):
    return subprocess.check_output([tool, *args], input=source, text=True,
                                   timeout=10).strip()


def formulas(text):
    return [line for line in text.splitlines()
            if not line.startswith(("c ", "ctl "))]


if name == "finite-adaptation-doc":
    readme = (Path(cases).parents[2] / "README.md").read_text()
    paragraph = " ".join(readme.split("- **Mealy/Moore**", 1)[1].split("\n\n", 1)[0].split())
    assert "for infinite words" in paragraph, paragraph
    assert "Under finite-word semantics, target adaptation is unsupported" in paragraph, paragraph
    assert "`SEMANTICS` and `TARGET` must agree" in paragraph, paragraph
    assert "`tlsf_convert` refuses all finite semantics" in paragraph, paragraph
elif name == "implicit-input-adaptation":
    # All six section roles, both adaptation directions, strict semantics and
    # overrides must give implicit inputs exactly the declared-input timing.
    roles = ("INITIALLY", "REQUIRE", "ASSUMPTIONS", "PRESET", "ASSERT", "GUARANTEES")
    for semantics, target, expected in (("Moore", "Mealy", "p <-> X u"),
                                        ("Mealy", "Moore", "X p <-> u")):
        for strict in ("", ",Strict"):
            for role in roles:
                base = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                        "%s OUTPUTS { p; } " + role + " { G(p <-> u); } }")
                args = ("--overwrite-semantics", semantics + strict,
                        "--overwrite-target", target)
                declared = base % "INPUTS { u; }"
                implicit = base % ""
                for tool in (convert, residual, compose, templates):
                    extra = ("--format", "csnf") if tool == templates else ()
                    actual = output(tool, *extra, *args, source=implicit)
                    reference = output(tool, *extra, *args, source=declared)
                    assert actual == reference, (tool, role, actual, reference)
                    if tool == templates or (tool == convert and role in (
                            "PRESET", "ASSERT", "GUARANTEES")):
                        assert expected in actual, actual
    # Input metrics and constraint support also include undeclared atoms.
    with tempfile.NamedTemporaryFile(mode="w", suffix=".tlsf") as fixture:
        fixture.write("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                      "OUTPUTS { p; } GUARANTEES { G(p <-> X u); } }")
        fixture.flush()
        metrics = next(csv.DictReader(io.StringIO(output(benchgraph, fixture.name)), delimiter="\t"))
        assert metrics["inputs"] == "1", metrics
    # Eventual/until monitors require an output-controlled goal. An implicit
    # environment atom must cause the same conservative fallback as a declared
    # input, rather than qualifying as an output-only goal.
    for formula in ("F(p && u)", "p U (p && u)"):
        for declaration in ("", "INPUTS { u; }"):
            source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                      f"{declaration} OUTPUTS {{ p; }} GUARANTEES {{ {formula}; }} }}")
            route = next(csv.DictReader(io.StringIO(output(
                compose, "--route-stats", source=source)), delimiter="\t"))
            assert route["uses_oxidd"] == "0" and route["route"] == "ltlsynt", route
elif name == "phase-b-support":
    # Local certifiers now reject the CLI fixtures before composition. Exercise
    # Phase B independently with locally solved blocks, including a dependency
    # chain in reverse AP order. The probe emits the real substituted residual.
    for chain in ("direct", "chain"):
        text = output(phase_b_probe, chain)
        assert text.splitlines() == [
            "register before Phase B: solved",
            "register after Phase B: rejected",
            "conflict: shared-output r",
            "G (q -> X !r) && G r"], text
elif name == "finite-adaptation":
    for semantics, target, guarantee in (("Mealy", "Moore", "G !p"),
                                         ("Moore", "Mealy", "G q")):
        for overrides in ("header", "target", "semantics", "both"):
            header_semantics = semantics + (",Finite" if overrides in ("header", "target") else "")
            header_target = semantics if overrides in ("target", "both") else target
            source = (f"INFO {{ SEMANTICS: {header_semantics} TARGET: "
                      f"{header_target} }} MAIN {{ "
                      "INPUTS { q; } OUTPUTS { p; } "
                      f"GUARANTEES {{ {guarantee}; }} }}")
            args = ()
            if overrides in ("target", "both"):
                args += ("--overwrite-target", target)
            if overrides in ("semantics", "both"):
                args += ("--overwrite-semantics", semantics + ",Finite")
            for tool in (convert, residual, compose, templates, benchgraph):
                if tool == benchgraph:
                    # The corpus tool takes paths and reports failed rows;
                    # it has no timing overrides or stdin input mode.
                    if overrides != "header":
                        continue
                    with tempfile.NamedTemporaryFile(mode="w", suffix=".tlsf") as fixture:
                        fixture.write(source)
                        fixture.flush()
                        result = subprocess.run([tool, fixture.name], text=True,
                                                capture_output=True, timeout=10)
                    row = next(csv.DictReader(io.StringIO(result.stdout), delimiter="\t"))
                    assert row["parse_status"] == "fail", result.stdout
                else:
                    result = subprocess.run([tool, *args], input=source, text=True,
                                            capture_output=True, timeout=10)
                    assert result.returncode != 0, (tool, result.stdout)
                assert "finite semantics/target adaptation is unsupported" in result.stderr, (
                    tool, result.stderr)
                assert "SEMANTICS and TARGET must agree" in result.stderr, result.stderr
                assert "realizable iff" not in result.stdout, result.stdout
elif name == "temporal-guards":
    for semantics in ("Mealy", "Moore", "Mealy,Strict", "Moore,Strict"):
        for guard in ("F q", "G q", "X q", "q U r", "q R r", "q W r"):
            families = {
                "reaction": f"G(({guard}) -> p);",
                "negative-reaction": f"G(({guard}) -> !p);",
                "response": f"G(({guard}) -> F p);",
                "guarded-next-assignment": f"G(({guard}) -> X p);",
                # The opposite r literals establish exclusivity even before
                # the temporal guard check; this must reach that new guard.
                "set-reset-register": f"G((r && ({guard})) -> X p); G((!r && ({guard})) -> X !p);",
                "toggle-register": f"G(({guard}) -> (X p <-> !p));",
                "fixed-delay-response": f"G(({guard}) -> X X p);",
            }
            for family, block in families.items():
                source = (f"INFO {{ SEMANTICS: {semantics} TARGET: "
                          f"{'Moore' if semantics.startswith('Moore') else 'Mealy'} }} "
                          "MAIN { INPUTS { q; r; } OUTPUTS { p; } "
                          f"GUARANTEES {{ {block} }} }}")
                requested = "reaction" if family == "negative-reaction" else family
                text = output(templates, "--certify", "--format", "csnf",
                              "--template", requested, source=source)
                emitted_family = "server" if family == "response" else requested
                assert f"b 0 candidate {emitted_family}" in text, (semantics, guard, text)
                assert "\ncert " not in text, text
                original = output(convert, source=source)
                for tool in (residual, compose):
                    text = output(tool, source=source)
                    assert "ctl " not in text, (family, text)
                    assert formulas(text) == [original], (family, text, original)
    # A purely Boolean reaction can still demand a combinational self-loop.
    # Composition already breaks such cycles; local certification must also
    # decline the impossible assignment p := !p.
    source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
              "OUTPUTS { p; } GUARANTEES { G(!p -> p); } }")
    text = output(templates, "--certify", "--format", "csnf", source=source)
    assert "b 0 candidate reaction" in text, text
    assert "\nasg " not in text, text
    for tool in (residual, compose):
        text = output(tool, source=source)
        assert "ctl " not in text, text
        assert formulas(text) == ["G (!p -> p)"], text
    source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
              "OUTPUTS { p; r; } GUARANTEES { G(r -> F p); } }")
    text = output(templates, "--certify", "--format", "csnf", source=source)
    assert "b 0 candidate server" in text, text
    assert "\nresp " not in text, text
    for tool in (residual, compose):
        text = output(tool, source=source)
        assert formulas(text) == ["G (r -> F p)"], text
elif name == "scheduler-guards":
    for family, obligations in (
            ("round-robin", "G F p; G F r;"),
            ("arbiter", "G(q -> F p); G(q -> F r);")):
        for semantics, outputs, inputs, mutex, extra in (
                ("Mealy,Finite", "p; r;", "q;", "!(p && r)", ""),
                ("Moore,Finite", "p; r;", "q;", "!(p && r)", ""),
                ("Mealy", "p; r; s;", "q;", "!(p && s) && !(r && s)", "G s;"),
                ("Mealy", "p; r;", "q; s;", "!(p && s) && !(r && s)", ""),
                ("Mealy", "p; r;", "q;", "!(p && p) && !(r && r)", "")):
            source = (f"INFO {{ SEMANTICS: {semantics} TARGET: "
                      f"{'Moore' if semantics.startswith('Moore') else 'Mealy'} }} "
                      f"MAIN {{ INPUTS {{ {inputs} }} OUTPUTS {{ {outputs} }} "
                      f"GUARANTEES {{ {obligations} G({mutex}); {extra} }} }}")
            text = output(templates, "--certify", "--format", "csnf",
                          "--template", family, source=source)
            assert f"solved {family}" not in text, text
            original = output(convert, source=source)
            for tool in (residual, compose):
                text = output(tool, *(("--single",) if tool == residual else ()),
                              source=source)
                assert "ctl " not in text, text
                expected = original
                if tool == compose:
                    expected = expected.replace("!(p && p) && !(r && r)", "!p && !r")
                assert formulas(text) == [expected], (family, text, expected)
    # The response matcher records input targets too; certification must not
    # mistake the vacuous output-support check for controllability.
    source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
              "INPUTS { q; s; t; } OUTPUTS { p; } GUARANTEES { "
              "G(q -> F s); G(q -> F t); G !(s && t); } }")
    text = output(templates, "--certify", "--format", "csnf", source=source)
    assert "b 0 candidate arbiter" in text, text
    assert "\narb " not in text, text
    text = output(residual, source=source)
    assert formulas(text) == [output(convert, source=source)], text
    result = subprocess.run([compose], input=source, text=True,
                            capture_output=True, timeout=10)
    assert result.returncode == 1, result
    assert "spec is UNREALIZABLE" in result.stderr, result.stderr
elif name == "implicit-input-invariant":
    for body in ("!u", "!u && p"):
        source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                  f"OUTPUTS {{ p; }} GUARANTEES {{ G({body}); }} }}")
        text = output(templates, "--certify", "--format", "csnf", source=source)
        assert "b 0 candidate safety-invariant" in text, text
        assert "\ncert " not in text, text
        for tool in (residual, compose):
            text = output(tool, source=source)
            assert "ctl " not in text, text
            assert "ins=u" in text, text
            assert formulas(text) == [output(convert, source=source)], text
elif name == "definition-register-use":
    # Phase B must see r through p's committed decoder, including a chain of
    # decoders whose AP order requires more than one substitution pass.
    for definitions, outputs, use in (
            ("G(p <-> r);", "p; r;", "p"),
            ("G(p <-> r); G(s <-> p);", "p; s; r;", "s")):
        source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                  f"INPUTS {{ q; }} OUTPUTS {{ {outputs} }} "
                  f"GUARANTEES {{ {definitions} G(q -> X !r); G {use}; }} }}")
        for tool in (residual, compose):
            text = output(tool, source=source)
            assert "c cluster 0 outs=r ins=q" in text, text
            assert formulas(text) == ["G (q -> X !r) && G r"], text
            assert "ctl r" not in text, text
            if tool == compose:
                assert "ctl p := " in text, text
elif name == "invariant-assumption":
    fixture = str(Path(cases) / (name + ".tlsf"))
    for tool in (residual, compose):
        text = output(tool, fixture)
        assert "ctl " not in text, text
        assert "c cluster 0 outs=p ins=" in text, text
        assert formulas(text) == ["G p -> false"], text
elif name == "nondefinition-sections":
    families = {
        "safety-invariant": "G p;",
        "reaction": "G(q -> p);",
        "reachability": "F p;",
        "persistence": "F G p;",
        "delayed-definition": "G(X p <-> q);",
        "guarded-next-assignment": "G(q -> X p);",
        "set-reset-register": "G(q -> X p); G(!q -> X !p);",
        "toggle-register": "G(q -> (X p <-> !p));",
        "fixed-delay-response": "G(q -> X X p);",
        "global-recurrence-switch": "(G F p <-> G q);",
        "response": "G(q -> F p);",
        "round-robin": "G F p; G F r; G !(p && r);",
        "arbiter": "G(q -> F p); G(q -> F r); G !(p && r);",
    }
    for semantics in ("Mealy", "Mealy,Strict"):
        for family, block in families.items():
            outputs = "p; r;" if family in ("round-robin", "arbiter") else "p;"
            source = (f"INFO {{ SEMANTICS: {semantics} TARGET: Mealy }} "
                      f"MAIN {{ INPUTS {{ q; }} OUTPUTS {{ {outputs} }} "
                      f"GUARANTEES {{ {block} }} }}")
            text = output(templates, "--certify", "--format", "csnf",
                          "--template", family, source=source)
            assert " solved " in text, (semantics, family, text)
            # Assumptions inside the candidate block used to be skipped by
            # output_is_free. The same environment read outside it must also
            # prevent certification, even if another block could consume it.
            for role in ("INITIALLY", "REQUIRE", "ASSUMPTIONS"):
                for sections in (f"{role} {{ {block} }} GUARANTEES {{ F false; }}",
                                 f"{role} {{ G p; }} GUARANTEES {{ {block} }}"):
                    source = (f"INFO {{ SEMANTICS: {semantics} TARGET: Mealy }} "
                              f"MAIN {{ INPUTS {{ q; }} OUTPUTS {{ {outputs} }} "
                              f"{sections} }}")
                    text = output(templates, "--certify", "--format", "csnf",
                                  "--template", family, source=source)
                    assert " solved " not in text, (family, role, text)
                    assert "\ncert " not in text, (family, role, text)
                    for tool in (residual, compose):
                        text = output(tool, source=source)
                        assert "ctl " not in text, (family, role, text)
                        assert re.search(r"\bp\b", "\n".join(formulas(text))), (
                            family, role, text)
            # The free-output guard must count unconditional PRESET and
            # strict ASSERT reads, even for register certifiers that used to
            # defer all ownership checking to composition.
            for role in ("PRESET", "ASSERT"):
                source = (f"INFO {{ SEMANTICS: {semantics} TARGET: Mealy }} "
                          f"MAIN {{ INPUTS {{ q; }} OUTPUTS {{ {outputs} }} "
                          f"{role} {{ F p; }} GUARANTEES {{ {block} }} }}")
                text = output(templates, "--certify", "--format", "csnf",
                              "--template", family, source=source)
                assert " solved " not in text, (semantics, family, role, text)
                for tool in (residual, compose):
                    text = output(tool, source=source)
                    assert "ctl " not in text, (semantics, family, role, text)
                    assert re.search(r"\bp\b", "\n".join(formulas(text))), text
elif name == "finite-registers":
    families = {
        "delayed-definition": "G({next} p <-> false);",
        "set-reset-register": "G(q -> {next} p); G(!q -> {next} !p);",
        "toggle-register": "G(q -> ({next} p <-> !p));",
        "fixed-delay-response": "G(q -> {next} {next} p);",
        "guarded-next-assignment": "G(q -> {next} p);",
    }
    for family, block in families.items():
        for next_op in ("X", "X[!]"):
            source = ("INFO { SEMANTICS: Mealy,Finite TARGET: Mealy } "
                      "MAIN { INPUTS { q; } OUTPUTS { p; } GUARANTEES { "
                      + block.format(next=next_op) + " } }")
            original = output(convert, source=source)
            text = output(templates, "--certify", "--format", "csnf",
                          "--template", family, source=source)
            assert f"b 0 candidate {family}" in text, text
            assert "\ncert " not in text, text
            text = output(residual, "--single", source=source)
            assert "c outs=p" in text, text
            assert formulas(text) == [original], text
            text = output(compose, source=source)
            assert "ctl " not in text, text
            assert "c cluster 0 outs=p ins=" in text, text
            # tlsfcompose simplifies equivalence with false before printing.
            expected = f"G !{next_op} p" if family == "delayed-definition" else original
            assert formulas(text) == [expected], text
elif name == "target-moore-mealy":
    fixture = str(Path(cases) / (name + ".tlsf"))
    for tool in (residual, compose):
        text = output(tool, fixture)
        assert "ctl " not in text, text
        assert formulas(text) == ["G (p <-> X q)"], text
    text = output(templates, "--certify", "--format", "csnf", fixture)
    assert "cl 0 G (p <-> X q)" in text, text
    metrics = next(csv.DictReader(io.StringIO(output(benchgraph, fixture)), delimiter="\t"))
    assert metrics["guard_x"] == "1", metrics
    # Cover all six sections, the inverse adaptation, and CLI overrides.
    # Environment occurrences keep these definitions/registers residual.
    for semantics, target, shifted in (("Moore", "Mealy", "p <-> X q"),
                                       ("Mealy", "Moore", "X p <-> q")):
        source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } "
                  "MAIN { INPUTS { q; } OUTPUTS { p; } "
                  + " ".join(f"{role} {{ G(p <-> q); }}" for role in
                             ("INITIALLY", "REQUIRE", "ASSUMPTIONS", "PRESET",
                              "ASSERT", "GUARANTEES")) + " }")
        args = ("--overwrite-semantics", semantics, "--overwrite-target", target)
        original = output(convert, *args, source=source)
        for tool in (residual, compose):
            text = output(tool, *args, source=source)
            assert "ctl " not in text, text
            assert formulas(text) == [original], text
        text = output(templates, "--certify", "--format", "csnf", *args,
                      source=source)
        assert sum(line.endswith(f"G ({shifted})") for line in text.splitlines()
                   if line.startswith("cl ")) == 6, text
elif name == "sections":
    # Every system section can read a PRESET definition. ASSERT definitions
    # cover GUARANTEES in both objectives; the reverse needs non-strictness.
    ordinary = {"PRESET": {"PRESET", "ASSERT", "GUARANTEES"},
                "ASSERT": {"ASSERT", "GUARANTEES"},
                "GUARANTEES": {"ASSERT", "GUARANTEES"}}
    strict = dict(ordinary, GUARANTEES={"GUARANTEES"})
    roles = ("INITIALLY", "PRESET", "REQUIRE", "ASSERT", "ASSUMPTIONS",
             "GUARANTEES")
    for semantics, admitted in (("Mealy", ordinary), ("Mealy,Strict", strict)):
        for definition in roles:
            for use in roles:
                source = (f"INFO {{ SEMANTICS: {semantics} TARGET: Mealy }} "
                          "MAIN { INPUTS { q; } OUTPUTS { p; } "
                          f"{definition} {{ G(p <-> q); }} "
                          f"{use} {{ F p; }} GUARANTEES {{ F p; }} }}")
                text = output(compose, source=source)
                expected = use in admitted.get(definition, set())
                assert ("ctl p := q" in text) == expected, (
                    semantics, definition, use, text)
                # A rejected decoder must leave p in the emitted game; an
                # admitted one must substitute p in every surviving section.
                assert bool(re.search(r"\bp\b", "\n".join(formulas(text)))) != expected, (
                    semantics, definition, use, text)
else:
    fixture = str(Path(cases) / (name + ".tlsf"))
    original = output(convert, fixture)
    healthy = name in ("definition-guarantee-use", "definition-preset-use")
    for tool in (residual, compose):
        text = output(tool, fixture)
        clusters = [line for line in text.splitlines() if line.startswith("c cluster ")]
        assert len(clusters) == 1, text
        if healthy:
            assert clusters == ["c cluster 0 outs= ins=q"], text
            assert formulas(text) == ["F q"], text
            if tool == compose:
                assert "ctl p := q" in text, text
        else:
            # Retain the original output and defining constraint together.
            outputs = "p,r" if name == "finite-cluster-end" else "p"
            inputs = "" if name == "finite-cluster-end" else "q"
            assert clusters == [f"c cluster 0 outs={outputs} ins={inputs}"], text
            assert "ctl " not in text, text
            assert formulas(text) == [original], text

    if name in ("definition-future", "delayed-definition-future"):
        text = output(templates, "--certify", "--format", "csnf", fixture)
        family = "definition" if name == "definition-future" else "delayed-definition"
        assert f"b 0 candidate {family}" in text, text
        assert "cert 0 " not in text, text
