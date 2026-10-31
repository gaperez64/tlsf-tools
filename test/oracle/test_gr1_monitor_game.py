#!/usr/bin/env python3
"""Golden monitor games, native certificates and explicit controller checks."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import tempfile

from aag import Circuit, verify_controller
from golden import Golden
from test_native_reduction_language import Game, tiny

FIXTURES = Path(__file__).resolve().parents[1] / "fixtures/gr1_monitor_game"


def run(command, expected=0):
    result = subprocess.run(list(map(str, command)), text=True, capture_output=True, timeout=60)
    assert result.returncode == expected, (command, result.stdout, result.stderr)
    return result


def mutate(text, latch=False):
    lines = text.splitlines()
    _m, ni, nl, *_ = map(int, lines[0].split()[1:])
    position = 1 + ni if latch else 1 + ni + nl
    fields = lines[position].split()
    bit = 1 if latch else 0
    fields[bit] = str(int(fields[bit]) ^ 1)
    lines[position] = " ".join(fields)
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--builddir", required=True, type=Path)
    build = parser.parse_args().builddir.resolve()
    gold = Golden("monitor-game")
    reducer = build / "test/api/native_reduction"
    solver, checker = build / "tlsfsolve", build / "tlsfcertcheck"
    rng = random.Random(0x20260924)
    with tempfile.TemporaryDirectory(dir=build) as temp:
        directory = Path(temp)
        objectives = {}

        def reduce(source, label, semantics="exact", status=0):
            print(f"monitor case: {label}", flush=True)
            prefix = directory / label
            result = run([reducer, source, semantics, prefix], status)
            gold.check("reduce", [label, semantics, status])
            if status:
                gold.check("decline", result.stderr)
                return None
            data = json.loads(prefix.with_suffix(".json").read_text())
            text = prefix.with_suffix(".aag").read_text()
            gold.check("provenance", data)
            gold.check("game", text)
            if data["source_origin_metadata"]["available"]:
                assert data["source_origin_metadata"]["source_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
            path = prefix.with_suffix(".aag")
            Path(str(path) + ".symbols").write_text(prefix.with_suffix(".symbols").read_text())
            if semantics == "exact":
                lowered = run([build / "tlsf2ltl", "--format", "ltl", source]).stdout.strip()
                symbols = {row["name"]: row["game_symbol"] for row in data["inputs"] + data["outputs"]}
                formula = re.sub(r"[A-Za-z_@][A-Za-z0-9_@']*",
                                 lambda m: '"' + symbols[m[0]] + '"' if m[0] in symbols else m[0], lowered)
                objectives[str(path)] = (formula, ",".join(row["game_symbol"] for row in data["inputs"]),
                                         ",".join(row["game_symbol"] for row in data["outputs"]))
            return path, data

        def solve(path, data, label):
            policy, cert = directory / (label + "-policy.aag"), directory / (label + "-cert.aag")
            result = subprocess.run([str(solver), "--game-profile=gr1", "--policy", str(policy),
                                     "--certificate", str(cert), str(path)],
                                    text=True, capture_output=True, timeout=60)
            assert result.returncode in (0, 1), result.stderr
            gold.check("solver", [label, result.returncode])
            if str(path) in objectives:
                assert gold.verdict(*objectives[str(path)]) == (result.returncode == 0)
            checked = run([checker, "--method", "certificate", "--certificate", cert, path, policy])
            assert checked.stdout.splitlines()[-1] == "VERIFIED", checked
            if result.returncode == 0:
                controller = directory / (label + "-controller.aag")
                run([checker, "--method", "certificate", "--certificate", cert,
                     "--emit-controller", controller, path, policy])
                if len(data["inputs"]) <= 1 and len(data["outputs"]) <= 1:
                    assert verify_controller(Circuit(path.read_text()), Circuit(controller.read_text()), data) == "VERIFIED"
            return result.returncode

        # Preserve the former cross-size, symmetry and conjunct-splitting corpus.
        for source in sorted(FIXTURES.glob("*.tlsf")):
            path, data = reduce(source, source.stem)
            assert data["schema"].endswith(".v3")
            assert data["provenance_source"] == "frontend"
            assert data["source_origin_metadata"]["available"]
            solve(path, data, source.stem)

        # Preserve the old per-conjunct encoding checks: 80 words for each
        # of the first eight monitors in both representative instances.
        component_count = fallback_count = 0
        for filename in ("arbiter_pb_2_pe_.tlsf", "arbiter_on_inpchange_pb_2_pe_.tlsf"):
            _, inventory = reduce(FIXTURES / filename, "inventory-" + Path(filename).stem)
            names = [row["name"] for row in inventory["inputs"] + inventory["outputs"]]
            for index, monitor in enumerate(inventory["monitors"][:8]):
                label = f"component-{Path(filename).stem}-{index}"
                conjunct = monitor["conjunct"]
                source = directory / (label + ".tlsf")
                source.write_text("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { " +
                                  "; ".join(names) + "; } OUTPUTS { unused_component; } GUARANTEES { " +
                                  conjunct.replace("&", "&&").replace("|", "||") + "; } }")
                path, _ = reduce(source, label)
                metadata = json.loads(path.with_suffix(".metadata.json").read_text())
                fallback_count += metadata["fallback_monitor_count"]
                game = Game(path.read_text())
                words = [([rng.randrange(1 << len(game.inputs)) for _ in range(rng.randrange(5))],
                          [rng.randrange(1 << len(game.inputs)) for _ in range(rng.randrange(1, 6))])
                         for _ in range(80)]
                actual = "".join("1" if game.accepts(prefix, loop) else "0" for prefix, loop in words)
                formula = objectives[str(path)][0]
                gold.language(formula, game.input_names, words, actual)
                component_count += 1
        assert component_count >= 6 and fallback_count >= 1

        mutex = "!((g[0] && g[1]) || (g[0] && g[2]) || (g[1] && g[2]))"
        for label, body, symmetric in (
                ("symmetric-mutex", mutex, True),
                ("scalar-dependent", "s || " + mutex, False),
                ("related-counts", "(g[0] && g[1] && g[2]) <-> (r[0] && r[1])", False)):
            source = directory / (label + ".tlsf")
            source.write_text("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                              "INPUTS { r[2]; s; } OUTPUTS { g[3]; } GUARANTEES { G(" + body + "); } }")
            _, data = reduce(source, label)
            assert any(bool(m.get("symmetric_signature")) for m in data["monitors"]) == symmetric

        source = directory / "split-rule.tlsf"
        source.write_text("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                          "INPUTS { a; b; c; } OUTPUTS { d; e; f; } "
                          "ASSUMPTIONS { a; G(b && c); } GUARANTEES { G(d && (e && f)); } }")
        _, data = reduce(source, "split-rule")
        assert sum(m["side"] == "assumption" for m in data["monitors"]) == 3
        assert sum(m["side"] == "guarantee" for m in data["monitors"]) == 3

        # Independently check the committed controller, two corruptions, and
        # all former invalid ownership/interface examples.
        source = FIXTURES / "arbiter_pb_2_pe_.tlsf"
        path, data = reduce(source, "closed-loop")
        game = Circuit(path.read_text())
        controller = (FIXTURES / "arbiter_n2.aag").read_text()
        assert verify_controller(game, Circuit(controller), data) == "VERIFIED"
        for latch in (False, True):
            assert verify_controller(game, Circuit(mutate(controller, latch)), data) == "REFUTED"
        assert verify_controller(game, Circuit(controller), data, state_cap=1) == "UNKNOWN"
        partition = directory / "partition.tlsf"
        partition.write_text(tiny("i", "o", "true;", "G i; G o;"))
        path, data = reduce(partition, "partition")
        invalid = [
            "aag 0 0 0 2 0\n1\n1\no0 controllable_i\no1 controllable_o\n",
            "aag 1 1 0 2 0\n2\n1\n1\ni0 i\no0 controllable_i\no1 controllable_o\n",
            "aag 1 1 0 0 0\n2\ni0 i\n",
            "aag 1 1 0 1 0\n2\n1\ni0 controllable_i\no0 controllable_o\n",
            "aag 1 1 0 2 0\n2\n1\n1\ni0 i\no0 o\no1 controllable_o\n",
        ]
        for text in invalid:
            assert verify_controller(Circuit(path.read_text()), Circuit(text), data) == "INVALID"

        for label, source_text, status in (
                ("persistence", tiny("i", "o", "true;", "F G o;"), 3),
                ("moore", tiny("i", "o", "true;", "G o;").replace("Mealy", "Moore"), 3),
                ("duplicate", tiny("i", "o", "true;", "G o; G (o && true);"), 0),
                ("numeric-scalar", tiny("i_1", "o", "true;", "G (i_1 -> F o);"), 0),
                ("collision", tiny("a[0..1]; a_0", "o", "true;", "G (a_0 -> o);"), 3)):
            source = directory / (label + ".tlsf")
            source.write_text(source_text)
            reduced = reduce(source, label, status=status)
            if label == "duplicate":
                assert not reduced[1]["source_origin_metadata"]["available"]
                assert all(row["source_origin"] is None for row in reduced[1]["monitors"])
            if label == "numeric-scalar":
                assert reduced[1]["inputs"][0]["index_tuple"] == []
                assert reduced[1]["inputs"][0]["dimensions"] == 0

        source = directory / "exact-vs-strict.tlsf"
        source.write_text(tiny("i", "o", "G F o;", "G i;"))
        for semantics, expected in (("exact", 0), ("strict", 1)):
            path, data = reduce(source, "difference-" + semantics, semantics)
            assert solve(path, data, "difference-" + semantics) == expected
        source.write_text(tiny("i", "o", "true;", "G F o;"))
        path, data = reduce(source, "liveness-only", "strict")
        assert solve(path, data, "liveness-only") == 0

        names = ["@", "a'", "req@i", "val'", "controllable_x", "uncontrollable_x",
                 "monitor_0_state_0", "assumption_safety_violated", "curr_0", "_", "_0",
                 "controllable_", "uncontrollable_", "x", "y"]
        guarantees = ["G ({i} -> {o});", "G !{i};", "G {o};", "G ({i} -> X {o});",
                      "G ({i} -> {o}); G !{o};", "G F {o};", "G !{i}; G {o};"]
        edge_names = [("@", "a'"), ("controllable_x", "uncontrollable_x"),
                      ("monitor_0_state_0", "assumption_safety_violated"), ("req@i", "val'")]
        for index in range(40):
            chosen = edge_names[index] if index < len(edge_names) else rng.sample(names, 2)
            variants = []
            for variant, (i, o) in enumerate((("i", "o"), chosen)):
                label = f"alpha-{index}-{variant}"
                source = directory / (label + ".tlsf")
                source.write_text(tiny(i, o, "true;", guarantees[index % len(guarantees)].format(i=i, o=o)))
                path, data = reduce(source, label)
                game = Game(path.read_text())
                assert game.input_names == ["uncontrollable_i0", "controllable_o0"]
                assert [row["name"] for row in data["inputs"] + data["outputs"]] == [i, o]
                assert data["source_origin_metadata"]["available"]
                variants.append((path.read_bytes(), solve(path, data, label)))
            assert variants[0] == variants[1]
    gold.finish()
    print("golden monitor games, certificates, controller mutations and 40 alpha pairs passed")


if __name__ == "__main__":
    main()
