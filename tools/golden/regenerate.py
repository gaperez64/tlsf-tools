#!/usr/bin/env python3
"""Reproduce memberships and verify frozen recordings using in-house checks.

Never overwrites historical data or provenance. Scratch/output must be below
build-sprint. Use --translation to also replay every kernel-checked receipt.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys

from reference import atoms, membership, parse, parse_prefix, prefix, random_formulas, sample_equivalent

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "test/fixtures/golden"
NAMES = ["unused_in", "req", "a", "unused_out", "c", "grant", "b"]


def run(args, **kwargs):
    return subprocess.run(list(map(str, args)), capture_output=True, text=True,
                          timeout=kwargs.pop("timeout", 1800), **kwargs)


def fingerprints():
    return {str(p.relative_to(DEST)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in DEST.rglob("*") if p.is_file()}


def reproduce_dpa(output):
    directory = DEST / "dpa"
    words = [([int(x) for x in p.split()], [int(x) for x in q.split()])
             for p, q in (line.split(";") for line in (directory / "words.txt").read_text().splitlines())]
    lines = []
    for line in (directory / "membership.tsv").read_text().splitlines():
        formula, tree, expected = line.split("\t")
        actual = membership(formula, NAMES, words)
        assert actual == expected, (formula, "membership disagreement")
        assert membership(parse_prefix(tree), NAMES, words) == actual, (formula, "AST disagreement")
        # Retain the historical AST serialization. Its parser origin is frozen;
        # only the membership column is rederived here.
        lines.append("\t".join((formula, tree, actual)))
    data = "\n".join(lines) + "\n"
    assert data.encode() == (directory / "membership.tsv").read_bytes()
    (output / "membership.tsv").write_text(data)
    print(f"dpa: {len(lines)} x {len(words)} memberships reproduced byte-identically", flush=True)


def random_corpus(build, output):
    directory = output / "random"
    directory.mkdir(exist_ok=True)
    formulas = random_formulas()
    import random
    rng = random.Random(0x97D0A)
    words = [([], [bits]) for bits in range(128)] + [
        ([rng.randrange(128) for _ in range(rng.randrange(5))],
         [rng.randrange(128) for _ in range(rng.randrange(1, 6))]) for _ in range(64)]
    (directory / "words.txt").write_text("\n".join(" ".join(map(str, p)) + ";" +
        " ".join(map(str, q)) for p, q in words) + "\n")
    (directory / "membership.tsv").write_text("\n".join("\t".join((f, prefix(parse(f)),
        membership(f, NAMES, words))) for f in formulas) + "\n")
    (directory / "formulas.ltl").write_text("\n".join(formulas) + "\n")
    result = run([build / "test/unit/dpa_equivalence", directory / "formulas.ltl"],
                 env=dict(os.environ, DPA_REFERENCE_DIR=str(directory)))
    (output / "random.log").write_text(result.stdout + result.stderr)
    assert result.returncode == 0, result.stderr
    print(f"random: {len(formulas)} seeded in-house formulas, {len(words)} lassos each; native DPA agrees", flush=True)


def verify_languages():
    count = 0
    for path in sorted(DEST.glob("*.json")):
        rows = json.loads(path.read_text())
        if not isinstance(rows, list):
            continue
        for row in rows:
            if row[0] == "language":
                formula, names, words, expected = row[1]
                assert membership(formula, names, words) == expected, (path, formula)
                count += len(words)
    print(f"language: {count} committed memberships rederived", flush=True)


def script(name, *args):
    sys.argv = [str(ROOT / "test/oracle" / name), *map(str, args)]
    runpy.run_path(sys.argv[0], run_name="__main__")


def verify_native_verdict(build, output, fields):
    """Exact native game result, or None. Never infer a verdict from a decline."""
    formula, inputs, outputs, finite, moore = fields
    if finite or moore:
        return None
    tree = parse(formula)
    names = sorted(atoms(tree))

    def selected(interface):
        import re
        result = set()
        for item in filter(None, interface.split(",")):
            if item.startswith("/") and item.endswith("/"):
                result.update(n for n in names if re.search(item[1:-1], n))
            else:
                result.add(item)
        return result
    ins, outs = selected(inputs), selected(outputs)
    if ins & outs or not set(names) <= ins | outs:
        return None
    aliases = {n: f"refap{i}" for i, n in enumerate(sorted(ins | outs))}

    def render(node):
        op = node[0]
        if op == "ap":
            return aliases[node[1]]
        if op in ("0", "1"):
            return "true" if op == "1" else "false"
        if len(node) == 2:
            return f"{op} ({render(node[1])})"
        if op == "^":
            return f"!({render(node[1])} <-> {render(node[2])})"
        symbol = {"i": "->", "e": "<->", "&": "&&", "|": "||"}.get(op, op)
        return f"({render(node[1])} {symbol} {render(node[2])})"
    source = output / "verdict.tlsf"
    source.write_text("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { " +
        " ".join(aliases[n] + ";" for n in sorted(ins)) + " } OUTPUTS { " +
        " ".join(aliases[n] + ";" for n in sorted(outs)) + " } GUARANTEES { " + render(tree) + "; } }")
    base = output / "verdict"
    for suffix in (".cert.aag", ".cert.aag.json", ".policy.aag", ".policy.aag.json"):
        base.with_suffix(suffix).unlink(missing_ok=True)
    try:
        reduced = run([build / "test/api/native_reduction", source, "exact", base], timeout=20)
        if reduced.returncode != 0:
            assert reduced.returncode == 3, reduced.stderr
            return None
        game = base.with_suffix(".aag")
        cert, policy = base.with_suffix(".cert.aag"), base.with_suffix(".policy.aag")
        solved = run([build / "tlsfsolve", "--certificate", cert, "--policy", policy, game], timeout=20)
        if solved.returncode not in (0, 1):
            return None
        sidecar_path = Path(str(cert) + ".json")
        if not sidecar_path.is_file():
            return None
        sidecar = json.loads(sidecar_path.read_text())
        if sidecar.get("side") != ("system" if solved.returncode == 0 else "environment"):
            return None
        # A failed certificate is UNKNOWN, never a losing verdict. Winning
        # games use the policy-free region proof; losing games require the
        # dual environment certificate AND checked closed-loop counterstrategy.
        command = [build / "tlsfcertcheck", "--certificate", cert, "--method"]
        command += ["region", game] if solved.returncode == 0 else ["both", game, policy]
        checked = run(command, timeout=20)
        if checked.returncode != 0:
            return None
        return solved.returncode == 0
    except subprocess.TimeoutExpired:
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT / "build-sprint/oracle-retirement")
    parser.add_argument("--only", choices=("dpa", "exports", "pruning", "native", "language", "monitor", "lift", "norm", "api", "step1"))
    parser.add_argument("--translation", action="store_true", help="replay all committed C/Lean translation receipts")
    options = parser.parse_args()
    build, output = options.build.resolve(), options.output.resolve()
    assert output.is_relative_to(ROOT / "build-sprint"), "scratch must be under build-sprint"
    output.mkdir(parents=True, exist_ok=True)
    temp = ROOT / "build-sprint/tmp"
    temp.mkdir(exist_ok=True)
    os.environ.update(TMPDIR=str(temp), LEAN_NUM_THREADS="1", LEAN_STACK_SIZE_KB="2048",
                      LEAN_MAIN_USE_THREAD="0", CARGO_BUILD_JOBS="1")
    before = fingerprints()
    sys.path.insert(0, str(ROOT / "test/oracle"))
    import golden
    base = golden.Golden
    totals, cache, verified_suites = Counter(), {}, {}

    class Verifier(base):
        def check(self, label, value):
            super().check(label, value)
            if label == "normalized" and self.name.startswith("norm-"):
                original = next(v for k, v in self.records if k == "original")
                sample_equivalent(original, value, count=512)
                totals["sampled_normalization_pairs"] += 1
            if label == "ast-export":
                lines = value.splitlines()
                for index, line in enumerate(lines):
                    if line.startswith("string: "):
                        sample_equivalent(lines[index - 1].split(": ", 1)[1], line[8:], count=512)
                        totals["sampled_api_pairs"] += 1

        def verdict(self, *args, **kwargs):
            position = self.position
            expected = super().verdict(*args, **kwargs)
            fields = self.records[position][1]
            key = json.dumps(fields)
            if key not in cache:
                cache[key] = verify_native_verdict(build, output, fields)
            actual = cache[key]
            if actual is not None:
                assert actual == expected, (self.name, fields, actual, expected)
            totals["unknown" if actual is None else "native_certificate_agrees"] += 1
            return expected  # Historical data, never persisted as new evidence.

        def language(self, formula, names, words, actual):
            assert membership(formula, names, words) == actual, (self.name, formula)
            super().language(formula, names, words, actual)

        def finish(self):
            super().finish()
            verified_suites[self.name] = self.position
            print(f"verified frozen suite {self.name}: {self.position} records", flush=True)
    golden.Golden = Verifier
    cases = ROOT / "test/fixtures/cases"
    selected = lambda name: options.only in (None, name)
    try:
        if selected("dpa"):
            reproduce_dpa(output)
            random_corpus(build, output)
        if selected("language"):
            verify_languages()
        if selected("pruning"):
            script("test_assumption_pruning.py", build / "tlsf2ltl", build / "tlsfresidual", build / "tlsfcompose")
            from pruning_sources import verify
            verify(ROOT, build)
        if selected("exports"):
            for mode in ("lowercase", "comment", "signals"):
                script("test_review4_exports.py", build / "tlsf2ltl", build / "tlsfresidual", build / "tlsfcompose", mode)
            for mode in ("moore", "finite", "implicit", "wrapper"):
                script("test_compose_driver_semantics.py", build / "tlsfcompose", mode)
            script("test_decomposition_exactness.py", build / "tlsf2ltl", build / "tlsfresidual", build / "tlsfcompose", build / "test/unit/phase_b_probe", cases)
            script("test_disjoint_assumptions.py", build / "tlsf2ltl", build / "tlsfresidual", build / "tlsfcompose", cases / "disjoint_assumptions.tlsf")
        for mode, name in (("native", "native_reduction"), ("language", "native_reduction_language"),
                           ("monitor", "gr1_monitor_game"), ("lift", "native_lift_differential")):
            if selected(mode):
                script("test_" + name + ".py", "--builddir", build)
        if selected("norm"):
            script("test_normalization.py", build / "tlsfnorm", build / "tlsf2ltl", cases)
        if selected("api"):
            script("test_conversion.py", build / "test/api/ast_golden", cases / "cluster_split.tlsf")
        if selected("step1"):
            script("native_oracle.py", build)
        if options.translation:
            from verify_translation import verify
            verify(build, output)
    finally:
        assert fingerprints() == before, "historical data/provenance changed"
    (output / "verification.json").write_text(json.dumps({"historical_files_unchanged": len(before),
        "checks": dict(totals), "unique_verdicts": len(cache), "python": sys.version,
        "verified_suites": verified_suites,
        "direct_evaluator_sha256": hashlib.sha256(Path(__file__).with_name("reference.py").read_bytes()).hexdigest()},
        indent=2) + "\n")
    print(f"historical files unchanged: {len(before)}; verdict crosschecks: {dict(totals)}", flush=True)


if __name__ == "__main__":
    main()
