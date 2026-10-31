#!/usr/bin/env python3
"""Offline C/Lean translation validation; requires Lean, never run by CI.

Run from the repository root in the task's memory-limited systemd scope.
All transient artifacts are below build-scratch-t. No external oracle is used.
"""
import argparse
from collections import Counter, defaultdict
from datetime import date
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SCRATCH = ROOT / "build-scratch-t/translation"
DEST = ROOT / "test/fixtures/golden/translation"
NAMES = ("unused_in", "req", "a", "unused_out", "c", "grant", "b")
REVIEWS = [
    "G | F | $a & $a X F $b X F $b",
    "G | F | $a & $a X X $b X X $b",
    "G | F $a & F $a F G $b",
    "X G | $a & $a F G $b",
    "& G $s & | F $q | $p ! $p & $p G F $r",
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(args, **kw):
    return subprocess.run(list(map(str, args)), capture_output=True, text=True,
                          timeout=kw.pop("timeout", 60), **kw)


def request(kind, mode, names, prefix):
    return " ".join(["TV1", kind, mode, str(len(names)), *names, prefix])


def collect(build):
    paths = sorted(set(ROOT.glob("bench/**/*.tlsf")) | set(ROOT.glob("test/**/*.tlsf")))
    assert len(paths) == 217, "review corpus changes before regenerating"
    cases = {}

    def add(names, prefix, group, origin):
        prefix = " ".join(prefix.split())
        key = (tuple(names), prefix)
        row = cases.setdefault(key, {"names": list(names), "prefix": prefix, "sets": {}})
        row["sets"].setdefault(group, []).append(origin)

    coverage = {mode: [] for mode in ("default", "general")}
    for mode in coverage:
        for path in paths:
            try:
                result = run([build / "test/unit/tv_inventory", mode, path, "exact",
                              SCRATCH / "inventory-result"], timeout=20)
                status = result.returncode
                for line in result.stdout.splitlines():
                    if line.startswith("TV1 "):
                        fields = line.split()
                        count = int(fields[3])
                        add(fields[4:4 + count], " ".join(fields[4 + count:]),
                            "corpus", str(path.relative_to(ROOT)))
                reason = result.stderr.strip()
            except subprocess.TimeoutExpired as e:
                status, reason = "timeout", str(e)
            coverage[mode].append({"path": str(path.relative_to(ROOT)), "status": status,
                                   "reason": reason})
        print("coverage", mode, Counter(str(x["status"]) for x in coverage[mode]), flush=True)

    equivalence_source = (ROOT / "test/unit/dpa_equivalence.cpp").read_text()
    literals = set(re.findall(r'"([^"\n]*)"', equivalence_source))
    equivalences = literals | {"!(" + x + ")" for x in literals}
    for line in (ROOT / "test/fixtures/golden/dpa/membership.tsv").read_text().splitlines():
        text, prefix, _ = line.split("\t")
        add(NAMES, prefix, "golden", text)
        if text in equivalences:
            add(NAMES, prefix, "equivalence", text)
    # Include every pinned infinite-word verdict and every stored monitor
    # construction formula, including historical accepted rows archived in
    # provenance. Finite-word games are outside this automaton API.
    golden_formulas = defaultdict(list)

    def add_formula(text, inputs, outputs, origin):
        atom_names = set()
        for token in re.findall(r'"(?:[^"\\]|\\.)*"|[A-Za-z_@][A-Za-z0-9_@\']*', text):
            if token.startswith('"'):
                atom_names.add(json.loads(token))
            elif token not in ("G", "F", "X", "U", "R", "W", "M", "true", "false"):
                atom_names.add(token)

        def literal(name):
            if name.startswith("/^") and name.endswith("$/"):
                encoded = name[2:-2]
                assert re.fullmatch(r"(?:\\x[0-9a-fA-F]{2})+", encoded), name
                return [bytes.fromhex("".join(re.findall(r"\\x([0-9a-fA-F]{2})", encoded))).decode()]
            if name.startswith("/") and name.endswith("/"):
                return sorted(a for a in atom_names if re.search(name[1:-1], a))
            return [name]
        inputs = [a for name in inputs for a in literal(name)]
        outputs = [a for name in outputs for a in literal(name)]
        golden_formulas[(text, tuple(inputs), tuple(outputs))].append(origin)

    def stored_monitors(value, origin):
        if isinstance(value, dict):
            if all(k in value for k in ("monitors", "inputs", "outputs")):
                names = lambda xs: [x if isinstance(x, str) else x["name"] for x in xs]
                ins, outs = names(value["inputs"]), names(value["outputs"])
                for monitor in value["monitors"]:
                    if "construction_formula" not in monitor:
                        continue
                    support = (monitor.get("source_origin") or {}).get("signals", ins + outs)
                    add_formula(monitor["construction_formula"],
                                [x for x in ins if x in support],
                                [x for x in outs if x in support], origin)
            for child in value.values():
                stored_monitors(child, origin)
        elif isinstance(value, list):
            for child in value:
                stored_monitors(child, origin)

    for path in sorted((ROOT / "test/fixtures/golden").glob("*.json")):
        rows = json.loads(path.read_text())
        if isinstance(rows, list):
            for index, row in enumerate(rows):
                if isinstance(row, list) and len(row) > 1 and row[0] == "verdict":
                    fields = row[1]
                    if len(fields) >= 4 and not fields[3]:
                        add_formula(fields[0], list(filter(None, fields[1].split(","))),
                                    list(filter(None, fields[2].split(","))), f"{path.name}:{index}")
        stored_monitors(rows, path.name)
    for (text, ins, outs), origins in sorted(golden_formulas.items()):
        aliases = {name: f"tvrename{i}" for i, name in enumerate(ins + outs)}
        reverse = {alias: name for name, alias in aliases.items()}

        def rename(match):
            token = match.group()
            if token.startswith('"'):
                return aliases[json.loads(token)]
            if token in ("0", "1"):
                return "true" if token == "1" else "false"
            if token in ("G", "F", "X", "U", "R", "W", "M", "true", "false"):
                return token
            return aliases.get(token, token)

        # The frontend lowercases APs. Temporary valid identifiers preserve
        # the golden's case-sensitive, sometimes quoted AP identities; restore
        # their exact names and order on the parsed prefix AST afterward.
        body = re.sub(r'"(?:[^"\\]|\\.)*"|[A-Za-z_@][A-Za-z0-9_@\']*|\b[01]\b', rename, text)
        body = re.sub(r"(?<!&)&(?!&)", "&&", body)
        body = re.sub(r"(?<!\|)\|(?!\|)", "||", body)
        source = ("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { " +
                  " ".join(aliases[x] + ";" for x in ins) + " } OUTPUTS { " +
                  " ".join(aliases[x] + ";" for x in outs) + " } GUARANTEES { " + body + "; } }")
        path = SCRATCH / "golden-formula.tlsf"
        path.write_text(source)
        grounded = run([build / "test/unit/tv_inventory", "--ground", path])
        assert grounded.returncode == 0, (text, grounded.stderr)
        fields = grounded.stdout.split()
        assert fields[:3] == ["TV1", "parity", "default"], grounded.stdout
        count = int(fields[3])
        names = [reverse[x] for x in fields[4:4 + count]]
        prefix = " ".join("$" + reverse[x[1:]] if x.startswith("$") else x
                          for x in fields[4 + count:])
        for origin in origins:
            add(names, prefix, "golden", origin)
    for prefix in REVIEWS:
        for formula in (prefix, "! " + prefix):
            names = sorted({x[1:] for x in formula.split() if x.startswith("$")})
            add(names, formula, "review", formula)
    source_hashes = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}
    result = {"cases": sorted(cases.values(), key=lambda x: (x["names"], x["prefix"])),
              "golden_formula_inventory_sha256": sha(json.dumps(sorted(golden_formulas)).encode()),
              "coverage": coverage, "corpus_sources": source_hashes}
    (SCRATCH / "inventory.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def validate_one(build, validator, text, timeout, receipts=None):
    source, target = SCRATCH / "request.txt", SCRATCH / "dump.txt"
    source.write_text(text + "\n")
    try:
        result = run([build / "test/unit/dpa_dump", source], timeout=timeout)
        if result.returncode == 77:
            return "declined", "unsupported", sha(result.stdout.encode())
        if result.returncode:
            return "fail", f"C dump failure ({result.returncode}): {result.stderr.strip()}", None
        digest = sha(result.stdout.encode())
        previous = (receipts or {}).get(text)
        if previous and previous["status"] == "pass" and previous["sha256"] == digest:
            return previous["status"], previous["reason"], digest
        target.write_text(result.stdout)
        checked = run([validator, source, target], timeout=timeout)
        if checked.returncode or checked.stdout != "pass\n":
            return "fail", checked.stderr.strip() or "invalid validator verdict", None
        return "pass", "", digest
    except subprocess.TimeoutExpired:
        return "fail", "validation timeout", None


def parse_tree(tokens):
    token = next(tokens)
    arity = 0 if token in ("0", "1") or token.startswith("$") else (1 if token in "!XxFG" else 2)
    return (token, tuple(parse_tree(tokens) for _ in range(arity)))


def prefix_tree(tree):
    return " ".join([tree[0], *(prefix_tree(x) for x in tree[1])])


def shrinks(tree):
    if tree[1]:
        yield ("0", ())
        yield ("1", ())
        yield from tree[1]
        for index, child in enumerate(tree[1]):
            for smaller in shrinks(child):
                children = list(tree[1])
                children[index] = smaller
                yield (tree[0], tuple(children))


def minimize(build, validator, row, timeout):
    tree = parse_tree(iter(row["prefix"].split()))
    trials = 0
    while trials < 100:
        changed = False
        for candidate in sorted(set(shrinks(tree)), key=lambda x: len(prefix_tree(x).split())):
            if len(prefix_tree(candidate).split()) >= len(prefix_tree(tree).split()):
                continue
            text = request(row["kind"], row["mode"], row["names"], prefix_tree(candidate))
            status, reason, _ = validate_one(build, validator, text, timeout)
            trials += 1
            if status == "fail" and reason == row["reason"]:
                tree, changed = candidate, True
                break
            if trials >= 100:
                break
        if not changed:
            break
    return {"prefix": prefix_tree(tree), "trials": trials,
            "disabled": True, "reason": row["reason"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--reuse-inventory", action="store_true")
    parser.add_argument("--collect-only", action="store_true")
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument("--set", choices=("corpus", "golden", "equivalence", "review"))
    parser.add_argument("--resume", action="store_true",
                        help="reuse receipts only for this exact Lean executable and identical fresh C dumps")
    parser.add_argument("--max-new", type=int, default=0,
                        help="checkpoint after this many new verdicts; exit 75 until the run is complete")
    args = parser.parse_args()
    SCRATCH.mkdir(parents=True, exist_ok=True)
    os.environ["TMPDIR"] = str(ROOT / "build-scratch-t/tmp")
    os.environ["LEAN_NUM_THREADS"] = "1"
    build = args.build.resolve()
    compiled = run(["meson", "compile", "-C", build, "-j2", "dpa_dump", "tv_inventory"],
                   cwd=ROOT, timeout=600)
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    data = json.loads((SCRATCH / "inventory.json").read_text()) if args.reuse_inventory else collect(build)
    for path, digest in data["corpus_sources"].items():
        assert sha((ROOT / path).read_bytes()) == digest, f"stale corpus inventory: {path}"
    assert all(row["status"] != "timeout" for rows in data["coverage"].values() for row in rows), \
        "incomplete corpus inventory: a reduction timed out"
    if args.collect_only:
        return
    # Never accept verdicts from an executable left over from a failed build.
    built = run([Path.home() / ".elan/bin/lake", "build", "dpaValidate"],
                cwd=ROOT / "proofs", timeout=600)
    assert built.returncode == 0, built.stdout + built.stderr
    validator = ROOT / "proofs/.lake/build/bin/dpaValidate"
    assert validator.is_file(), "build lake exe dpaValidate first"
    checked = run([validator, "--self-test"], timeout=60)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    version = run([Path.home() / ".elan/bin/lake", "env", "lean", "--version"], cwd=ROOT / "proofs")
    assert version.returncode == 0 and "4.35.0" in version.stdout, version
    executable_hash = sha(validator.read_bytes())
    checkpoint = SCRATCH / "checkpoint.json"
    receipts = {}
    if args.resume and checkpoint.exists():
        prior = json.loads(checkpoint.read_text())
        if prior["validator_sha256"] == executable_hash:
            receipts = prior["receipts"]
    new_verdicts = 0
    counts = defaultdict(Counter)
    failures, goldens, records = [], [], []
    for index, case in enumerate(data["cases"]):
        if args.set and args.set not in case["sets"]:
            continue
        for mode in ("default", "general"):
            for kind in ("parity", "buchi"):
                text = request(kind, mode, case["names"], case["prefix"])
                previous = receipts.get(text)
                status, reason, digest = validate_one(build, validator, text, args.timeout, receipts)
                if not previous or digest is None or previous["sha256"] != digest:
                    new_verdicts += 1
                receipts[text] = {"status": status, "reason": reason, "sha256": digest}
                row = {**case, "mode": mode, "kind": kind, "status": status,
                       "reason": reason, "sha256": digest}
                records.append(row)
                for group in case["sets"]:
                    counts[f"{group}/{mode}/{kind}"][status] += 1
                if status in ("pass", "declined"):
                    goldens.append(f"{digest}\t{status}\t{text}\n")
                if status == "fail":
                    print("FAIL", mode, kind, case["prefix"], reason, flush=True)
                    failures.append(row)
        print(f"validated {index + 1}/{len(data['cases'])}", flush=True)
        # Interrupted runs retain exact verdicts without publishing partial goldens.
        (SCRATCH / "progress.json").write_text(json.dumps(records, indent=2) + "\n")
        pending = checkpoint.with_suffix(".new")
        pending.write_text(json.dumps({"validator_sha256": executable_hash, "receipts": receipts}) + "\n")
        pending.replace(checkpoint)
        if args.max_new and new_verdicts >= args.max_new and index + 1 < len(data["cases"]):
            print(f"checkpoint saved: {new_verdicts} new verdicts; resume with --resume", flush=True)
            raise SystemExit(75)
    for row in failures:
        print("minimizing", row["mode"], row["kind"], row["prefix"], flush=True)
        row["minimized"] = minimize(build, validator, row, args.timeout)
    report = {"date": str(date.today()), "counts": dict(sorted(counts.items())),
              "coverage": {mode: dict(Counter(str(x["status"]) for x in rows))
                           for mode, rows in data["coverage"].items()},
              "failures": failures, "all_validated": not failures,
              "partial_set": args.set}
    (SCRATCH / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    # Only a complete run may publish the CI fixtures.
    if not args.set:
        DEST.mkdir(parents=True, exist_ok=True)
        (DEST / "hashes.tsv").write_text("".join(sorted(goldens)))
        (DEST / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        provenance = {"date": report["date"], "lean": version.stdout.strip(),
                      "validator_executable_sha256": executable_hash,
                      "revision": run(["git", "rev-parse", "HEAD"], cwd=ROOT).stdout.strip(),
                      "checker_theorems": ["Tlsf.Dpa.Validation.check_language",
                                           "Tlsf.Dpa.Validation.checkBuchi_sound",
                                           "Tlsf.Dpa.Validation.checkCompact_sound",
                                           "Tlsf.Dpa.Validation.checkBuchiCompact_sound"],
                      "construction_theorem": "Tlsf.Dpa.Impl.normalized_finite_construction_language",
                      "validation_theorems": ["Tlsf.Dpa.Validation.validate_parity_sound",
                                               "Tlsf.Dpa.Validation.validate_buchi_sound"],
                      "hashes_sha256": sha((DEST / "hashes.tsv").read_bytes()),
                      "source_sha256": {
                          str(p.relative_to(ROOT)): sha(p.read_bytes())
                          for p in sorted(set(ROOT.glob("proofs/TlsfProofs/**/*.lean")) |
                                          set(ROOT.glob("src/lib/dpa*.[ch]")) |
                                          {ROOT / "test/unit/dpa_dump.c",
                                           Path(__file__).resolve(),
                                           ROOT / "tools/golden/tv_inventory.cc"})},
                      "corpus_sources": data["corpus_sources"],
                      "golden_formula_inventory_sha256": data["golden_formula_inventory_sha256"],
                      "validated_artifacts": sum(r["status"] == "pass" for r in records),
                      "golden_artifacts": len(goldens)}
        (DEST / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
