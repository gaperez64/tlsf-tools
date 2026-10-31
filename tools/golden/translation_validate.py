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
    for prefix in REVIEWS:
        for formula in (prefix, "! " + prefix):
            names = sorted({x[1:] for x in formula.split() if x.startswith("$")})
            add(names, formula, "review", formula)
    source_hashes = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}
    result = {"cases": sorted(cases.values(), key=lambda x: (x["names"], x["prefix"])),
              "coverage": coverage, "corpus_sources": source_hashes}
    (SCRATCH / "inventory.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def validate_one(build, validator, text, timeout):
    source, target = SCRATCH / "request.txt", SCRATCH / "dump.txt"
    source.write_text(text + "\n")
    try:
        result = run([build / "test/unit/dpa_dump", source], timeout=timeout)
        if result.returncode == 77:
            return "declined", "unsupported", sha(result.stdout.encode())
        if result.returncode:
            return "fail", f"C dump failure ({result.returncode}): {result.stderr.strip()}", None
        target.write_text(result.stdout)
        checked = run([validator, source, target], timeout=timeout)
        if checked.returncode or checked.stdout != "pass\n":
            return "fail", checked.stderr.strip() or "invalid validator verdict", None
        return "pass", "", sha(result.stdout.encode())
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
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--set", choices=("corpus", "golden", "equivalence", "review"))
    args = parser.parse_args()
    SCRATCH.mkdir(parents=True, exist_ok=True)
    os.environ["TMPDIR"] = str(ROOT / "build-scratch-t/tmp")
    os.environ["LEAN_NUM_THREADS"] = "1"
    build = args.build.resolve()
    data = json.loads((SCRATCH / "inventory.json").read_text()) if args.reuse_inventory else collect(build)
    for path, digest in data["corpus_sources"].items():
        assert sha((ROOT / path).read_bytes()) == digest, f"stale corpus inventory: {path}"
    if args.collect_only:
        return
    compiled = run(["meson", "compile", "-C", build, "-j2", "dpa_dump", "tv_inventory"],
                   cwd=ROOT, timeout=600)
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
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
    counts = defaultdict(Counter)
    failures, goldens, records = [], [], []
    for index, case in enumerate(data["cases"]):
        if args.set and args.set not in case["sets"]:
            continue
        for mode in ("default", "general"):
            for kind in ("parity", "buchi"):
                text = request(kind, mode, case["names"], case["prefix"])
                status, reason, digest = validate_one(build, validator, text, args.timeout)
                row = {**case, "mode": mode, "kind": kind, "status": status, "reason": reason}
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
                      "validated_artifacts": sum(r["status"] == "pass" for r in records),
                      "golden_artifacts": len(goldens)}
        (DEST / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
