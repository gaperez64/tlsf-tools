"""Sequential, bounded expansion comparison; writes full evidence under bld.

No corpus files are modified. Both binaries receive exactly --format ltl.
"""
import argparse
import collections
import csv
import difflib
import json
import os
from pathlib import Path
import subprocess
import hashlib

ROOT = Path(__file__).resolve().parents[2]
SCRATCH = ROOT / "bld/codex-tmp"
CORPUS = Path("/home/gaperez/GIT-repos/acacia-bonsai/tlsf-corpus")
ENV = {**os.environ, "TMPDIR": str(SCRATCH)}
# §4.8: X[1] and X have the same core. Pin both observations for this
# hand-written fixture; every unaccounted-for output difference stays "other".
IDENTITY_EXPECTATIONS = {
    "test/fixtures/scoping110/identity_sugar.tlsf": ("true\n", "false\n"),
}


def run(binary, source, baseline):
    env = {**ENV, "LD_LIBRARY_PATH": str(SCRATCH / "main-bin") if baseline
           else str(ROOT / "bld/subprojects/yyjson-0.12.0")}
    try:
        result = subprocess.run([str(binary), "--format", "ltl", str(source)],
                                capture_output=True, text=True, env=env, timeout=17)
        return {"status": result.returncode, "stdout": result.stdout,
                "stderr": result.stderr}
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "stdout": "", "stderr": ""}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-stem", default="impact110")
    args = parser.parse_args()
    assert Path(args.output_stem).name == args.output_stem
    stem = args.output_stem
    rows = []
    evidence = []
    sources = [("corpus", p) for p in sorted(CORPUS.rglob("*.tlsf"))]
    sources += [(group, p) for group in ("bench/specs", "test")
                for p in sorted((ROOT / group).rglob("*.tlsf"))]
    for group, source in sources:
        old = run(SCRATCH / "main-bin/tlsf2ltl-main", source, True)
        new = run(ROOT / "bld/tlsf2ltl", source, False)
        name = str(source.relative_to(CORPUS if group == "corpus" else ROOT))
        if "timeout" in (old["status"], new["status"]):
            change, category = "timeout", "timeout"
        elif old["status"] == 0 and new["status"] != 0:
            change = "newly rejected"
            category = ("scoping" if "expand: scoping:" in new["stderr"] else
                        "typing" if "expand: typing:" in new["stderr"] else "other")
        elif old["status"] != 0 and new["status"] == 0:
            change, category = "newly accepted", "closure"
        elif old["status"] == new["status"] == 0 and old["stdout"] != new["stdout"]:
            # All such cases must be individually reviewed before this gate is
            # complete; record the full outputs rather than inferring a cause.
            change = "different output"
            category = ("identity" if IDENTITY_EXPECTATIONS.get(name) ==
                        (old["stdout"], new["stdout"]) else "other")
        else:
            change, category = "unchanged", "accepted" if new["status"] == 0 else "rejected"
        diff = "".join(difflib.unified_diff(old["stdout"].splitlines(True),
                                          new["stdout"].splitlines(True),
                                          fromfile="main", tofile="new"))
        rows.append([group, name, old["status"], new["status"], change, category,
                     json.dumps(new["stderr"].strip(), ensure_ascii=False),
                     json.dumps(diff, ensure_ascii=False)])
        if change != "unchanged":
            evidence.append({"group": group, "file": name, "change": change,
                             "category": category, "main": old, "new": new,
                             "diff": diff})
        if len(rows) % 100 == 0:
            print(f"{len(rows)}/{len(sources)}", flush=True)
    with (SCRATCH / (stem + ".tsv")).open("w") as stream:
        writer = csv.writer(stream, delimiter="\t")
        writer.writerow(["group", "file", "main_status", "new_status", "change",
                         "category", "diagnostic", "diff"])
        writer.writerows(rows)
    (SCRATCH / (stem + ".json")).write_text(json.dumps(evidence, indent=2) + "\n")
    counts = collections.Counter((r[0], r[4], r[5]) for r in rows)
    metadata = {
        "base": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "timeout_seconds": 17, "sequential": True,
        "source_counts": dict(collections.Counter(group for group, _ in sources)),
        "binary_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (SCRATCH / "main-bin/tlsf2ltl-main", ROOT / "bld/tlsf2ltl")},
        "counts": {" | ".join(k): v for k, v in sorted(counts.items())},
    }
    (SCRATCH / (stem + "-meta.json")).write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps({" | ".join(k): v for k, v in sorted(counts.items())}, indent=2))


if __name__ == "__main__":
    main()
