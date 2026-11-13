"""Keep normalization help and rejected legacy options consistent."""

import subprocess
import sys
import csv
import io


normalize = sys.argv[1]
result = subprocess.run([normalize, "--help"], text=True, capture_output=True)
assert result.returncode == 0 and "--norm-soundness" in result.stderr, result
assert "--check-equivalence" not in result.stderr, result
assert "verify is an alias" in result.stderr, result
for option in ("--check-equivalence", "--check-equivalence=auto",
               "--check-equivalence=off"):
    result = subprocess.run([normalize, option], text=True, capture_output=True)
    assert result.returncode == 1 and "unknown option" in result.stderr, result

source = '''INFO { TITLE: "stats"; DESCRIPTION: "stats";
SEMANTICS: Mealy; TARGET: Mealy; }
MAIN { INPUTS { a; b; c; } GUARANTEE { G(a && b && c); } }
'''


def run(*args, text=source):
    return subprocess.run([normalize, *args], input=text, text=True,
                          capture_output=True, timeout=10)


for args, text in [(("--passes", "route-safe"), source),
                   (("--passes", "sickert-stage2"),
                    source.replace("SEMANTICS: Mealy", "SEMANTICS: Mealy,Finite")),
                   (("--passes", "pre-weak"), source)]:
    asserted = run("--norm-soundness", "assert", *args, text=text)
    verified = run("--norm-soundness", "verify", *args, text=text)
    assert (asserted.returncode, asserted.stdout, asserted.stderr) == (
        verified.returncode, verified.stdout, verified.stderr), (asserted, verified)
    assert asserted.returncode == (0 if args[-1] == "route-safe" else 1), asserted

for args, column in [(("--passes", "split"), "split"),
                     (("--pre-passes", "pre-spine-split"), "pre-spine-split"),
                     (("--passes", "route-safe", "--norm-max-nodes", "1"),
                      "rejected_nodes"),
                     (("--passes", "route-safe", "--norm-max-growth", "1"),
                      "rejected_growth")]:
    plain = run(*args)
    measured = run("--norm-stats=tsv", *args)
    assert plain.returncode == measured.returncode == 0, (plain, measured)
    assert plain.stdout == measured.stdout, (plain, measured)
    rows = list(csv.DictReader(io.StringIO(measured.stderr), delimiter="\t"))
    active, = [row for row in rows if row["schedule"] != "off"]
    assert int(active[column]) == 1, active
    assert int(active["formulas_seen"]) == int(active["iterations_total"]) == 1, active
    assert "passes_changed_total" in active and "rules_fired_total" not in active
