#!/usr/bin/env python3
"""norm_sweep.py — sweep normalization schedules over a TLSF corpus.

Runs `tlsfbenchgraph` once per schedule (using its --pre-normalize /
--match-normalize flags) and reports, per schedule, the structural deltas vs the
`off` baseline: extra template candidates, certified/solved blocks, eliminated
constraints, owned outputs, and the Sickert obstacle tail.

This is the structural/certification sweep (no solver is run here): it answers
"which schedule exposes the most exact recognition per spec, and at what growth
and soundness cost". A schedule is `soundness_eligible` only if it introduces no
new parse failures vs `off` (a new failure means the soundness gate rejected the
schedule on some spec — e.g. an infinite-word-only pass on a Finite spec).

Example:
  scripts/norm_sweep.py --corpus benchmarks/tlsf \\
      --tlsfbenchgraph build-research/tlsfbenchgraph \\
      --schedules off match-safe:1 match-safe:2 pre-safe:1,match-safe:1 \\
      --out docs/benchgraph/norm_sweep.tsv
"""
import argparse
import csv
import io
import os
import subprocess
import sys

# Columns summed into per-schedule aggregates.
CANDIDATE_COLS = [
    "response", "mutex", "recurrence", "persistence", "global_recurrence",
    "guarded_next", "definition",
]
SUM_COLS = CANDIDATE_COLS + [
    "template_candidates", "solved_blocks", "certified_blocks",
    "eliminated_constraints", "owned_outputs", "fully_solved",
    "formula_size_raw", "formula_size_norm",
    "u_under_w", "limit_under_temporal", "w_under_gf", "u_under_fg",
]


def collect_specs(corpus, explicit):
    specs = list(explicit)
    if corpus:
        for root, _dirs, files in os.walk(corpus):
            for f in sorted(files):
                if f.endswith(".tlsf"):
                    specs.append(os.path.join(root, f))
    return sorted(specs)


def run_schedule(benchgraph, specs, schedule, split, timeout):
    """Run tlsfbenchgraph for one schedule; return (aggregate dict, n_fail)."""
    cmd = [benchgraph]
    if split:
        cmd.append("--split")
    if schedule != "off":
        # A schedule may carry a pre-axis and a match-axis joined by '+';
        # otherwise it is a match schedule.
        pre, _, match = schedule.partition("+")
        if not match:
            pre, match = "", pre
        if pre:
            cmd += ["--pre-normalize", pre]
        if match:
            cmd += ["--match-normalize", match]
    cmd += specs
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, -1
    agg = {c: 0 for c in SUM_COLS}
    agg["n_ok"] = 0
    n_fail = 0
    reader = csv.DictReader(io.StringIO(proc.stdout), delimiter="\t")
    for row in reader:
        if row.get("file", "").startswith("#"):
            continue
        if row.get("parse_status") != "ok":
            n_fail += 1
            continue
        agg["n_ok"] += 1
        for c in SUM_COLS:
            v = row.get(c, "0")
            agg[c] += int(v) if v not in ("-", "", None) else 0
    return agg, n_fail


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--corpus", help="directory of *.tlsf specs (recursive)")
    p.add_argument("specs", nargs="*", help="explicit spec files")
    p.add_argument("--tlsfbenchgraph", required=True)
    p.add_argument("--schedules", nargs="+",
                   default=["off", "match-safe:1", "match-safe:2",
                            "pre-safe:1+match-safe:1"],
                   help="schedules; 'PRE+MATCH' splits the two axes")
    p.add_argument("--split", action="store_true", default=True)
    p.add_argument("--no-split", dest="split", action="store_false")
    p.add_argument("--timeout", type=float, default=600)
    p.add_argument("--out", help="TSV output (default stdout)")
    p.add_argument("--markdown", help="also write a markdown summary here")
    args = p.parse_args(argv)

    specs = collect_specs(args.corpus, args.specs)
    if not specs:
        print("norm_sweep: no specs", file=sys.stderr)
        return 1

    if "off" not in args.schedules:
        args.schedules = ["off"] + args.schedules
    base = None
    rows = []
    for sched in args.schedules:
        agg, n_fail = run_schedule(args.tlsfbenchgraph, specs, sched,
                                   args.split, args.timeout)
        if agg is None:
            print(f"norm_sweep: schedule {sched} timed out", file=sys.stderr)
            continue
        if sched == "off":
            base = agg
            base_fail = n_fail
        rows.append((sched, agg, n_fail))

    if base is None:
        print("norm_sweep: baseline 'off' did not run", file=sys.stderr)
        return 1

    out_cols = [
        "schedule", "n_ok", "n_fail",
        "candidate_delta_total", "certified_delta", "solved_delta",
        "fully_solved_delta", "elim_constraints_delta", "owned_outputs_delta",
        "limit_under_temporal_after", "w_under_gf_after", "u_under_fg_after",
        "formula_growth_percent", "new_fail", "soundness_eligible",
        "recommendation",
    ]

    def cand_total(agg):
        return sum(agg[c] for c in CANDIDATE_COLS)

    out = open(args.out, "w") if args.out else sys.stdout
    w = csv.writer(out, delimiter="\t")
    w.writerow(out_cols)
    summary = []
    for sched, agg, n_fail in rows:
        cdelta = cand_total(agg) - cand_total(base)
        certd = agg["certified_blocks"] - base["certified_blocks"]
        solvd = agg["solved_blocks"] - base["solved_blocks"]
        fsd = agg["fully_solved"] - base["fully_solved"]
        elimd = agg["eliminated_constraints"] - base["eliminated_constraints"]
        ownd = agg["owned_outputs"] - base["owned_outputs"]
        new_fail = max(0, n_fail - base_fail)
        growth = 0.0
        if base["formula_size_norm"]:
            growth = 100.0 * (agg["formula_size_norm"] -
                              base["formula_size_norm"]) / base["formula_size_norm"]
        eligible = 1 if new_fail == 0 else 0
        if sched == "off":
            rec = "baseline"
        elif not eligible:
            rec = "revert (new soundness failures)"
        elif solvd < 0 or elimd < 0:
            # Fewer solved/eliminated blocks: needs a solver-level check before
            # trusting (it may be benign — e.g. weak-simplify dropping vacuous
            # G(true) invariants — or a real recognizer regression).
            rec = "review (solved/elim regressed; verify with solver)"
        elif solvd > 0 or certd > 0 or elimd > 0:
            rec = "keep (more certified/solved)" if growth < 25 else \
                "opt-in (helps but grows)"
        elif cdelta > 0:
            rec = "opt-in (more candidates, no extra solved)"
        else:
            rec = "revert (no downstream gain)"
        w.writerow([sched, agg["n_ok"], n_fail, cdelta, certd, solvd, fsd,
                    elimd, ownd, agg["limit_under_temporal"], agg["w_under_gf"],
                    agg["u_under_fg"], f"{growth:.1f}", new_fail, eligible, rec])
        summary.append((sched, cdelta, certd, solvd, elimd, growth, eligible,
                       rec))
    if args.out:
        out.close()
        print(f"norm_sweep: wrote {args.out}", file=sys.stderr)

    if args.markdown:
        with open(args.markdown, "w") as md:
            md.write("# Normalization schedule sweep\n\n")
            md.write(f"Corpus: {len(specs)} specs. Structural/certification "
                     "sweep (no solver). Only soundness-eligible rows "
                     "(no new parse failures) should be ranked.\n\n")
            md.write("| schedule | cand Δ | certified Δ | solved Δ | "
                     "elim Δ | growth % | eligible | recommendation |\n")
            md.write("|---|--:|--:|--:|--:|--:|:--:|---|\n")
            for s in summary:
                md.write(f"| `{s[0]}` | {s[1]:+d} | {s[2]:+d} | {s[3]:+d} | "
                         f"{s[4]:+d} | {s[5]:+.1f} | {'yes' if s[6] else 'NO'} "
                         f"| {s[7]} |\n")
        print(f"norm_sweep: wrote {args.markdown}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
