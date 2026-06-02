#!/usr/bin/env python3
"""Generate the aggregate plots and numbers behind BENCHGRAPH.md.

Runs `tlsfbenchgraph` over one or more TLSF corpora, aggregates the per-spec
metrics TSV, and writes a set of PNG plots plus a markdown stats snippet.  The
TSVs themselves are written to a temporary directory and discarded.

Usage:
    python3 scripts/benchgraph_plots.py \
        --benchgraph build/tlsfbenchgraph \
        --out docs/benchgraph \
        --wl 6 \
        ~/GIT-repos/benchmarks/tlsf:tlsf \
        ~/GIT-repos/benchmarks/tlsf-fin:tlsf-fin

Each positional argument is `DIR[:LABEL]` (LABEL defaults to the directory's
base name).  Requires matplotlib; everything else is stdlib.
"""
import argparse
import os
import subprocess
import sys
import tempfile
from statistics import median, mean

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

SHAPES = [
    "response", "mutex", "recurrence", "persistence", "guarded_next",
    "definition",
]


def run_benchgraph(benchgraph, corpus_dir, wl):
    """Run tlsfbenchgraph on a corpus dir; return list of row dicts."""
    with tempfile.TemporaryDirectory() as td:
        tsv = os.path.join(td, "m.tsv")
        cmd = [benchgraph, "--input-dir", corpus_dir, "--output", tsv]
        if wl:
            cmd += ["--wl", str(wl)]
        subprocess.run(cmd, check=True)
        rows = []
        with open(tsv) as f:
            header = f.readline().rstrip("\n").split("\t")
            for line in f:
                if line.startswith("#"):
                    continue
                vals = line.rstrip("\n").split("\t")
                rows.append(dict(zip(header, vals)))
    return rows


def col_int(rows, key):
    """Integer values of a column for parsed specs (skips '-')."""
    out = []
    for r in rows:
        v = r.get(key, "-")
        if v not in ("-", ""):
            out.append(int(v))
    return out


def aggregate(label, rows):
    parsed = [r for r in rows if r["parse_status"] == "ok"]
    n = len(rows)
    np = len(parsed)
    agg = {
        "label": label,
        "n": n,
        "parsed": np,
        "constraints": col_int(parsed, "constraints"),
        "inputs": col_int(parsed, "inputs"),
        "outputs": col_int(parsed, "outputs"),
        "safety": sum(col_int(parsed, "safety")),
        "liveness": sum(col_int(parsed, "liveness")),
        "solved_total": sum(col_int(parsed, "solved_blocks")),
        "certified_total": sum(col_int(parsed, "certified_blocks")),
        "specs_with_solved": sum(1 for r in parsed if int(r["solved_blocks"]) > 0),
        "wl_stab": col_int(parsed, "wl_stab_depth"),
        "comp": col_int(parsed, "largest_output_component"),
    }
    # per-shape: how many specs exhibit it, and total candidates
    for s in SHAPES:
        vals = col_int(parsed, s)
        agg[f"{s}_specs"] = sum(1 for v in vals if v > 0)
        agg[f"{s}_total"] = sum(vals)
    # formula reduction ratio (norm/raw) for specs with raw>0
    ratios = []
    for r in parsed:
        raw = int(r["formula_size_raw"])
        norm = int(r["formula_size_norm"])
        if raw > 0:
            ratios.append(norm / raw)
    agg["reduction_ratios"] = ratios
    return agg


# --------------------------------------------------------------------------
# Plots
# --------------------------------------------------------------------------

def plot_shape_prevalence(aggs, out):
    fig, ax = plt.subplots(figsize=(8, 4.2))
    width = 0.8 / len(aggs)
    x = range(len(SHAPES))
    for i, a in enumerate(aggs):
        pct = [100.0 * a[f"{s}_specs"] / a["parsed"] for s in SHAPES]
        ax.bar([xi + i * width for xi in x], pct, width, label=a["label"])
    ax.set_xticks([xi + width * (len(aggs) - 1) / 2 for xi in x])
    ax.set_xticklabels(SHAPES, rotation=20, ha="right")
    ax.set_ylabel("% of specs exhibiting the shape")
    ax.set_title("Template-shape prevalence")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(out, "shape_prevalence.png"), dpi=120)
    plt.close(fig)


def plot_constraints_hist(aggs, out):
    fig, ax = plt.subplots(figsize=(8, 4.2))
    maxc = max((max(a["constraints"]) for a in aggs if a["constraints"]),
               default=1)
    bins = [b for b in range(0, min(maxc, 60) + 2)]
    for a in aggs:
        ax.hist(a["constraints"], bins=bins, alpha=0.55, label=a["label"])
    ax.set_yscale("log")
    ax.set_xlabel("constraints per spec (clipped at 60)")
    ax.set_ylabel("# specs (log)")
    ax.set_title("Distribution of constraint count")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(out, "constraints_hist.png"), dpi=120)
    plt.close(fig)


def plot_coverage(aggs, out):
    fig, ax = plt.subplots(figsize=(7, 4.2))
    labels = [a["label"] for a in aggs]
    solved_pct = [100.0 * a["specs_with_solved"] / a["parsed"] for a in aggs]
    ax.bar(labels, solved_pct, color="#4c72b0")
    for i, a in enumerate(aggs):
        ax.text(i, solved_pct[i],
                f" {a['specs_with_solved']}/{a['parsed']}\n {a['solved_total']} blocks",
                va="bottom", ha="center", fontsize=9)
    ax.set_ylabel("% of specs with ≥1 SOLVED block")
    ax.set_title("Template-solvable coverage (current 4 certified templates)")
    ax.set_ylim(0, max(solved_pct + [1]) * 1.4)
    fig.tight_layout()
    fig.savefig(os.path.join(out, "coverage.png"), dpi=120)
    plt.close(fig)


def plot_reduction(aggs, out):
    fig, ax = plt.subplots(figsize=(8, 4.2))
    bins = [i / 10 for i in range(0, 31)]  # 0.0 .. 3.0
    for a in aggs:
        if a["reduction_ratios"]:
            clipped = [min(r, 3.0) for r in a["reduction_ratios"]]
            ax.hist(clipped, bins=bins, alpha=0.55, label=a["label"])
    ax.axvline(1.0, color="k", lw=0.8, ls="--")
    ax.set_xlabel("normalised / raw formula size (clipped at 3.0; 1.0 = no change)")
    ax.set_ylabel("# specs")
    ax.set_title("Formula size under --strong-simplify (normalisation, may grow)")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(out, "reduction.png"), dpi=120)
    plt.close(fig)


def plot_wl(aggs, out):
    if not any(a["wl_stab"] for a in aggs):
        return False
    fig, ax = plt.subplots(figsize=(7, 4.2))
    maxd = max((max(a["wl_stab"]) for a in aggs if a["wl_stab"]), default=1)
    bins = [b - 0.5 for b in range(0, maxd + 2)]
    for a in aggs:
        if a["wl_stab"]:
            ax.hist(a["wl_stab"], bins=bins, alpha=0.55, label=a["label"])
    ax.set_xlabel("WL stabilisation depth")
    ax.set_ylabel("# specs")
    ax.set_title("Weisfeiler-Lehman stabilisation depth")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(out, "wl_stab.png"), dpi=120)
    plt.close(fig)
    return True


# --------------------------------------------------------------------------

def stats_markdown(aggs, wl_ok):
    def fmt(xs):
        return f"{median(xs):.0f} / {mean(xs):.1f} / {max(xs)}" if xs else "-"

    lines = []
    lines.append("| corpus | specs | parsed | constraints (med/mean/max) | "
                 "inputs (med) | outputs (med) |")
    lines.append("|---|--:|--:|---|--:|--:|")
    for a in aggs:
        lines.append(
            f"| `{a['label']}` | {a['n']} | {a['parsed']} | {fmt(a['constraints'])} "
            f"| {median(a['inputs']):.0f} | {median(a['outputs']):.0f} |")
    lines.append("")
    lines.append("| corpus | " + " | ".join(SHAPES) + " |")
    lines.append("|---|" + "--:|" * len(SHAPES))
    for a in aggs:
        cells = [f"{a[f'{s}_specs']} ({a[f'{s}_total']})" for s in SHAPES]
        lines.append(f"| `{a['label']}` | " + " | ".join(cells) + " |")
    lines.append("")
    lines.append("_(cells: # specs with the shape, and total candidate count)_")
    lines.append("")
    lines.append("| corpus | safety | liveness | solved blocks | certified | "
                 "specs with a solved block | norm/raw size (med/mean) |")
    lines.append("|---|--:|--:|--:|--:|--:|--:|")
    for a in aggs:
        rr = a["reduction_ratios"]
        ratio = f"{median(rr):.2f} / {mean(rr):.2f}" if rr else "-"
        lines.append(
            f"| `{a['label']}` | {a['safety']} | {a['liveness']} | "
            f"{a['solved_total']} | {a['certified_total']} | "
            f"{a['specs_with_solved']} | {ratio} |")
    if wl_ok:
        lines.append("")
        lines.append("| corpus | WL stabilisation depth (med/mean/max) |")
        lines.append("|---|---|")
        for a in aggs:
            lines.append(f"| `{a['label']}` | {fmt(a['wl_stab'])} |")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--benchgraph", default="build/tlsfbenchgraph")
    ap.add_argument("--out", default="docs/benchgraph")
    ap.add_argument("--wl", type=int, default=6)
    ap.add_argument("corpora", nargs="+", help="DIR[:LABEL] ...")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    aggs = []
    for spec in args.corpora:
        d, _, label = spec.partition(":")
        label = label or os.path.basename(os.path.normpath(d))
        print(f"running benchgraph on {d} ({label}) ...", file=sys.stderr)
        rows = run_benchgraph(args.benchgraph, d, args.wl)
        aggs.append(aggregate(label, rows))

    plot_shape_prevalence(aggs, args.out)
    plot_constraints_hist(aggs, args.out)
    plot_coverage(aggs, args.out)
    plot_reduction(aggs, args.out)
    wl_ok = plot_wl(aggs, args.out)
    print(f"plots written to {args.out}/", file=sys.stderr)

    # Markdown stats to stdout (paste into BENCHGRAPH.md).
    print(stats_markdown(aggs, wl_ok))


if __name__ == "__main__":
    main()
