#!/usr/bin/env python3
"""Test double for the external Acacia automata generator protocol."""

from __future__ import annotations

import argparse
import pathlib


parser = argparse.ArgumentParser()
parser.add_argument("--formula", type=pathlib.Path)
parser.add_argument("--hoa", type=pathlib.Path)
parser.add_argument("--name", default="-")
parser.add_argument("--schedule", default="off")
parser.add_argument("--inputs", default="")
parser.add_argument("--outputs", default="")
parser.add_argument("--orientation", default="real")
parser.add_argument("--preference", default="small")
parser.add_argument("--realizability-simplify", action="store_true")
parser.add_argument("--no-header", action="store_true")
parser.add_argument("--version", action="store_true")
args = parser.parse_args()

if args.version:
    print("fake-automata-generator 1")
    raise SystemExit(0)
if args.formula is None or args.hoa is None:
    parser.error("--formula and --hoa are required")

args.hoa.write_text(
    "HOA: v1\n"
    "States: 1\n"
    "Start: 0\n"
    "AP: 0\n"
    "acc-name: Buchi\n"
    "Acceptance: 1 Inf(0)\n"
    "properties: state-acc\n"
    "--BODY--\n"
    "State: 0 {0}\n"
    "[t] 0\n"
    "--END--\n",
    encoding="utf-8",
)
fields = (
    "schema_version\tname\tschedule\torientation\tpreference\tinputs\t"
    "outputs\tformula_nodes\tstates\tedges\tacceptance_sets\tsccs\t"
    "state_acc\tdeterministic\tcomplete\tuniversal\thoa"
)
if not args.no_header:
    print(fields)
print(
    f"1\t{args.name}\t{args.schedule}\t{args.orientation}\t"
    f"{args.preference}\t{args.inputs}\t{args.outputs}\t1\t1\t1\t1\t1\t"
    f"1\t1\t1\t0\t{args.hoa}"
)
