# TLSF normalization and Acacia automata study

This research path keeps production conversion and solver CLIs unchanged. It
creates durable bundles at Acacia's formula-to-automaton boundary: the same
optional realizability simplifier, worker orientation, interface BDD ordering,
translator type/preferences/options, and state-based Büchi conversion.
Formula-level verdict shortcuts, safety-core witnesses, and formula
decomposition happen outside this boundary and must be measured separately;
an HOA replay result is not a replacement for an end-to-end Acacia verdict.

`tlsf-tools` does not link to Spot or expose Spot types in this workflow.  The
orchestrator translates TLSF into ordinary TLSF/LTL files and invokes an
external automaton generator; Acacia owns the Spot-dependent generator and
replay adapters used below.  The existing `tlsf2spot` program remains only an
example consumer of the public tlsf-tools representation.

Build `tlsf-tools` with `-Dresearch_tools=true` and Acacia with
`-Dbuild_research_tools=true`, then run:

```sh
scripts/automata_study.py --file-list panel.list --output RUN \
  --tlsfnorm build/tlsfnorm --tlsf2ltl build/tlsf2ltl \
  --tlsfinfo build/tlsfinfo --tlsfbenchgraph build/tlsfbenchgraph \
  --automata-generator ../acacia-bonsai/build/src/acacia-automata-study

scripts/evaluate_automata_study.py --bundle RUN --output RESULTS \
  --acacia-replay ../acacia-bonsai/build/src/acacia-hoa-replay \
  --timeout 20 --repetitions 1
```

The default schedule ladder is `off`; `split`; `split,nnf,weak,bool-canon`;
`pre-safe` plus `split,match-safe`; `split,route-safe`; and bounded Sickert
profiles at one and two iterations. Each variant retains its normalized TLSF,
LTL, three worker-orientation HOA files, a versioned metrics row, source hash,
and tool versions.

Translation failures and timeouts are first-class manifest rows in bundle
schema 2.  They carry `generation_status`, elapsed time, and a bounded error
message; one difficult orientation therefore cannot discard the rest of a
corpus sweep.
Each bundle also contains `source-features.tsv`, computed before and
independently of normalization, translation, and solving.  That table contains
only source digests, interface sizes, and `guard_*` AST measurements; derived
template and residual measurements are excluded by construction.

The replay orchestrator uses one memory-limited user-systemd scope per run,
persists every sample atomically, distinguishes timeouts, resource limits, and
other errors, detects simultaneous real/unreal wins as a hard conflict, and
reports losses/gains relative to the `off` schedule.
Resume mode verifies the script, binaries, bundle, schedules, resource limits,
and other run metadata before appending, so incompatible samples cannot be
silently mixed.

Offline selectors may use only `guard_*` fields from `tlsfbenchgraph` plus
explicit TLSF metadata such as input/output counts. They must not use paths,
filenames, automaton metrics, or solver results. A selector is eligible for a
later production proposal only with zero losses/opposite verdicts on grouped
holdouts, non-worse PAR-2, and useful alternate-only wins across at least two
families. This PR deliberately does not add such a production selector.
