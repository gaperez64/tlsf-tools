# Automata study

Build tlsf-tools with `-Dresearch_tools=true` and Acacia with
`-Dbuild_research_tools=true`, then run:

```sh
scripts/automata_study.py --file-list panel.list --output RUN \
  --tlsfnorm build-research/tlsfnorm --tlsf2ltl build-research/tlsf2ltl \
  --tlsfinfo build-research/tlsfinfo --tlsfbenchgraph build-research/tlsfbenchgraph \
  --automata-generator /path/to/acacia-research-build/src/acacia-automata-study
```

Each variant saves normalized TLSF/LTL, three oriented HOAs, versioned metrics,
source hash and tool versions. Schema 2 retains failed and timed-out rows.
The default schedules range from `off` through split, normalization and bounded
Sickert profiles. The selected generator handles generation and replay.
HOA replay does not establish an end-to-end synthesis verdict.

`source-features.tsv` contains digests, interface sizes and `guard_*` AST
measurements taken before normalization, translation or solving. Selectors may
use only `guard_*` and explicit TLSF metadata, excluding filenames, paths,
automaton metrics and solver results. Compare losses/gains against `off`,
separate timeouts, resource limits and errors, and detect conflicting verdicts.
