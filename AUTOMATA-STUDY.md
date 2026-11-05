# TLSF normalization and Acacia automata study

`scripts/automata_study.py` creates durable bundles at Acacia's formula-to-automaton
boundary, preserving its optional realizability simplifier, worker orientation,
interface BDD order, translator type/preferences/options, and state-based Büchi
conversion. Formula verdict shortcuts, safety-core witnesses, and decomposition
sit outside this boundary and need separate measurement. HOA replay does not
replace an end-to-end Acacia verdict. Production conversion and solver CLIs are
unchanged.

Build tlsf-tools with `-Dresearch_tools=true` and Acacia with
`-Dbuild_research_tools=true`, then run:

```sh
scripts/automata_study.py --file-list panel.list --output RUN \
  --tlsfnorm build/tlsfnorm --tlsf2ltl build/tlsf2ltl \
  --tlsfinfo build/tlsfinfo --tlsfbenchgraph build/tlsfbenchgraph \
  --automata-generator ../acacia-bonsai/build/src/acacia-automata-study
```

The default ladder is `off`; `split`; `split,nnf,weak,bool-canon`; `pre-safe`
plus `split,match-safe`; `split,route-safe`; and Sickert profiles bounded to
one/two iterations. Variants retain normalized TLSF/LTL, three oriented HOAs,
versioned metrics, source hash, and tool versions. Bundle schema 2 retains
failure/timeout rows (`generation_status`, elapsed time, bounded error), so one
orientation cannot discard a sweep. `source-features.tsv` is computed before
normalization/translation/solving: digests, interface sizes, and `guard_*` AST
measurements only, excluding template/residual measurements.

Selectors may use only `guard_*` and explicit TLSF metadata (such as I/O counts),
never paths, filenames, automaton metrics, or solver results. Production proposals
require zero losses/opposite verdicts on grouped holdouts, non-worse PAR-2, and
useful alternate-only wins in at least two families. No production selector is
included. The selected generator owns generation/replay; tlsf-tools passes files
and does not link to an external automata backend.
This workflow ends at bundle generation. External evaluation must separate
timeouts/resource limits/errors, detect conflicting verdicts, and report
losses/gains against `off`.
