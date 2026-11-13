# Golden integration fixtures

All executable checks and offline tools use in-house machinery. No external
translation or synthesis installation, Python bindings, or setup is used.
Historical Spot 2.16 evidence remains frozen data: its origin, dates, versions,
source hashes, receipts and payloads are preserved exactly. It is never relabeled
as an in-house result. `provenance.json` and `tool-versions.json` describe that
historical evidence, not prerequisites for running today's tools.

## Reproduce and verify

From the repository root, with one heavy job at a time:

```sh
mkdir -p build-sprint/tmp
export TMPDIR="$PWD/build-sprint/tmp" CARGO_BUILD_JOBS=1
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=2048 LEAN_MAIN_USE_THREAD=0
export PATH="$HOME/.elan/bin:$PATH"
meson setup build-sprint/release --buildtype=release -Dresearch_tools=true
ninja -C build-sprint/release -j1
python3 tools/golden/test_gates.py
python3 tools/golden/regenerate.py --build build-sprint/release --translation
meson test -C build-sprint/release --no-rebuild --num-processes 1 --print-errorlogs
```

Lean 4.35.0 is needed only for `--translation`. `--only` selects `dpa`, `exports`,
`pruning`, `native`, `language`, `monitor`, `lift`, `norm`, `api`, or `step1`.
The default runs all suites. Output goes to `build-sprint/oracle-retirement`;
`--output` may select another directory under `build-sprint`. The verifier
fingerprints all golden files before and after and never writes to this directory.
There is no recording switch. Failure, timeout, unsupported syntax, or missing
certificate evidence never creates a verdict or new golden.

## Independence and frozen suites

| Suite/use | Current check and reproducibility |
| --- | --- |
| `dpa/membership.tsv` | `reference.py` parses the original formulas independently and evaluates all 512 lassos per formula by direct least/greatest fixed points on word positions. It also evaluates the archived prefix AST independently. Every membership bit is reproduced; the original AST serialization and historical formula/word corpus stay frozen. The complete file is reconstructed into scratch and compared byte for byte. |
| Random formulas / former filtering | The historical random and Delta₂ text files are frozen. A seeded in-house generator writes a separate fresh safety/recurrence/product corpus and direct-semantic membership table into scratch, then runs the native DPA harness against it. No historical random stream is silently replaced. |
| Native-language, monitor and disjoint-assumptions memberships | All committed membership rows are rederived by the independent direct evaluator; native AAG evaluations must agree. These membership expectations are regenerable. |
| Automaton translation / Pi₂ converse search | The C dumper and Lean validator check completed automata against formula semantics with kernel-checked translation-validation theorems. `--translation` replays every passing TV1/TVD1 request, requiring the same dump hash, without rewriting receipts. `dpa_pi2_converse.py --build ... --output build-sprint/pi2` applies the same checker to its bounded corpus; unsupported/timeouts remain unknown. |
| General LTL and finite/Moore realizability | Frozen historical verdicts only. The verifier additionally attempts exact native reductions, OxiDD solving, system region proofs and dual environment certificate/counterstrategy checks for infinite Mealy cases. Unsupported cases remain unknown; even successful crosschecks do not replace historical provenance. |
| Native reduction and lift | Historical differential recordings remain verify-only. The original reducer/prototype is retired. Current artifacts/dispositions are compared with committed data, alongside native game, ownership, provenance and certificate checks. This does not renew the old independent differential. |
| Normalization / conversion | Native serialization is reproduced exactly; original and transformed objectives are sampled on deterministic lassos with the independent evaluator. Historical exact equivalence claims stay frozen: sampling does not establish full equivalence. |
| Compose / review4 exports | Historical verdicts, formula bytes and controller exports remain frozen and checked. The old generated driver snapshots are hash-verified historical data only. Current generated drivers return UNKNOWN for unresolved residuals without a selected command, and use `.formula` instead of the historical backend-specific suffix. Separate tests execute current drivers with a protocol stub and exercise UNKNOWN/error handling. |
| Assumption pruning | All 63 historical verdicts and 85 export records remain verify-only. The archived source migration is checked by stripping only DESCRIPTION and comparing the complete emitted ordinary/strict objectives byte for byte. |
| `native-api-8b158d7` | Frozen API/CLI differential; replay compares the current native outputs with committed expectations and runs native verification. |

The direct evaluator imports no production parser, normalizer, DPA constructor,
BDD package, or circuit simulator. Its finite semantics require nonempty words:
plain X is weak, X[!] is strong; F/U/M are least fixed points and G/R/W greatest
fixed points. Finite-word and lasso tests cover every temporal operator and
boundary. Bounded membership/equivalence sampling is regression evidence only.

The OxiDD solver and certificate checkers use the native reduction frontend;
they are independent checks of game obligations, not independent parsing or
normalization. The explicit GR(1) differential and `test/gr1_one_step.c` supply
additional independent game checks. Declines are not inferred to be losing.

## Translation receipts and trust

[translation/report.json](translation/report.json) records the original complete
TV1 run, including censored timeouts; only passes entered `hashes.tsv`. There
are 4,134 passing TV1 requests and a separate 68-pass, four-unsupported TVD1
receipt in [translation/dag](translation/dag). Replaying the passing rows does
not renew timed-out or unsupported claims. The original dates and executable,
source and corpus hashes remain historical.

Lean proves the executable reference and the per-instance translation checker.
Runtime formulas without a validated receipt rely on the reference and sample,
not a universal proof of C refinement. C memory safety, BDD refinement, compiler
correctness, caller extraction of the whole objective, and caller normalization
remain separate obligations. TVD1 explicitly records its caller-trusted
normalization premise. See [proofs/README.md](../../../proofs/README.md).

The [retirement report](../../../tools/analysis/oracle-retirement-report.txt)
records the replacement checks and their scope. Its source-binding ledger is
[historical data](../../../tools/analysis/history/oracle-retirement.json);
current source changes do not require rebinding ledgers. Historical source
hashes in receipts describe the original run, not today's source tree.

`check_no_external_oracles.py` scans tools, scripts, bench, tests, production
sources, examples and build declarations. Only explicit frozen provenance/data
paths may contain historical names. Their bytes are hash-bound; executable
imports/includes/discovery/commands are forbidden throughout executable source.
`check_golden_provenance.py` checks that every file in this directory except
`MANIFEST.sha256` is listed exactly once in that manifest, verifies every
SHA-256, and limits the whole directory, including the manifest, to 4,400,000
bytes (the owner's 4.4 MB cap). The proof-source and external-oracle guards
remain separate checks.

## Updating goldens

When a golden changes, regenerate `MANIFEST.sha256` in the same PR and include
a note explaining why the output changed. Review the output difference and
run the affected behaviour checks before accepting the new hashes. Preserve
historical receipts and their original claims; new evidence must describe its
own origin and scope. Do not add a per-PR source-hash ledger.

From the repository root, after the intended golden edits:

```sh
python3 - <<'PY'
import hashlib
from pathlib import Path

root = Path("test/fixtures/golden")
manifest = root / "MANIFEST.sha256"
files = sorted(p for p in root.rglob("*") if p.is_file() and p != manifest)
manifest.write_text("".join(
    f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(root)}\n"
    for p in files))
PY
python3 test/cli/check_golden_provenance.py .
```

The external-oracle guard also binds frozen historical data and this guide in
`tools/golden/historical-files.json`; update its entry when editing this guide.
