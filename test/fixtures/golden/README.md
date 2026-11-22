# Golden fixtures

Executable checks use in-house machinery. Historical Spot 2.16 results retain
their original provenance, receipts and hashes; running the checks requires no
external translation or synthesis installation.

## Verify

From the repository root, after the [build prerequisites](../../../README.md#build):

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
The default runs all suites. Scratch output must be under `build-sprint`;
`--output` overrides the default `build-sprint/oracle-retirement`.
The verifier never rewrites goldens or converts unsupported/error results into
verdicts.

| Evidence | Current check and limit |
| --- | --- |
| Formula membership | Independent direct fixed-point evaluation on words; DPA membership is reproduced byte for byte. |
| Random formulas | A separate seeded in-house corpus; historical streams remain frozen. |
| TV1/TVD1 automata | Lean language validation replays passing receipts with identical dump hashes. Historical timeouts/unsupported requests gain no new claim. |
| General LTL and finite/Moore verdicts | Frozen results; exact native reductions and certificate checks crosscheck supported infinite Mealy cases. |
| Native reduction/lift/API | Compare artifacts and run native checks; the retired independent differential is not renewed. |
| Normalization/conversion | Exact serialization plus sampled semantic equivalence. Sampling does not prove full equivalence. |
| Compose/pruning | Frozen verdicts/exports and current driver tests; unresolved residuals return UNKNOWN without a selected command. |

The direct evaluator imports no production parser, normalizer, DPA, BDD or
circuit simulator. Finite words are nonempty: plain X is weak, X[!] strong.
Native solvers/checkers share the reduction frontend, so they do not
independently validate parsing/normalization. See the [proof index](../../../proofs/README.md)
for theorem scope and the caller-trusted normalization premise in TVD1.

## Updating goldens

Review changed output and run the affected behavior checks before accepting
new hashes. Keep historical receipts and their claims; new evidence needs its
own origin and scope. Regenerate `MANIFEST.sha256` in the same PR and explain
why the output changed:

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

The manifest lists every fixture exactly once; the directory cap is 4,400,000
bytes including the manifest. Editing this guide also requires updating its
hash in `tools/golden/historical-files.json`. The external-oracle guard permits
historical names only in explicit hash-bound data. Proof references are checked
separately; no per-PR source-hash ledger is required.
