# spot-syntcomp image

A SYNTCOMP image bundling **ltlsynt / ltlfsynt** (from Spot) with the
**tlsf-tools decomposed-synthesis preprocessor** (templates + in-process OxiDD
safety/GR(1) solvers). The preprocessor carves clusters off a TLSF spec and
forwards only the hard liveness residual to `ltlsynt`.

It derives from the upstream
[`spot-syntcomp`](https://gitlab.lre.epita.fr/spot/syntcomp25) image (the Spot
build stage mirrors it) and adds OxiDD + the preprocessor utilities.

## Entry points

All take a TLSF file and follow the SYNTCOMP contract (`REALIZABLE` /
`UNREALIZABLE` on stdout; for synthesis, the AIGER controller follows
`REALIZABLE`):

| Command | Track | Output |
|---|---|---|
| `spot-syntcomp-syn  SPEC.tlsf` | synthesis | `REALIZABLE` + AIGER, or `UNREALIZABLE` |
| `spot-syntcomp-real SPEC.tlsf` | realizability | `REALIZABLE` / `UNREALIZABLE` |

Both run `tlsfcompose --split --aiger --ltlsynt ltlsynt SPEC.tlsf` under the
hood. `ltlsynt`, `ltlfsynt`, and the preprocessing utilities (`tlsfgraph`,
`tlsfresidual`, `tlsftemplates`, `tlsf2ltl`, …) are also on `PATH` for the
non-preprocessed configs.

Exit codes: `0` realizable, `1` unrealizable, `2` inconclusive (backend
failure/timeout — no verdict claimed).

## Usage

```sh
# Pull (published by the CD workflow on a version tag):
docker pull ghcr.io/gaperez64/spot-syntcomp:latest

# Synthesize a controller:
docker run --rm -v "$PWD:/work" -w /work \
  ghcr.io/gaperez64/spot-syntcomp:latest spot-syntcomp-syn spec.tlsf

# Realizability only:
docker run --rm -v "$PWD:/work" -w /work \
  ghcr.io/gaperez64/spot-syntcomp:latest spot-syntcomp-real spec.tlsf
```

## Building locally

From the repo root, with the OxiDD submodule checked out
(`git submodule update --init --recursive external/oxidd`):

```sh
docker build -f docker/Dockerfile -t spot-syntcomp .
```

Build args: `SPOT_VERSION` (default `2.15.1`).

## Caveat (preprocessor soundness)

The `--split` decomposition currently skips *output-free* clusters
unconditionally (`src/main_tlsfcompose.c`). That is sound for environment
assumptions but **unsound for input-only guarantees not entailed by the
assumptions** — such a spec can be reported `REALIZABLE` when it is not (e.g.
`G(o && a)` with `a` an input). This is the known "output-free assumption
cluster" gap tracked in `BENCHGRAPH.md`; fixing it needs an entailment check.
Keep this in mind before relying on the image for unrealizable instances.
