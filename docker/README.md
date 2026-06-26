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

Both run `tlsf-solve --solver ltlsynt SPEC.tlsf` under the hood. `ltlsynt`,
`ltlfsynt`, and the stable preprocessing utilities
(`tlsfcompose`, `tlsfsolve`, `tlsfresidual`, `tlsfnorm`, `tlsf2ltl`,
`tlsf2tlsf`, `tlsfinfo`, `tlsf-solve`) are also on `PATH` for
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

## Soundness of output-free clusters

`--split` can produce *output-free* clusters (input-only system guarantees, e.g.
`G(a)` after `G(o && a)` splits into `G(o)` and `G(a)`).  These are **not**
dropped: each is realizability-checked via ltlsynt with all assumptions present
(the system has full control of any outputs the cluster references through
assumptions).  Unrealizable there soundly implies the whole spec is
unrealizable, so e.g. `G(o && a)` with `a` an input is correctly reported
`UNREALIZABLE`, while an input-only guarantee entailed by the assumptions stays
`REALIZABLE`.
