# Normalization schedule sweep

Structural/certification sweep of 2545 specs from `benchmarks/tlsf` at `6c56b55`, without a solver. Rank only soundness-eligible rows (no new parse failures).

| schedule | cand Δ | certified Δ | solved Δ | elim Δ | growth % | eligible | recommendation |
|---|--:|--:|--:|--:|--:|:--:|---|
| `off` | +0 | +0 | +0 | +0 | +0.0 | yes | baseline |
| `match-safe:1` | +23 | +18 | -57 | -57 | +0.0 | yes | review (solved/elim regressed; verify with solver) |
| `match-safe:2` | +23 | +18 | -57 | -57 | +0.0 | yes | review (solved/elim regressed; verify with solver) |
| `pre-safe:1+match-safe:1` | +23 | +18 | -57 | -57 | +0.0 | yes | review (solved/elim regressed; verify with solver) |
| `route-safe:1` | -658 | -14 | -349 | -222 | +0.0 | yes | review (solved/elim regressed; verify with solver) |
