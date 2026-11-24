# GR(1) system region certificates

```sh
tlsfcertcheck --method region --certificate certificate.aag game.aag
```

The sidecar defaults to `certificate.aag.json`. The checker validates a total
winning move relation without a controller policy or solver fixpoint.
Success prints `REGION_VERIFIED` and exits 0; a failed sufficient proof prints
`REGION_FAILED` and exits 6. Resource failures yield `UNKNOWN`.
`--json-out` writes `tlsf-gr1-region-checkresult-v1`.
The method exports no controller or environment counterstrategy.

## Certificate format

The checker validates the AIG and `tlsf-gr1-certificate-v1` interface.
All game/artifact latch resets must be constant 0/1; other resets are `INVALID`.
For state `s`, environment input `u` and system control `c`, the game defines
successor `T(s,u,c)` and `Bad(s,u,c)`.

| Predicate | Meaning |
|---|---|
| `W(s)` | Certificate `inv`. |
| `G_j(s)` | Flattened game justice goal `j`. |
| `F_i(s)` | Game fairness assumption `i`. |
| `Y[j,k](s)`, `X[j,k,i](s)` | Cumulative rank predicates. |

Input-dependent acceptance uses reset-0 sampling latches. Goals use current
state; stuttering uses successor fairness, which holds the current input's
value. With no fairness, synthetic `F_0 = true` disables stuttering.

The checker requires state-only W/Y/X, certificate goals equal to game goals,
Y equal to the union of its X lanes and monotone in k, X covering W for every
goal, and concrete reset membership in W. `move_*` circuits are structurally
validated but their values are unused.

## Move obligations

Goal states take precedence; otherwise choose the least lexicographic rank:

```text
L[j,k,i] = W & X[j,k,i] &
           !(G_j | every X[j,k',i'] with (k',i') <lex (k,i)).
```

```text
SafeInv(s,u,c) = !Bad(s,u,c) & W(T(s,u,c)).

At a current goal state:
Good_j(s,u,c) = SafeInv(s,u,c).

In least-rank layer L[j,k,i]:
Good_j(s,u,c) = SafeInv(s,u,c) &
  ( G_j(T(s,u,c))
    | (k > 0 & Y[j,k-1](T(s,u,c)))
    | (X[j,k,i](T(s,u,c)) & !F_i(T(s,u,c))) ).

For every goal layer and disjoint rank layer:
forall s in that layer, forall u: exists c. Good_j(s,u,c).
```

One control must satisfy safety, invariance and progress together. The scheduler
starts at goal 0 and advances after current-state satisfaction of that goal.
All-zero reset and each one-hot mode are checked separately. `--stats` reports
selected roots, modes/layers and timings in `TLSFCERTCHECK_STATS`,
`TLSFCERTCHECK_REGION_MODE` and `TLSFCERTCHECK_REGION_LAYER` records.

`Tlsf.Gr1.region_conditions_sound` proves the mathematical method;
see the [proof index](../proofs/README.md#gr1-region-certificates).
C execution, BDDs, AIG evaluation and TLSF-to-game reduction remain trusted.

## Lift candidates

After ordinary element-axis discovery declines, the lift API can propose
monitor folds from proved logarithmic encoding widths (route A), then
parametric-support folds over ordinary element buses (route B).
Route A folds monitor-state disjunctions, optionally excluding a uniquely
identified transient state. Route B requires whole element domains with
constant exclusions, unique state transports and exact seed reconstruction.
Neither route proves a cutoff: every REAL result requires `REGION_VERIFIED`
on the unchanged, source-bound concrete target.

Discovery, seed solving and checking share probe, deadline and RSS budgets.
Limits are cooperative; individual libc/I/O calls are not preempted.
Fold evidence records source bindings, seeds, mappings and `checker_order`.
Capacity failures may retry the other BDD order with the remaining budget;
semantic failures do not. Diagnostics are in `decline_detail` (`fold_*` and
`param_*` reasons). See [gr1_lift.h](../include/tlsf/gr1_lift.h).
