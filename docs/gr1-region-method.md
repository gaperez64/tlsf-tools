# GR(1) relational region checking (`gr1-region-v1`)

`tlsfcertcheck --method region` checks that a realizable system certificate
describes a total winning move relation, without loading, compiling, or trusting
a controller policy, calling the GR(1) solver, or recomputing its fixpoint.

```sh
tlsfcertcheck --method region --certificate certificate.aag game.aag
```

The sidecar defaults to `certificate.aag.json`. Success exits 0 with final
stdout `REGION_VERIFIED`; a failed sufficient proof is `REGION_FAILED` (exit 6).
It never emits `UNREAL`, `REFUTED`, or an environment counter-strategy.
`--json-out` writes `tlsf-gr1-region-checkresult-v1`. Other methods (`auto`,
`certificate`, `closed-loop`, `both`) retain their policy-based interfaces/results.

## Arena and certificate

For sampled state `s`, current uncontrollable letter `u`, and one controllable
letter `c`, the AIG defines successor `T(s,u,c)` and `Bad(s,u,c)`. Acceptance
sampling converts input-dependent justice/fairness into reset-0 state latches:

| Predicate | Meaning |
|---|---|
| `W(s)` | Certificate `inv`. |
| `G_j(s)` | Flattened game justice goal `j`. |
| `F_i(s)` | Game fairness assumption `i`. |
| `Y[j,k](s)`, `X[j,k,i](s)` | Cumulative rank predicates. |

Justice uses the current state; the goal counter advances after `G_j(s)`.
Rank stuttering uses successor fairness `F_i(T(s,u,c))`, whose sampling latch
holds the current input's value. With no fairness assumptions, synthetic
`F_0 = true` makes rank stuttering unavailable.

Scheduler modes are checked separately: all-zero reset (goal 0), one-hot goal 0,
then each remaining one-hot goal. The first two have identical obligations:
`Good_0` depends on game state and full input/control vectors, without policy
or counter inputs. They cannot be distinguished by behavioral mutation without
a counter-dependent policy premise, but retain separate checks/statistics.
The counter stays at `j` unless `G_j(s)`, then advances to `(j+1) mod J`.
It is strategy memory outside the move relation.

The checker validates the full AIG and `tlsf-gr1-certificate-v1` interface, then
checks these semantic conditions:

- `W`, `Y`, and `X` are independent of `u` and `c`.
- Certificate `goal_j` equals the actual game's goal predicate.
- `Y[j,k]` is exactly the union of `X[j,k,i]` over `i`, monotone in `k`.
- For every goal, `X` predicates cover `W`; the concrete reset lies in `W`.

Game, certificate, and any policy supplied to another method need constant
0/1 latch resets. Self-literal/uninitialized or other nonconstant resets yield
`INVALID`, as in `tlsfsolve`; they are never coerced to Boolean values.

Goal states take precedence. Other states use the least lexicographic rank:

```text
L[j,k,i] = W & X[j,k,i] &
           !(G_j | every X[j,k',i'] with (k',i') <lex (k,i)).
```

`move_*` names/circuits are structurally validated but never used as hints or
selected BDD roots. The shared selected-root builder evaluates only game latch
updates, safety, justice/fairness, and certificate `inv`, `goal_*`, `Y`, and `X`;
irrelevant exclusive move cones are skipped.

## Allowed moves and sufficiency

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

Existential quantification follows the complete conjunction: one `c` must
satisfy safety, invariance, and progress together. Each mode reuses successor
substitutions and images of `W`, `G_j`, `F_i`, and lower `Y` levels.

Assume a finite deterministic AIG arena with Mealy order (environment `u`,
then system `c`) and the documented reset/acceptance-sampling semantics.
Totality supplies a control for each `(s,j,u)` in `W`; finite choice defines
a strategy on `(s,j)`. `SafeInv` preserves safety and `W`.

While `G_j` is false, least rank cannot increase: a step reaches the goal,
decreases `k`, or stays in the selected `X[j,k,i]` with successor `F_i` false.
A fair play cannot stutter at a fixed least rank forever. Finite lexicographic
rank therefore forces `G_j`, where the counter advances safely. Repeating
around the finite counter visits every system justice infinitely often on
fair plays. This proves a winning strategy exists; the method exports no circuit.

`--stats` adds selected-root counts, mode/layer counts and aggregate time to
`TLSFCERTCHECK_STATS`, plus one `TLSFCERTCHECK_REGION_MODE` per mode and
`TLSFCERTCHECK_REGION_LAYER` per checked layer. Timeouts, BDD capacity failures,
invalid mappings, and other resource failures yield `UNKNOWN`, never a proof result.
