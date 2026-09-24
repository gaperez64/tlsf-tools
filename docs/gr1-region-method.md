# GR(1) relational region checking (`gr1-region-v1`)

`tlsfcertcheck --method region` verifies that a realizable system certificate
describes a total winning move relation.  It does not load, compile, or trust a
controller policy, and it does not call the GR(1) solver or recompute its
fixpoint.

```sh
tlsfcertcheck --method region --certificate certificate.aag game.aag
```

The certificate sidecar defaults to `certificate.aag.json`.  Successful
verification exits with status 0 and ends stdout with `REGION_VERIFIED`.  The
method identifier is `gr1-region-v1`; `--json-out` writes
`tlsf-gr1-region-checkresult-v1`.  A failed sufficient proof is
`REGION_FAILED` (exit 6), not an UNREAL verdict.  This method never emits
`UNREAL`, `REFUTED`, or an environment counter-strategy.  `auto`,
`certificate`, `closed-loop`, and `both` retain their existing policy-based
interfaces and results.

## Arena and timing

Let `s` be the complete sampled game state, `u` the current uncontrollable
letter, and `c` one current controllable letter.  The AIG defines the
deterministic successor `T(s,u,c)` and unsafe predicate `Bad(s,u,c)`.  Before
checking, input-dependent justice and fairness literals are converted by the
existing acceptance-sampling transformation into reset-0 state latches.  Thus
the predicates below are state predicates:

- `W(s)` is certificate output `inv`;
- `G_j(s)` is flattened game justice goal `j`;
- `F_i(s)` is game fairness assumption `i`;
- `Y[j,k](s)` and `X[j,k,i](s)` are the cumulative rank predicates.

Justice is sampled in the current state.  In particular, the goal counter
advances after a step whose current state satisfies `G_j(s)`.  Fairness in the
rank-stuttering clause is sampled at the successor: it is
`F_i(T(s,u,c))`, not `F_i(s)`.  These conventions also cover acceptance that
originally depended on the current input letter, because its sampling latch at
the successor contains that letter's value.  When the game has no fairness
assumptions, the single synthetic disjunct behaves as `F_0 = true`, so rank
stuttering is unavailable.

The scheduler modes are checked independently in this order:

1. the all-zero reset encoding, interpreted as goal 0;
2. one-hot goal 0;
3. each remaining one-hot goal.

All-zero and one-hot goal 0 intrinsically have the same `gr1-region-v1`
logical obligation.  The policy-free `Good_j` interface contains game state,
uncontrollable inputs, and the complete controllable vector, but no policy or
counter input.  Both encodings select `j = 0`, and therefore produce the same
goal/rank layers and the same `Good_0` predicate.  They cannot be distinguished
by a behavioral mutation without adding a counter-dependent policy premise.
They nevertheless remain separate checks and separate statistics, so the
reset convention and every explicit scheduler mode are both covered.  The
deterministic counter update is: stay at `j` when `G_j(s)` is false, and advance
to `(j+1) mod J` when `G_j(s)` is true.  The counter is strategy memory, not
part of the certificate's move relation.

## Validated certificate shape

The checker first validates the full AIG structure and the complete existing
`tlsf-gr1-certificate-v1` interface.  It then establishes all of the following
semantically:

- `W`, every `Y[j,k]`, and every `X[j,k,i]` is independent of `u` and `c`;
- certificate `goal_j` equals the corresponding predicate compiled from the
  actual game;
- `Y[j,k]` is exactly the union of `X[j,k,i]` over `i`;
- the `Y` levels are monotone in `k`;
- every state in `W` is covered by an `X` predicate for every goal;
- the concrete reset state belongs to `W`.

Every latch reset in the game, policy (when another method supplies one), and
certificate must be the constant `0` or `1`.  A self-literal/uninitialized
reset or any other nonconstant reset is unsupported and yields `INVALID`, as
it does in `tlsfsolve`; it is never coerced to a Boolean reset value.  The
region reset-membership check therefore always concerns one concrete game
state.

Ranks use the documented least lexicographic convention.  Goal states are
handled first.  For a non-goal state, `(k,i)` is selected only in the disjoint
layer

```text
L[j,k,i] = W & X[j,k,i] &
           !(G_j | every X[j,k',i'] with (k',i') <lex (k,i)).
```

The certificate's `move_*` outputs are not used, even as hints.  Their names
and circuits remain structurally validated as part of the certificate
interface, but their Boolean cones are not selected as BDD roots.  The method
instead selects exactly the game latch updates, safety properties, justice and
fairness predicates, plus certificate `inv`, `goal_*`, `Y`, and `X` roots.  It
uses the shared selected-root builder, so irrelevant exclusive `move_*` cones
are not evaluated.

## Joint allowed-move obligation

For scheduler goal `j`, define

```text
SafeInv(s,u,c) = !Bad(s,u,c) & W(T(s,u,c)).
```

At a current goal state,

```text
Good_j(s,u,c) = SafeInv(s,u,c).
```

At a state in least-rank layer `L[j,k,i]`,

```text
Good_j(s,u,c) = SafeInv(s,u,c) &
  ( G_j(T(s,u,c))
    | (k > 0 & Y[j,k-1](T(s,u,c)))
    | (X[j,k,i](T(s,u,c)) & !F_i(T(s,u,c))) ).
```

For every goal layer and disjoint rank layer, the checker proves

```text
forall s in that layer, forall u: exists c. Good_j(s,u,c).
```

The existential quantifier is applied only after constructing the complete
conjunction.  Consequently, a safe choice, an invariant-preserving choice,
and a progressing choice must be one and the same `c`.  Separate witnesses for
the conjuncts cannot pass.  Successor substitution objects and the images of
`W`, `G_j`, `F_i`, and lower `Y` levels are reused within each mode.

## Why the obligations are sufficient

Assume a finite deterministic AIG game with the usual Mealy move order: the
environment supplies `u`, then the system may choose `c` as a function of the
current sampled state, scheduler mode, and `u`.  Also assume the AIG reset and
acceptance-sampling transformation have their documented semantics.

The checked existential obligation supplies at least one control for every
triple `(s,j,u)` with `s` in `W`.  Because the arena is finite, choosing one
such control for every triple defines a strategy on the augmented state
`(s,j)`.  `SafeInv` makes every resulting transition safe and keeps the play in
`W`.

Fix a scheduler goal `j` while its current-state justice predicate remains
false.  The least rank of the current state cannot increase.  A transition may
reach `G_j`, decrease `k`, or remain within the selected `X[j,k,i]`; the last
case is allowed only when `F_i` is false at the successor.  In a play satisfying
every environment fairness assumption infinitely often, a fixed least rank
cannot stutter forever.  The finite lexicographic rank therefore decreases
only finitely many times before `G_j` is reached.  On that current goal state,
the checked counter convention advances to the next goal while `SafeInv`
preserves the region.  Repeating the argument around the finite counter proves
that every system justice goal occurs infinitely often on every fair play.
Hence the selected controls form a winning strategy, although this method does
not construct or export its circuit.

## Diagnostics and resources

`--stats` retains the general `TLSFCERTCHECK_STATS` line and adds selected game
and certificate root counts, mode/layer counts, and aggregate mode/layer time.
It also emits one `TLSFCERTCHECK_REGION_MODE` record per scheduler mode and one
`TLSFCERTCHECK_REGION_LAYER` record per checked goal/rank layer.  Timeout, BDD
capacity failure, invalid mapping, or another resource failure yields
`UNKNOWN`; none is converted into a proof result.
