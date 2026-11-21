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

## Encoded monitor-fold candidates (route A)

The native system lift first runs its existing element-axis discovery unchanged.
Only after it finds no window, and encounters `axis/encoding_width` for a
changing frontend `representation-bit` declaration with
`proved-logarithmic-encoding` provenance and the selected parameter ID, it tries
`monitor-fold-v1`. Unproved widths keep the old decline behavior. This rule uses
no benchmark names, identifier spellings, decoder templates, or state ordinals.

A schema key contains the source formula/node occurrence, generator binder IDs,
side, role and monitor class. It deliberately excludes concrete code patterns
and state counts. The source-bound inventory supplies each instance's latches.
The grammar consists of constants and conjunctions of these schema folds:

```text
Live(schema) = AND monitor instances m: OR state latches q of m: q
LiveExcept(schema) = AND m: OR q other than the tagged transient state: q
```

`LiveExcept` is available only when each instance has exactly one latch with
reset 1 and constant-0 next literal. `Live` includes multi-hot states; it does
not assume reachable or one-hot valuations.

Seed selection uses relative encoding-width profiles, rather than treating bit
positions as clients. It searches sizes 3..9, bounded by `max_sizes_per_axis`
new probes and a `max_seed_probes` allowance shared by routes A and B.
Legacy discovery and the U window keep main's name-sorted parameter order and
trace, including unused-axis probes. This can cost extra seed solves before a
fold fallback runs: on the n=6 fixture, adding `a=6;` and an unused input bus
`auxiliary[a];` costs six seed solves, versus three when `a` is renamed to `z`.
This known legacy-order cost cannot affect soundness: every fold candidate still
requires target `REGION_VERIFIED`. Legacy spending cannot exhaust the fallback
allowance; both phases still share the arm's deadline and RSS limits. Public
probe/reduction totals include all actual work. Fold evidence separately records
`discovery_probes` and usable `discovery_reductions`, including cached probes
reused by route B, so these fallback counters are invariant under irrelevant
parameter renaming.

Fallback axes come only from complete frontend width dependencies of element
buses (route B) or proved logarithmic representation widths (route A). The
existing route A width proof also admits recursive width definitions, whose
general dependency-completeness flag is conservative. Axes are ordered by
multisets of declaration shapes and monitor/generator incidence, excluding
names and numeric source/declaration IDs. Route A and route B axis selection is
therefore name-independent. Structurally indistinguishable axes are declined
with `fold_axis_ambiguous` or `param_axis_ambiguous`, rather than ordered by
spelling. These routes require a changing bus extent; support-only
parameters without an extent dependency cannot supply their coordinate domain.

Equal-width profiles prefer a common concrete plateau (normally 5/6/7);
unequal-width profiles require two different-width witnesses (normally 4/8). Thus power-of-two
witnesses need not be consecutive. Sizes 1/2 are excluded from fold learning.
This bounded search can decline other families with `fold_insufficient_strata`.
Seed reduction, solving, learning and checking all consume the arm's existing
deadline and live RSS budget; no target solve occurs in this candidate rule.

The existing solver supplies per-source-goal rank depths and predicates.
For W and every X level/fairness lane, the learner keeps the conjunction of
grammar atoms implied by every corresponding solved predicate. Y is the union
of X lanes. This can overapproximate a solver predicate. Consequently the
entire proposed certificate must pass **each seed's region check**, even when
it reconstructs the solved predicates exactly. Evidence records full-state-space
BDD equality as `exact_predicates`, plus seed values, width profiles, game
hashes, source occurrences, bindings and latch mappings. Region validation is
the acceptance criterion: the prototype's folded sufficient ranks need not
reproduce every redundant intermediate solver predicate. A rejected seed gives
`fold_seed_mismatch`; it does not justify a target verdict.

Instantiation uses the target's actual monitor inventories and justice predicates;
the unchanged target game supplies its transitions, safety and fairness.
`move_*` are zero placeholders, as permitted by the region interface.
The rule only **generates candidates**. Every REALIZABLE result must still pass
`prove`/`both_check` against the unchanged, source-bound concrete target AAG and
obtain `REGION_VERIFIED`. No check is weakened or bypassed. The method's
soundness is proved in Lean by `Tlsf.Gr1.region_conditions_sound` (PR #142).
A bad candidate only costs coverage; seed agreement is not a cutoff theorem.

If the target region checker exhausts its BDD capacity in the default order,
this path retries once in input-first order with the same caps and remaining
deadline/RSS budget. Semantic failures, artifact limits, cancellation and deadline
stops do not trigger an order retry. `checker_order` records the verifying order.
There is no policy fallback for folded candidates. The combined API retains its
existing independently checked direct fallback after a candidate decline.

Seed lowering uses the expanded source and provenance directly; it skips the
cover, recognition and template/composition analyses that reduction does not
consume. Accepted seeds have matching Mealy semantics and target, so target
adaptation is a no-op. The frontend shares the arm's cancellation, deadline and
live RSS budget. Checkpoints cover parsing AST allocations, temporary inference arenas,
substitution searches, numeric/formula evaluation and generation, set insertion,
recursive value/formula equality, membership, intersection and difference
(including disjoint scans with no allocations), provenance duplicate-signal and
AP-reference scans, formula printing, JSON construction and JSON serialization (strings are escaped in 4 KiB chunks).
Evaluation and traversal polls are amortized over 4096 steps per arena;
storage growth polls immediately and checks the full requested allocation against remaining RSS.
This includes the initial inference slab, AST slabs, intern tables, provenance
JSON pools and serialization/printing buffers. Ordinary callers with no budget
use an inline predictable branch and no budget callback or counter updates.
Only the additional seed lowerings in `discover_fold` opt in to capping each
generated provenance tree at the frontend's existing 2000-level recursion limit
when a frontend budget is active, before any consumer can traverse it; deeper
trees decline with `cause=resource`. Target preparation, legacy seed probes and
every other caller retain their existing behavior, including under a budget.
Unbudgeted expansion has no generated-depth cap.

These are cooperative limits: source-size-bounded parser/lexer operations and
individual libc allocation, copy, string and I/O operations are not preempted.
Parameter-dependent walks poll within their loops; no process is forked.
RSS is sampled at the existing 10 ms interval at ordinary polls and immediately
before storage growth, rather than enforced as a kernel hard limit.
Check counters advance when
each seed/target check starts, including rejected candidates and checks
interrupted by the budget callback.

All fold declines/stops are retained in `decline_detail`, including
`fold_unproved_width`, `fold_generator_binding`, `fold_monitor_inventory`,
`fold_schema_mismatch`, `fold_insufficient_strata`, `fold_probe_budget`,
`fold_rank_depth_changed`, `fold_no_candidate`, `fold_missing_tag`,
`fold_seed_mismatch` and `fold_region_failed(default|input-first)`.
The grammar is intentionally small; richer tagged-state or client-specific
predicates, such as the load-balancer schema, require a separate extension.

## Parametric-support folds (route B)

After the existing element lift and encoded fold decline, a growing-support
fallback handles constant-state global monitors over ordinary element buses.
Activation requires `bus_schema/large_template`, or its subsequent structural
shape mismatch when the arity bound is raised, and an unbound nonsymmetric
whole-bus monitor. Existing successful paths keep priority. Failed-axis probes
are destroyed before later legacy axes or route A run; only an activation flag
survives. After those paths decline, route B recreates probes under the same
fold probe allowance and arm deadline/RSS budgets, examining only canonical
provenance axes even after a legacy bus-schema exit. A U-only window retains its priority for UNREAL seeds;
REAL seeds instead enable the pending fold, selecting across all cached probes.
Checked REAL seeds are reused; newly selected sizes are solved and checked
under the same budgets. With distinguished constants `{0,1}`, the load-balancer
fixture selects 4/5/6 so that a nonconstant goal owner leaves a fold witness.
Declaration domains and family state counts are computed once per instance,
with cooperative budget checks throughout inventory and domain traversal.
Activation probing also records deadline, cancellation and RSS failures in
`decline_detail` before propagating them in either API.
Discovery selects three smaller nondegenerate instances
whose source occurrence/generator sets and domains match the target. Singleton
expansion can change a source node, so the load-balancer fixture selects 3/4/5.
No benchmark names, filenames, formula templates or identifier spellings enter
the detector.

Families retain source formula/node occurrences, binder IDs, side and role.
Indexed domains must be whole element domains with constant exclusions.
References to a distinguished element remain absolute constants, never offsets.
The first slice excludes ordered pair, prefix/suffix and moving-endpoint
domains, representation-bit buses, varying monitor state counts, indexed
fairness, changing rank depths and larger feature alphabets.

For state transport the feature alphabet consists of scalar letters, bound or
constant element letters, and whole-bus zero/at-most-one count tests. The code
abstracts each concrete next-state equation over this alphabet and requires
exact BDD equality when expanding it back. It then checks reset, all next
state equations, and acceptance under every state permutation (up to six
state bits). Exactly one transport must match, including at the reference
instance. Tags name the resulting states; their numeric labels have no
cross-instance meaning. All comparisons include arbitrary zero/multi-hot
valuations, without assuming one-hot encodings or reachability.

The candidate grammar is a Boolean predicate over fixed tagged states, the
goal's owner and one remaining element, conjunctively folded over remaining
elements. Fixed states include global/scalar monitors and each distinguished
constant's indexed monitors. Existential projection of a solved seed learns
the fold body `G`. This includes the form

```text
F(fixed, owner) AND forall i outside {constants, owner}: G(fixed, owner, i)
```

because `F` may be absorbed into each nonempty fold body. Discovery retains a
remaining witness even for indexed goals. Projection reconstruction must be
exact on every binding and every selected seed. Full-Boolean BDD equality is
required for W, every X/Y, and every goal, not just region acceptance of a
seed candidate. Lanes use the goal generator, constant/owner binding class,
rank level and source-bound fairness owner. Rank depth must be constant for
each goal generator, including all binding classes. Y is the union of X.
Actual target goal and fairness predicates remain those in the target AAG.

This code only **generates candidates**. A candidate has no cutoff or soundness
claim of its own. Every REALIZABLE result still requires `REGION_VERIFIED`
against the unchanged source-bound concrete target AAG. The existing region
method is proved sound by `Tlsf.Gr1.region_conditions_sound` (PR #142); this
extension neither bypasses nor weakens its checks and requires no additional
Lean theorem for its heuristic generator. A bad candidate can only cost
coverage. The shared checker-order fallback tries input-first first on route
B: the B2 experiments at n=10/11 verified quickly in that order while default
construction exhausted its deadline. Evidence records the verifying order,
source bindings, unique tag transports and exact seed predicate counts.

Route B diagnostics in `decline_detail` include `param_state_growth`,
`param_ordered_domain`, `param_tag_transport`, `param_no_candidate`,
`param_seed_mismatch`, `param_region_failed(default|input-first)`,
`param_rank_depth_changed`, `param_fairness_changed`, `param_encoding`,
`param_feature_alphabet`, `param_monitor_inventory`, `param_goal_inventory`,
`param_insufficient_seeds`, `param_subset_budget`, `param_semantics`,
and `param_discovery_failed`. Shared resource, deadline
and cancellation diagnostics still apply; `param_failed` attributes a stopped
candidate. Fault hooks 14–26 cover
state growth, domain rejection, tag ambiguity, grammar failure, seed mismatch,
a corrupted target candidate, rank/fairness changes and discovery/learning/
checking/result-copy and pending-fallback setup allocation failures. Both native
API test panels exercise them; every hook is registered in `lift_fault_cases`.
