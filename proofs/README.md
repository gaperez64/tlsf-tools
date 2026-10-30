# TLSF decomposition exactness proofs

This standalone project uses Lean 4.35.0 and core only (`import Init`). The
`TlsfProofs` target checks every module and `Examples.lean`, with warnings treated
as errors. All proof steps are checked by the kernel. Classical reasoning is
used for proposition cases, least witnesses and choosing component strategies.
There are no external Lean packages or executable decision shortcuts. The
dependency audit of the main results contains only `propext`,
`Classical.choice` and `Quot.sound`.

What is proved:

- `LTL.lean` models the expanded AST: constants, atoms, all five Boolean
  connectives, weak/strong next, F, G, U, R, W and M. `Sat len w f j` uses
  `len = none` for an infinite word and `some n` for positions below n.
  Queries outside the word are false. Weak next is true at the final position;
  strong next is false there. Locality reads only the formula's atoms at
  in-range positions at or after j. Boolean substitution is exact.
- `Game.lean` models input-first Mealy strategies with a history and current
  masked inputs. `play` supplies an infinite stream of environment choices.
  `Realizable` requires satisfaction at zero on every infinite play;
  `FinRealizable` requires some nonempty winning prefix on every play, exactly
  the `FinWin` quantifier order. Replay rebuilds each strategy's own history
  from inputs. Decoration implements a current-letter map, and a product
  strategy plays each component's owned output signals.
- `Objective.lean` constructs the literal ordinary objective
  `I -> (P && ((G Req && A) -> (G As && Gu)))` and strict objective
  `I -> (P && (As W !Req) && ((G Req && A) -> Gu))`.
  `objective_sat` proves their equivalence to section obligations at enabled
  positions, including the strict safety obligation before REQUIRE fails.
- `Passes.lean` models one substitution pass in list order, followed by exactly
  `passes` repetitions. Its letter map composes updates in the reverse order:
  substituting first d and then e denotes `setLetter d (setLetter e v)`.
  Ranked dependencies converge for every list order. After enough passes,
  every definition holds, including definitions with the equivalence flipped.
- `Definition.lean` proves realizability equivalence for both word kinds and
  both ordinary/strict semantics. The residual contains only retained entries,
  each transformed by the actual pass structure. A decorated residual strategy
  reconstructs a winning original strategy. The reverse proof uses section
  coverage and a dependency-closed support; it does not require a conditional
  definition to hold on plays where that section has no obligation.
- `Cluster.lean` proves infinite-word realizability iff every cluster is
  realizable, for both ordinary/strict semantics. Every cluster keeps all
  environment entries. Environment entries use inputs only; each system
  entry's outputs belong to its key's class. A key without a system entry is
  trivially realizable, even when the environment is inconsistent.
- `Pruning.lean` proves `prune_realizable` for infinite Mealy games, for both
  ordinary and strict objectives. `Prunable isIn K D` requires environment
  roles in D, input-only atoms in D, and no D atom in any K entry. `EnvSat D`
  is an infinite witness for `Initial D && G Require D && Assume D`. A
  residual strategy pins D inputs to that witness and replays the original
  strategy; locality transfers all K obligations. Adding D is pointwise
  weakening, including the strict safety obligation. No finite theorem is
  claimed.
- `Examples.lean` proves every requested game counterexample, guard rejection,
  finite next boundary and finite split failure. It also checks an accepted
  Boolean fixture in both equivalence orientations and a list order requiring
  more than one substitution pass.

- `Rewrites.lean` ports NNF, local weak simplification, the ordered local
  rewrite rules, bottom-up rewriting, the capped rewrite driver, pre-weak
  simplification and spine decomposition. All exactness statements quantify
  over every word and valid position, for both word kinds when finite mode is
  enabled and for infinite words otherwise.

## Guard and game interfaces

`Admissible isIn strict kept ds passes` consists of these conditions:

1. Each definition name is an output (`isIn name = false`).
2. Each right-hand side is Boolean, and definition names are pairwise distinct.
3. There is a rank function, with every dependency between eliminated signals
   strictly decreasing and every defined signal's rank below `passes`.
4. Every original entry mentioning a definition name has a system role and
   satisfies `covers strict use definitionRole`.

`covers` is exactly equality of roles, a PRESET definition, a GUARANTEE use of
an ASSERT definition, or an ordinary ASSERT use of a GUARANTEE definition.
`covers_trans` checks every Boolean/role combination using kernel reduction.
`Admissible.not_self` proves that self dependence contradicts the rank condition. Instantiate `passes` with
`ds.length + 1` for the C loop's `nelim + 1` passes. The theorem also permits any
other pass count satisfying the explicit rank bound.

`Clustered isIn owner es` records input-only environment support and ownership
of every output in each system entry. `whole es` contains every entry;
`cluster es k` retains every environment entry and the system entries at k.
The theorem quantifies over all keys, including unused keys. No finite split
claim is made: finite components can need incompatible ending positions.
After this split, `prune_realizable` may be applied separately to each cluster.
It compares the full cluster K ++ D against K. All kept entries, including
PRESET, ASSERT and retained environment entries, participate in disjointness.
`EnvSat` is a full-word witness; only its input atoms matter under `Prunable`.
If D is inconsistent, `pruning_without_envSat_changes_verdict` exhibits a
realizable full objective and an unrealizable pruned objective for either shape.

When C collapses the decomposition to one cluster, keeping every entry gives
the original game directly, including for finite and output-dependent cases (`collapsed_cluster`,
`collapsed_cluster_realizable_fin`).

## Issue obligations

Names without an explicit namespace belong to `Tlsf`; counterexamples and
fixtures belong to `Tlsf.Examples`.

| Issue | Obligation | Theorem or definition |
| --- | --- | --- |
| #79 | First split with every environment entry and disjoint system outputs | `Clustered`, `cluster`, `cluster_same_environment`, `clusters_realizable` |
| #79 | Compose strategies with independent histories | `replay_ignores_outputs`, `replay_history`, `product_plays`, `cluster_product` |
| #79 | Empty system key is realizable | `empty_cluster_objective`, `empty_cluster_realizable` |
| #79 | Prune input-only environment entries disjoint from all kept entries, given a joint infinite witness | `Prunable`, `EnvSat`, `prune_realizable` |
| #79 | Pinned-input strategy is causal and its replay matches the original play | `pinStrategy`, `replay_pin_history`, `play_pinStrategy` |
| #79 | Inconsistent disjoint assumptions can change the verdict in either shape | `recurrence_conflict`, `issue79_original`, `issue79_pruned`, `issue79_env_unsat`, `pruning_without_envSat_changes_verdict` |
| #84 | No eliminated output occurs on the environment side | `Admissible.occurrences`, `normalize_environment`, `elim_backward` |
| #84 | Original game wins by falsifying an output assumption; residual loses; guard rejects | `issue84_original`, `issue84_residual`, `issue84_rejected` |
| #86 | PRESET and strict ASSERT uses require a covering definition | `covers`, `covers_trans`, `enabled_cover`, `normalize_kept` |
| #86 | Unconditional preset counterexample and rejection | `issue86_original`, `input_q_unrealizable`, `issue86_rejected` |
| #84, #86 | Exact Boolean elimination for both semantics and word kinds | `elim_realizable_inf`, `elim_realizable_fin` |
| #84, #86 | Same C pass structure; every reconstructed equality holds | `sat_substPass`, `sat_substPasses`, `normalize_definitions`, `definition_sat`, `pass_order` |
| #91 | Current-letter Boolean decoder is causal and keeps inputs | `boolean_sat`, `normalize_inputs`, `play_decorate`, `transfer_inf`, `transfer_fin` |
| #91 | Future-dependent decoder loses against an answering environment; Boolean guard rejects | `issue91_noncausal`, `issue91_rejected` |
| #85 | One-letter weak next and the negation counterexample | `issue85_weak_next`, `issue85_negation` |
| #85 | Correct weak/strong next dualities | `next_neg_dual`, `strong_next_neg_dual` |
| #85 | Finite realizability distinguishes weak-next false from false | `issue85_finite_realizable`, `false_finite_unrealizable` |
| Finite split | Conservative one-cluster finite fallback preserves the game | `collapsed_cluster`, `collapsed_cluster_realizable_fin` |
| Finite split | Each component wins at a different length; conjunction loses | `finite_short_realizable`, `finite_long_realizable`, `finite_split_fails` |
| Core | In-range future locality and exact Boolean substitution | `sat_locality`, `sat_subst`, `subst_absent` |
| Core | Literal ordinary/strict section objective | `section_sat`, `weakUntil_guard`, `objective_sat` |
| Core | Input-preserving causal strategy transfer | `transfer`, `transfer_inf`, `transfer_fin` |
| Positive fixtures | Guard is satisfiable for either equivalence orientation | `boolean_fixture` |

## Issue #85: rewrite exactness

The new module is `TlsfProofs/Rewrites.lean`, in namespace `Tlsf.Rewrites`.
`Ltl` is an abbreviation for the existing `Formula`, not a second syntax.

```
Exact fin f g := ∀ len, (fin = true ∨ len = none) → ∀ w j,
  InRange len j → (Sat len w f j ↔ Sat len w g j)
```

A valid position in `some n` entails `n > 0`, so these statements include
exactly the requested nonempty finite words. With `fin = false`, the length
must be `none`. No assumptions about valuations, formula shape or rewrite-flag
combinations are added within the expanded core syntax.

| Issue | Obligation | Theorem statement (implicit type/equality parameters omitted) |
| --- | --- | --- |
| #85 | Congruence before pass soundness | `exact_congr` lifts Exact equivalences of immediate children; `bind_exact` and `context_exact` replace holes in arbitrary nested contexts, including negation and implication |
| #85 | Both NNF polarities | `nnf_exact f fin : Exact fin (to_nnf f true fin) f ∧ Exact fin (to_nnf f false fin) (neg f)` |
| #85 | Infinite-mode NNF is unsafe on finite words | `nnf_infinite_mode_finite_failure w` refutes equivalence for `not (X p)` on a one-letter word, reusing `Examples.issue85_negation` |
| #85 | Every local constant/redundancy rule | `simplify_exact f : Exact fin (simplify_weak_local f fin) f` |
| #85 | Every combination of local-rule flags | `apply_local_exact f flags : Exact flags.finite (apply_local f flags) f` |
| #85 | Bottom-up subformula replacement | `rw_pass_exact f flags : Exact flags.finite (rw_pass f flags) f`, using `bottom_up_exact` and `exact_congr` |
| #85 | NNF first, structural stability test, cap 200 | `apply_rewrites_exact f flags : Exact flags.finite (apply_rewrites f flags) f`; `rewrite_loop_exact` proves this for every fuel, even when no fixpoint is reached |
| #85 | High-level weak simplifier on core constructors | `pre_weak_exact f : Exact fin (pre_weak f fin) f` |
| #85 | Conjunction of all decomposed parts | `decompose_exact f : Exact fin (conjoin (rewrite_decompose f)) f`; `decompose_has_part` supplies the nonempty-list premise needed for strong next |
| #85 | Finite-safe temporal RULES rows | `route_push_g_in`, `route_push_x_in`, `route_push_strong_x_in`, `or_to_guarded_next_impl`, `or_to_guarded_strong_next_impl`, `or_to_response_impl`, `pre_spine_split_exact` |
| #85 | Expanded indexed-next identities | `pre_x0`, `pre_xn_flatten`, `pre_xn_bool_distribute` for `next_power`, with both-word exactness |
| #85 | Reject all three finite-disabled metadata rows | `sickert_rules_refused`, `sickert_limit_lift_refused`, `sickert_gf_w_refused`, `sickert_fg_u_refused` show the finite guard returns false |
| #85 | Counterexample to the unrestricted context equation | `sickert_finite_counterexample`: on one letter with p=true, `C[GF p]` is false and `(GF p && C[true]) || C[false]` is true for `C[z] = G(!z)` |

The named distribution and guarded-implication lemmas state satisfaction
biconditionals for every `len`, word and valid position; they therefore cover
finite words without an extra side condition. They prove `G(a&&b)=Ga&&Gb`,
`X(a&&b)=Xa&&Xb` for weak and strong next, and `!r||T a = r->T a` for weak
next, strong next and eventually. The guarded-implication lemma also applies
to a next chain by taking its operand to be the remaining chain.

The Sickert counterexample deliberately uses a **nonpositive** context. It
refutes the equation with an unrestricted context, including on finite words;
it is not a counterexample to the C pass's positive-NNF-context premise, nor
a claim of a finite-only failure of that monotone identity. The three finite
refusal results establish the actual metadata guard independently of this
example. No infinite-word Sickert soundness theorem is claimed.

The ports preserve return-on-first-rule order and structural AST equality.
`Flags` has one Bool per defined C flag. The driver passes the structure to
local traversals unchanged: `nnf` is never inspected there, so this is exactly
the C mask that removes RW_NNF/RW_FINITE and then restores RW_FINITE. AST
pointer reuse and arena allocation do not appear in the mathematical result.
`pre_local` factors only the NOT/AND/OR branches through the identical local
simplifier; its implication fold is deliberately smaller, it does not collapse
FF/GG, and `pre_walk` leaves a strong-next subtree untouched as the C default
branch does.

| C source in this worktree | Lean correspondence |
| --- | --- |
| `src/lib/nnf.c:9–123` | `to_nnf`, `nnf_sat`, `nnf_exact`; weak-next polarity/finite test at lines 80–86 |
| `src/lib/rewrite.c:15–38,46–181` | Structural `DecidableEq (Formula α)`, `simplify_weak_local`, `simplify_exact`; finite weak-X-false guard at lines 101–106 |
| `src/lib/rewrite.h:36–62`; `src/lib/rewrite.c:189–235` | `Flags`, ordered `apply_local`, `apply_local_exact` |
| `src/lib/rewrite.c:238–295` | `bottom_up`, `rw_pass`, `rw_pass_exact`; atom cases bypass local rewriting |
| `src/lib/rewrite.c:10,297–324` | `RW_FIXPOINT_CAP = 200`, `rewrite_loop`, `apply_rewrites`, `apply_rewrites_exact` |
| `src/lib/rewrite.c:345–380` | `rewrite_decompose`, `conjoin`, `decompose_sat`, `decompose_exact` |
| `src/lib/normalize.c:751–841` | `pre_local`, `pre_walk`, `pre_weak`, `pre_weak_exact` on expanded constructors |
| `src/lib/normalize.c:845–880` | `pre_spine_split`, `pre_spine_split_exact` on the core; indexed-X high-level branch excluded |
| `src/lib/normalize.c:88–142,419–435` | Temporal RULES identities; `SickertRule.equivalence_finite` and `finite_rule_allowed` model the finite-admission projection |
| `src/lib/normalize.c:987–1003` | `or_to_impl` and named response/guarded-next identities, valid in both operand orders by disjunction commutativity |
| `src/lib/normalize.c:1341–1373` | Finite mode propagated to NNF, weak and route-safe rewrites; supported passes compose by `Exact.trans` |
| `src/lib/print_ltlxba.c:214–216,242–249` | Trusted printer correspondence: NODE_X is weak X and NODE_X_STRONG uses X[!] for finite rendering |

Additional trusted gaps for #85:

- C and Lean ASTs, interned AP identifiers and structural equality must agree.
  The proofs cover successful transformations of expanded, unbounded core
  nodes, excluding malformed/high-level ASTs, integer nodes, bounded metadata,
  arena exhaustion and machine-size/allocation behavior.
- `NODE_NEXT_N` in pre-weak only recurses into its body
  (`src/lib/normalize.c:821–824`) and is outside `Formula`. The analogous
  indexed-next branch in pre-spine splitting, arithmetic evaluation, bounded
  quantifiers and expansion into ordinary nexts are not C-verified here.
  `next_power` states the identities of the expanded mathematical sequence.
- The RULES and finite guard ports do not verify the full scheduler, phase or
  growth checks, CLI option plumbing, other normalization passes, or Sickert
  transformations. A caller must run the finite admission check before those
  infinite-mode passes.
- Printing/escaping and downstream interpretation of X versus X[!], including
  `print_ltlxba.c:242–249`, remain trusted; these kernel proofs do not execute
  C or establish an emitted residual trust tag.

## C ↔ Lean correspondence

All C locations in this table are relative to the repository root **in this
working tree**, including the guards described here. The
correspondence covers the guarded mathematical model; it does not verify the C
implementation or the other CSNF template families.

| C source in this working tree | Lean port / correspondence obligation |
| --- | --- |
| `src/lib/ast_query.h:14–35,52–79`; `src/lib/cover.c:35–77` | `Formula`, `Formula.atoms`, `Boolean`, `isIn`; cover support must match the expanded formula |
| `src/lib/templates.c:72–119` | `subst`, `setLetter`, `setWord`, `sat_subst`, `subst_absent` |
| `src/lib/recognize.c` (`match_definition`); `src/lib/templates_certify.c` (`certify_definition`) | `Definition.entry`, `flip`, `Admissible.outputs`, `Admissible.boolean`; the certifier rejects every temporal theta using `ast_has_temporal` |
| `src/lib/templates.c:299–360,501–516` | `Ranked`, `Admissible.ranked`; accepted decoder dependency graph has a bounded topological rank |
| `src/lib/templates.c:405–409,479–497` | `Admissible.occurrences`, `covers`, `covers_trans`; the composition guard checks every affected section and rejects environment-side definitions |
| `src/lib/templates.c:517–543` | `Admissible.distinct`, `original`, `residual`; one chosen provider per output, defining entries dropped |
| `src/lib/residual.c:19–28` | `substPass`, `substPasses`; instantiate `passes = ds.length + 1` |
| `src/lib/residual_plan.c:23–39` | `residual`, `residual_objective`; optional additional rewrites require separate semantic correctness |
| `src/lib/residual_plan.c:44–53,72–115` | Freeze the first pruned/retained view across routing, solving and export; cache allocation failure disables pruning for the plan |
| `src/lib/residual.c:30–59,68–77` | `Formula.atoms`, `normalize_untouched`; support collection and unused-output declaration removal |
| `src/lib/section_pattern.c:81–114,173–225` | `sectionFormula`, `objectiveFormula`, `objective_sat`; empty sections are true, all section conjuncts are included |
| `src/lib/residual.c:111–184,186–234` | `Prunable`, `EnvSat`, `prune_realizable`; the transitive cone includes all kept roles, asserts dropped input support/disjointness, and prunes only infinite ordinary/strict Mealy games after a positive joint check |
| `src/lib/residual_sat.cc:17–74,78–116` | `EnvSat`; direct AST translation conjoins INITIALLY, globally wrapped REQUIRE, and ASSUMPTIONS; Spot nonemptiness is a trusted witness-existence answer; uncertainty keeps D |
| `src/lib/residual.c:252–357` | `Clustered`, `owner`, `clusters_realizable`; union-find gives disjoint output classes; the finite/output-dependent fallback keeps a single game |
| `src/lib/print_ltlxba.c:214–249`; `src/lib/nnf.c:75–86` | `Sat` for `next` and `strongNext`, `next_neg_dual`, `strong_next_neg_dual` |
| `src/lib/rewrite.c:101–116`; `src/lib/normalize.c:815–819` | `issue85_weak_next`, `issue85_negation`; finite next must retain its terminal behavior |
| `src/lib/decompose.c:69–75` | `elim_realizable_inf`, `elim_realizable_fin`, `clusters_realizable` delimit the mathematical basis of exactness |

The textual controller `ctl o := theta` is emitted outside `src/lib`, in
`src/tools/tlsfcompose/main.c:1027` in this working tree. `normalize_definitions` proves
that reconstruction by the composed letter map satisfies every such equation;
`play_decorate` supplies its Mealy implementation.

## Trusted gap

For CSNF decomposition, **definition elimination, clustering, and conditional
assumption pruning (`prune_realizable`) are proved**. The other CSNF
templates—Phase B Skolem values, registers, reaction and liveness schedulers—are
guarded but unproved. The rewrite theorems above
are separate formula-equivalence results, not proofs of these controllers.

The kernel checks a mathematical port; it does not execute or verify the C
binary. C sets, lists, AP identifiers, AST constructors and section roles must
correspond to the Lean model. In particular, **cover output sets must equal the
formula's output atoms**. This includes any normalized/matching formula used
by recognition: recognizing an equality must recover the same constraint and
support. Expansion, normalization, preprocessing, memory management, allocation
failure behavior and machine-integer bounds remain C obligations.

The cycle check must correspond to a rank on all accepted definitions, with a
bound below `nelim + 1`. Provider selection must make names distinct. The
section guard must inspect every entry mentioning an eliminated output,
including other definitions, and its role test must equal `covers`. The new
Boolean test must reject all temporal constructors, not merely next. The game
is **Mealy only**; the definition certifier must decline Moore.

The unproved templates now have these conservative runtime rules. These are
C guards, not additional Lean controller theorems. `TRUST_EXACT` means
realizability equivalence under the certifier and composition guards; a free
reaction/register can choose a satisfying strategy without forcing a unique
value on every trace.

- Every output-fixing non-definition certifier uses `output_is_free` in
  `src/lib/templates_certify.c`, directly or through
  `output_constrained_elsewhere`. It first requires a declared output. An
  environment-side occurrence
  in INITIALLY, REQUIRE or ASSUMPTIONS rejects elimination even inside the
  candidate block. Every use outside the block also rejects it, including
  unconditional PRESET and strict ASSERT uses. Round-robin uses this common
  check instead of skipping all member constraints; set/reset, toggle and
  guarded-next registers now use it too. The invariant, reaction,
  reachability, persistence, delayed-definition, fixed-delay, recurrence
  switch, response/server and arbiter certifiers share the same rule. A
  standalone mutex does not fix an output or discharge its constraint.
- Round-robin and arbiter certification require every mutex member to be an
  output and free outside the entire block, including members without a
  recurrence or response. The check covers every output of every block
  constraint. Mutex recognition rejects self-pairs such as `!(p && p)` before
  constructing the distinct member set. Arbiter grants must be outputs and
  requests must be plain inputs. Free unscheduled members can be held false.
- Every assigned definition/register value and every reaction, guarded-next,
  set/reset, toggle and fixed-delay guard must be temporal-free. Both positive
  and negative guards are checked. Reactions also decline self-reference;
  combinational definitions/reactions and Skolem invariants decline Moore
  semantics. Registers read the current letter to drive a later output, so
  Boolean current-input guards are permitted in Moore games. Server request
  artifacts represent plain input signals only; other guards, including
  temporal formulas and output requests, remain residual.
- Invariants conservatively decline bodies containing unflagged atoms. The
  cover's input support, residual interfaces, monitor eligibility and timing
  adaptation all treat those atoms as environment inputs. The bounded Boolean
  solver must not treat an omitted input as a constant false valuation,
  including in input-only bodies.
- Phase B checks support closed transitively under every committed definition
  theta (`src/lib/templates.c:425–455,559–606`), including dependencies absent
  from a surviving constraint's original output set. Rejected blocks remain
  residual. The `phase_b_probe` regression supplies locally solved blocks
  directly to composition, so the local free-output guard cannot mask this
  check; it covers direct and reversed-order transitive dependencies. This
  ownership check is not a Lean proof of Phase B elimination.
- Finite semantics declines **both weak and strong next** for delayed
  definitions, set/reset, toggle, fixed-delay and guarded-next in
  `src/lib/templates_certify.c`. At the final position weak next is true and
  strong next false,
  independently of the output; a transition register alone does not discharge
  an equivalence's terminal obligation. Weak-next implications have vacuous
  terminal obligations, but these families are conservatively declined too.
  Round-robin, arbiter and global-recurrence-switch also decline finite
  semantics: final-position GF obligations (or requests with F responses)
  cannot be discharged by an infinite fair schedule. In particular two final
  grants can contradict a mutex. Free F/FG outputs and plain-input single-grant
  servers can instead hold their output true, satisfying every nonempty prefix;
  Boolean invariants/reactions have no temporal terminal obligation.

Before cover construction, the shared `tlsf_pipeline_build_cover`
(`src/lib/pipeline.c`, `tlsf_pipeline_build_cover`) applies `spec_adapt_target`
exactly once after
expansion. The pipeline (including tlsfresidual and the decomposition API),
tlsfcompose, tlsftemplates and tlsfbenchgraph all use it. The conversion path
(`conversion_prepare`, including tlsf2ltl) uses the same validation. Both
refuse differing finite SEMANTICS/TARGET timing frames with an explicit
diagnostic, including CLI overrides; no finite-correct adaptation is claimed.
Infinite-word Moore/Mealy adaptation remains a trusted frontend obligation
outside these Lean theorems and includes implicit environment inputs. The
generated driver uses the effective TARGET move order: Moore targets bypass
the input-first OxiDD games, with infinite-word realizability checked by the
standard input-delay encoding for ltlsynt. Finite residuals use ltlfsynt with
explicit Mealy/Moore semantics. The controller-export wrapper refuses finite
games and Moore targets because it does not implement their export contracts.

An empty section is `tt` in Lean but represented by absence and dropped in C.
Their objectives must be equivalent, including the strict empty-REQUIRE case
`As W false = G As`. The successful C view must include every retained
constraint with the correct role. The expanded-core simplification, NNF and
rewrite passes listed above preserve `Sat` by the #85 theorems. Bounded expansion, high-level operator
lowering and normalization passes outside that list remain trusted.

Lean keeps the full signal type after elimination. C drops an unused output
from the residual's declaration. Projection to the used alphabet and extension
with arbitrary values must preserve both the game and the printed formula;
only the mapped decoder reconstruction may subsequently assign the eliminated
output. The absent-signal locality/substitution results support this interface,
but the declaration/filtering code is not verified here.

Union-find and cluster-key construction must establish `Clustered`. The
initial cluster contains every environment entry. Pruning then requires
`Prunable` and `EnvSat` for the actual dropped set. **Spot's positive
satisfiability answer is trusted**: Lean neither verifies Spot nor checks an
accepting run. The C AST-to-Spot translation must denote exactly
`Initial D && G Require D && Assume D`, using the substituted residual formulas.
The optional check uses at most 128 source AST nodes and a 256-state/1024-edge
translation budget; failure, exceptions, missing Spot headers, or an elapsed
50 ms deadline retain D. Spot calls are synchronous, so the elapsed-time
check discards overruns rather than preempting a call. Spot is currently a
required Meson dependency; the helper has a conservative compile-time
fallback if its translation headers are unavailable. Finite semantics and
Moore semantics/targets never use pruning. If an environment entry mentions an
output, or the semantics is finite, the C fallback must retain one game
before this proved pruning, including input-only system constraints. The `clusters_realizable` theorem is
for infinite words with input-only environment entries. `finite_split_fails`
shows that independent finite winning prefixes cannot in general be combined.

Printing, escaping and AP names must denote the Lean AST, preserve weak/strong
next, and emit controllers with the established dependency interpretation.
Any compiled controller composition must realize the composed letter map, not
a single order-sensitive simultaneous assignment of unexpanded values. Solver
and export frontends must use the positive system objective and the same
input/output ownership. In particular, **ltlfsynt's game must equal `FinWin`**:
for every play there is some nonempty finite winning prefix. The development
does not verify the external solver, its ending convention, the printer or the
reported trust label.

## Build

Run from `proofs/` with exactly one Lean compiler process at a time. The modules
form a dependency chain, so the default build checks them serially. The library
uses the same weak arguments as acacia: `-j1`, `-s2048`,
`-DElab.async=false`; `warningAsError = true`. Do not set a virtual-memory cap.

```sh
export PATH=$HOME/.elan/bin:$PATH
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=2048 LEAN_MAIN_USE_THREAD=0
lake build
```

For sequential per-module diagnostics:

```sh
for module in LTL Game Objective Passes Definition Cluster Pruning Examples Rewrites; do
  timeout 300 lake env lean "TlsfProofs/$module.lean" || exit $?
  timeout 300 lake build "TlsfProofs.$module" || exit $?
done
timeout 1500 lake build
```
