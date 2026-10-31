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
  is an infinite witness for `Initial D && G Require D && Assume D`.
  `envSat_of_word` bridges satisfaction of `environmentFormula D` on any
  infinite word (including a lasso) to `EnvSat D`. A
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
| `src/lib/residual.c:111–186,188–236` | `Prunable`, `EnvSat`, `prune_realizable`; the transitive cone includes all kept roles, asserts dropped input support/disjointness, and prunes only infinite ordinary/strict Mealy games after a positive joint check |
| `src/lib/env_witness.c:20–88` | Expanded AST/section compilation for `environmentFormula`; rejects other roles and unsupported syntax |
| `src/lib/env_witness.c:90–188` | Lasso successor and least/greatest fixed points implement `Sat none`; REQUIRE holds at every reachable position, INITIALLY/ASSUMPTIONS at zero; `environment_sat_iff` in `proofs/TlsfProofs/Pruning.lean:11–27` |
| `src/lib/env_witness.c:190–229`; `src/lib/env_witness.h:6–7` | Only a completed positive witness check returns SATISFIABLE; `envSat_of_word` in `proofs/TlsfProofs/Pruning.lean:29–31` supplies `EnvSat` for `prune_realizable`; incomplete search keeps D |
| `src/lib/residual.c:254–359` | `Clustered`, `owner`, `clusters_realizable`; union-find gives disjoint output classes; the finite/output-dependent fallback keeps a single game |
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
`Prunable` and `EnvSat` for the actual dropped set. The native checker
searches infinite lasso words with at most four positions and eight atoms,
under a 128-source-node syntax cap and a shared 200,000-update work budget
(candidate, node, fixed-point and section checks). The last position returns
to the chosen loop entry. F/U/M use least fixed points and G/R/W use greatest
fixed points over the reachable positions. REQUIRE is checked at every
position; INITIALLY and ASSUMPTIONS only at position zero. Only a completed
positive check certifies the conjunction. Failed candidates are skipped;
if no bounded witness is found, syntax is unsupported, or a budget is
exhausted, the result is UNKNOWN and D is kept. Incompleteness therefore
cannot change realizability.

`envSat_of_word` proves that satisfaction of this conjunction with `len = none`
on any word yields `EnvSat D`; applying `prune_realizable` then gives the
conditional equivalence. **The C evaluator, AST/section correspondence and
lasso-to-infinite-word interpretation remain trusted**: Lean does not execute
C or prove the evaluator implementation. Search completeness is unnecessary.
This check uses no external automata or SAT library. Finite semantics and
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

## Issues #80 / #83: lazy-DPA formalization

The eight modules under `TlsfProofs/Dpa/` use namespace `Tlsf.Dpa` and infinite
words only (`Sat none`). They formalize the conservative DESIGN §1 variant:
no support resets, no external suspension, a complete fixed product, and an
ordinary one-sibling global-tree update. The required reference merge is
`aa9327a`; STAGE2 was already merged at `9702e09`.

**The requested semantic proof chain is complete for the §8 admitted grammar.**
`tree_minEven` and `tree_maxOdd` prove the global recurrent-run theorem for
all colour streams. `flat_eventually_false_seeds`, `flat_global_language` and
`flat_eventual_language` discharge §6. `admitted_grammar` assembles the exact
component/product/parity language theorem. `Refinements.lean` proves §9's
semantic refinements and reference decision algorithms. The general Π₂ component
converse is now proved separately by `general_pi2_converse`, with the exact
component language in `general_pi2_language`. The §9 constructor/admission
theorems still concern the conservative §8 grammar; no C guard is changed.

The checked semantic class model is a Boolean function with a finite formula
representative. `class_finite_atoms` supplies a finite atom set on which each
function depends. Modal atoms, including a formula and its NNF dual, remain
independent; AP negation shares its AP variable. `Uses` is exact dependence,
so support tests disregard propositionally absorbed atoms of the current class.
A supported protector still contributes every X subformula of its frozen
syntax, including Xs inside Boolean operands that would absorb if materialized.
`Positive` states modal monotonicity; `NNFClass` supplies an NNF representative.
`GeneralConverse.lean` now proves the common finite alphabet of both fields
(`run_subformulaBound`), injection into finite Boolean truth tables
(`subformula_signature_injective`), and a finite list containing every
reachable component pair on every word (`finite_component_states`). It also
proves eventual false protected constraints and the general Π₂ component
language by finite closed-alphabet descent (Task J below). These are semantic
results, not a practical state bound or a proof of the C allocator/BDD bridge.

`Stage1.lean` defines the shared table and proves safety/co-safety and the
one-set parity results. `Component.lean` extends it with the general component
facts. The GF/FG corollaries are in `Converse.lean`: they reuse the general
accepting-seed theorem, avoiding a circular import from Stage1 to Component.
Their comments retain the STAGE1 equation/section references. In particular,
`gf_seed_bound` proves the upper bound sufficient for the unbounded-start
argument; it does not claim the full two-case extractor equation (3).

### Obligation map

All names below are in `Tlsf.Dpa`. The requested stages were built in order:
§5, §§6.1–6.5, §8, then §9. Remaining C bridges and ancillary obligations
are identified explicitly; they are not premises of the language equalities.

| Markdown section / claim | Lean definition or theorem | Status / scope |
| --- | --- | --- |
| STAGE1 §1: finite/safety/co-safety grammars, finite X depth | `finite`, `safety`, `cosafety`, `horizon`, `NNF` | Checked definitions |
| STAGE1 §1: full canonical NNF/X-distribution C transport | Existing `Tlsf.Rewrites.nnf_sat`, `pre_xn_bool_distribute`; `finite_nnf_polarity` | Semantic identities checked; C transport bridge trusted |
| STAGE1 §2: propositional classes, implication, exact support | `Class`, `Class.Implies`, `Uses`, `HasTag`, `support_locality`, `class_finite_atoms` | Checked; finite support per class |
| STAGE1 §2: frozen U and simultaneous raw D | `unfoldSyntax`, `stepSyntax`, `U`, `D`, `delta`, `U_idempotent` | Checked |
| STAGE1 §2 / STAGE2 §2: extractor, changing support, protection, retry | `reduce`, `Protected`, `dropX`, `elide`, `rho`, `elide_stable`, `rho_retry_stops` | Checked definitions and termination |
| STAGE1 §2 / STAGE2 §2: ordered component table and mark 0 | `Pair`, `Edge`, `initial`, `transition`, `run`, `marks` | Checked deterministic total function; fixed-input state finiteness pending |
| STAGE1 §3 (1): derivative and iterated derivative | `derivative`, `derivative_syntax`, `U_holds`, `derivatives_holds` | Checked for every class / infinite position |
| STAGE1 §3: finite windows | `finite_window`, `finite_window_constant`, `bounded_constant_eval` | Checked locality and constant after h+1 letters |
| STAGE1 §3: good prefixes | `cosafety_witness`, `class_cosafety_witness` | Checked; latter assumes `Positive` and exact co-safety support |
| STAGE1 §3: bad prefixes | `safety_bad_prefix`, `class_safety_bad_prefix` | Checked directly; does not require an unproved propositional dual-commutation lemma |
| STAGE1 §3: fragment closure / intersection | `U_safety`, `D_safety`, `U_cosafety`, `D_cosafety`, `tags_intersection`, `step_bounded` | Checked; standalone class-level NNF dual commutation not supplied |
| STAGE1 §4: safety, both directions | `safety_language`, `safety_complement` | Checked for positive support-tested classes |
| STAGE1 §4: co-safety, both directions; precedence of safety row | `cosafety_language`, `cosafety_complement` | Checked for NNF support-tested classes |
| STAGE1 §4 (2): GF all-field fixed | `gf_derivative_fixed`, `gf_all_fixed`, `gf_not_simple` | Checked |
| STAGE1 §4 (3): exact retry/seed case split | `gf_seed_bound`, `search_dropX_fixed` | Sufficient seed bound and protection checked; exact two-case equality pending |
| STAGE1 §4: GF finite windows, both directions | `gf_language` | Checked, using the general accepting-renewal-seed theorem |
| STAGE1 §4: FG finite windows and complement | `gf_complement`, `fg_language` | Checked on the identical completed dual run |
| STAGE1 §5: one-set min-even and max-odd tables | `oneSet_min_inf`, `oneSet_min_fin`, `oneSet_max_inf`, `oneSet_max_fin`, `gf_minEven`, `fg_minEven`, `gf_maxOdd`, `fg_maxOdd` | Checked numeric parity languages; identification with the built one-colour tree's unique path pending |
| Task J: fixed-input finite alphabet and semantic state closure | `run_subformulaBound`, `subformula_signature_injective`, `finite_reachable_pairs`, `finite_component_states` | Checked for all words and both fields, including retry and finite retention; no general language theorem follows from finiteness alone |
| Task J: nested Π₂ failed constraints | `pi2_cosafety_failure`, `class_pi2_cosafety_failure`, `general_eventually_false_cosafety_constraints` | Checked for the full Π₂ nesting structure and arbitrary NNF classes; every sufficiently late raw position has a false co-safety consequence |
| Task J: closed-alphabet descent and protection | `eventually_protected_of_cosafety_constraint`, `general_eventually_false_protected_constraints`, `general_eventually_false_passes` | Checked at every sufficiently late raw position and every intermediate weakening; no finite-window flush or never-false premise |
| Task J: general component language | `general_pi2_converse`, `general_pi2_language` | General Π₂ converse and language equality proved, including retry and retained finite remainders; C admission/refinement unchanged |
| Task T: executable canonical class decisions | `Impl.table_exact`, `Impl.equivalent_exact`, `Impl.uses_exact`, `Impl.hasTag_exact` | Checked executable truth tables and exact support, including Boolean absorption |
| Task T: executable component simulation | `Impl.classTag_exact`, `Impl.rho_exact`, `Impl.initial_exact`, `Impl.transition_exact`, `Impl.run_exact`, `Impl.marks_exact` | Checked for research structural tags; C transport, IDs and caches still outside the bridge |
| Task T: Π₂/Σ₂ orientation and numeric parity | `Impl.pi2_language`, `Impl.sigma2_language`, `Impl.dual_class_congr`, `Impl.class_sigma2_dual_pi2`, `Impl.research_component_language` | Checked for NNF whole classes accepted by research admission, including arbitrary canonical support; complete constructor/export theorem pending |
| Task T: canonical research domain and grouping branch | `Impl.canonicalResearchCheck_exact`, `Impl.canonicalResearchCheck_shannon`, `Impl.compatibleGroups_exact` | Executable support-union predicate and folded-class identity branch checked; constructor success/product simulation pending |
| Task T2: positive-Boolean Büchi rounds and incoming state split | `Impl.seenColours_exact`, `Impl.completedRounds_language`, `Impl.incoming_state_split`, `Impl.incomingMarks_language`, `Impl.buchiPriority_language`, `Impl.positive_buchi_language` | Checked executable Shannon residual/reset monitor, including constant acceptance and source-state 0/1 max-odd priorities; complete constructor selection remains separate |
| Task T2: component store, cache hits and permanent colours | `Impl.internComponent_valid`, `Impl.internComponent_language`, `Impl.internComponent_preserves_index`, `Impl.internComponent_preserves_literal`, `Impl.store_productColours` | Checked executable insertion-order lookup, equal-class and cached-dual sharing, fresh orientation, and preservation of all existing complete streams and literals |
| Task T2: shared-store Shannon and grouped assembly | `Impl.assemble_spec`, `Impl.assemble_presentation`, `Impl.assemble_shannon_presentation`, `Impl.assemble_grouped_presentation` | Checked compilation of explicit valid construction plans into the actual indexed acceptance and `ProductPresentation`; complete C plan selection/order refinement pending |
| STAGE2 §1: intended Π₂ and flat families | `Pi2`, `FlatQ`, `FlatR` | Checked grammar definitions |
| STAGE2 §3 (1): weakening, co-safety, unfoldedness | `rho_weakens`, `rho_cosafety`, `rho_unfolded`, `rho_nnfClass` | Checked; weakening assumes NNF |
| STAGE2 §3 (2): all/rejecting invariant | `ComponentInvariant`, `initial_invariant`, `transition_invariant`, `run_invariant`, `run_remainder` | Checked for arbitrary NNF inputs, without a Π₂ converse hypothesis |
| STAGE2 §3: false renewal / resumption unreachable | `no_false_renewal`, `no_active_resume`, `resume_unreachable` | Checked with the preceding invariant |
| STAGE2 §3 (3): all-field exactness, including false sink | `all_field_derivative`, `all_field_exactness` | Checked |
| STAGE2 §3 (4): satisfying words accept | `satisfying_accepts` | Checked for arbitrary NNF inputs |
| STAGE2 §3 (5): retained obligations across renewals | `rejecting_step_preserves`, `rejecting_preserves_obligation`, `all_preserves_obligation` | Checked with explicit active-interval condition for R |
| STAGE2 §3: accepting runs satisfy extracted seeds | `accepting_finite_obligation`, `accepting_simple_suffix`, `accepting_active_obligation`, `accepting_renewal_seed`, `accepting_active_finite_witness` | Checked; retained finite checks are not replaced by true |
| STAGE2 §4: fixed product and α=β(Inf(i)) | `productRun`, `productColours`, `EmersonLei`, `product_projection`, `product_language`, `product_complement` | Checked; language equality explicitly requires two-sided per-component equality |
| STAGE2 §5: all maximal opposite children, finite tree / depth | `MaximalOpposite`, `maximal_opposite_extension`, `ZTree`, `buildTree`, `child_cover`, `ZTree.path_length_le` | Checked reference builder, including empty colour universe |
| STAGE2 §5: generic maximal-model SAT builder | `unblocked_upward`, `maximal_under_blocks`, `maximal_builder_complete` | Abstract soundness/completeness checked; C query/loop refinement remains trusted |
| STAGE2 §5: ordinary one-sibling update | `ZTree.step`, `ZTree.advance`, `ZTree.step_valid`, `ZTree.advance_valid`, `treeRun_valid`, `treePriority_le` | Checked operation, valid paths and priority bound |
| STAGE2 §5: least recurrent anchor, stable prefix and sibling cycling | `Often`, `rotation_visits`, `ZTree.node_motion`, `ZTree.recurrent_run` | Checked by tree induction: infinitely many root rotations, or a stable child suffix |
| STAGE2 §5: recurrent-set acceptance | `recurrent_eventually_subset`, `recurrent_shift`, `ZTree.recurrent_run`, `tree_minEven` | Checked: min-even iff α(S), for every colour stream, including m=0, empty marks and constant α |
| STAGE2 §5: max-odd export P−p | `parity_export`, `tree_export`, `tree_maxOdd` | Checked: max-odd iff α(S); every ordinary exported priority is positive |
| STAGE2 §6.1: failed clause, raw constraint (6), exact progression (7) | `failed_clause`, `failed_flat_clause`, `global_all_implies`, `U_rawAll`, `BadFlatConstraint`, `initial_badFlat`, `flat_residual_step`, `badFlat_step` | Checked for the actual raw all-field and exactly retained finite residual |
| STAGE2 §6.2: flush old false finite candidates | `flush_false_window`, `flatCandidates_split`, `flatCandidates_bound`, `badFlat_flush` | Checked: old candidates become Boolean false; remaining supported X tails belong to selected bodies |
| STAGE2 §6.3 (8): protect a constraint / lose a protector | `badFlat_remove`, `removeBody_shorter`, `minimal_protectors`, `flat_constraint_protected`, `minimal_extractPass_constraint` | Checked throughout every intermediate removal pass; a lost H strictly reduces the proof constraint |
| STAGE2 §6.4 (9): eventually all extracted seeds false | `neverBot_finite_obligation`, `flat_eventually_false_seeds` | Checked: violating G(q) and never-false A imply an eventually false ρ(raw); finite first-pass results are excluded, disabling retry |
| STAGE2 §6.5: full G(q) converse | `flat_global_language` | Checked: Inf(marks G(q)) iff satisfaction of G(q); no false-seed premise remains |
| STAGE2 §6.5: dual F(r) | `flatR_dual`, `flat_eventual_language` | Checked: Fin(marks G(bar(r))) iff satisfaction of F(r), on the identical complete run |
| STAGE2 §8: assembled admitted grammar | `ProductPresentation`, `admitted_product`, `presentation_parity`, `admitted_grammar` | Checked: a fixed finite component product and covered global tree recognize every admitted formula in both parity orientations |
| STAGE2 §9.1: C's canonical-class grouping condition | `compatibleGroups_identity`, `compatibleGroups_nonidentity`, `nonempty_cosafety_identity`, `compatibleGroups_sat`, `compatibleGroups_admitted`, `compatibleGroups_parity` | Checked: finite operands join co-safety exactly when its folded canonical class differs from the Boolean identity; grammar closure and both parity languages |
| STAGE2 §9.1: canonical admission and grouped constructor success | `check_admission_exact`, `canonicalCheck_shannon`, `canonicalCheck_admitted`, `groupable_all_leaves`, `syntaxAcceptance_success`, `factoring_admission_exact`, `factoring_grouped_success`, `factoring_language`, `canonicalCheck_product`, `factoring_grouped_parity` | Checked conservative support domain, actual recursive canonical calls on remaining operands and both groups, failure propagation, original fallback, exact success domain and language preservation; factoring equivalence is explicit; C representation/status bridge trusted |
| STAGE2 §9.2: G/∧ and F/∨ distributions | `distribute_G_conj`, `distribute_F_disj`, `distribute_G_context`, `distribute_F_context` | Checked for every infinite word and arbitrary syntax context, including under frozen modalities; C traversal bridge trusted |
| STAGE2 §9.3: terminally decided products | `terminal_all_marks`, `terminal_recurrent_colour`, `terminal_product_decided`, `absorbing_maxOdd`, `terminal_absorption` | Checked constant substitution in fixed β, complemented occurrences, absorbing priorities P/P−1 and arbitrary entering/finite-prefix priorities |
| STAGE2 §9.4: current-AP care traversal | `restrictCurrent`, `unfoldCare`, `unfolding_care_exact`, `unfolding_syntax_care_exact`, `unfolding_care_root`, `care_finite_return`, `care_frozen_next`, `care_shannon`, `care_modal_shannon` | Checked syntax/class reference care, current AP branch recombination and frozen X; imperative DAG order/memo-key bridge trusted |
| STAGE2 §9.5: fragment bounds with exact fallback | `syntax_tag_lower`, `syntax_operator_upper`, `tags_shannon_intersection`, `bounds_intersection`, `bounded_tag_test_exact`, `support_pruning_tag`, `cached_lower_refinement`, `exact_tests_preserve_order` | Checked structural syntax bounds, actual support/cofactor intersection, arbitrary masks, stable lower caches, exact fallback and safety-first order; C bitset/cache bridge trusted |

### Task J: general Π₂ converse proved

**Focused follow-up outcome: proved.** `TlsfProofs/Dpa/GeneralConverse.lean`
now proves `general_eventually_false_passes` in a stronger form: the all-field
need not stay propositionally nonfalse. The default build checks the theorem.

```lean
theorem general_eventually_false_passes
    (x : Class ap) (hx : NNFClass x) (hpi : HasTag Pi2 x)
    (w : Word (Fin ap)) (hfalse : ¬Holds w 0 x) :
    ∃ N, ∀ n, N ≤ n →
      ¬Holds w n (extractPass (rawAll x w n))
```

`general_eventually_false_protected_constraints` proves the structural target
as well: every sufficiently late raw position has a false co-safety consequence
C whose supported X atoms remain protected in every NNF weakening y between
raw and C. `extractPass_protected_constraint` preserves it through every
simultaneous deletion, with protection recomputed at each pass.

The proof has two parts:

1. **Π₂ induction.** `pi2_cosafety_failure` extends the failed-clause argument
   through conjunction, disjunction, X, G, R and W, taking co-safety formulas as
   leaves. `class_pi2_cosafety_failure` lifts it to arbitrary NNF Boolean
   classes using the checked false-clause construction. A false co-safety
   consequence persists semantically under exact derivatives; it need never
   become propositionally false. This gives
   `general_eventually_false_cosafety_constraints` and the intermediate
   `general_eventually_false_reductions`.
2. **Smallest closed alphabet.** Among all false co-safety raw consequences
   at all times, choose one with a smallest finite subformula-closed alphabet
   B (`BadCosafetyConstraint`). Exact raw steps preserve B. A maximal X in B
   disappears after one step, contradicting minimality. Every supported X
   therefore lies below a maximal non-X modal atom H. Minimality forces H to
   be supported by C and by every intermediate weakening y: otherwise the
   false-cofactor argument removes H, giving a strictly smaller closed
   alphabet and another semantically false consequence. The same alphabet
   works at every later time, which proves
   `eventually_protected_of_cosafety_constraint`. No pigeonhole, numerical
   threshold, alternating-automaton correspondence or propositional flush is
   required.

`false_pass_disables_retry` then rules out retry at the relevant positions on
a never-false all-field, and `converse_of_eventually_false_passes` applies the
accepting-renewal theorem with its retained nonconstant finite remainders.
The resulting unconditional theorem `general_pi2_converse` proves
`GeneralPi2Converse`; `general_pi2_language` states
`Inf (marks x w) ↔ Holds w 0 x` for every NNF class with `HasTag Pi2 x`.

`false_cosafety_need_not_flush` remains valid: `F a` on the all-false word is
semantically false and every finite derivative is propositionally nonfalse.
The successful proof uses semantic falsity and closed-alphabet descent.

**Remaining boundary.** There is no remaining general Π₂ component-language
gap in the Lean model. The research-mode alignment below closes the two
operational mismatches found in review; the C representation refinement remains
trusted. Task T below adds executable component simulation and general
canonical-support Σ₂ dual classification. The §9 complete constructor and
admission results have not been extended to the general Π₂/Σ₂ grammar.
General admission remains opt-in through
`allow_unproved`; default admission is unchanged.

The repeatable search is `tools/golden/dpa_pi2_converse.py`. The recorded run
compared both language inclusions with Spot 2.16 through the existing
`dpa_equivalence.cpp` harness and `--allow-unproved`:

- 7,058 small/targeted formulas, including duals. The exhaustive part enumerates
  mixed Π₂ formulas with at most six grammar nodes over positive a,b, modulo
  commutativity of ∧/∨; direct safety/co-safety cases are omitted. The targeted
  families cover disappearing F/U/M protectors, delayed finite obligations,
  `GF(a ∧ X b)`, `G(a → F(X b ∧ XX c))`, R/W, and mixed literal signs.
- 4,000 deeper cases, including duals, from seed 80002931: 2,000 generated Π₂
  formulas of 7–18 grammar nodes over a,b,c and their negations (a signed literal
  counts as one leaf), alternating G/co-safety bodies with general Π₂ bodies.
- **11,058 equivalences; zero mismatches, declines, or timeouts.** The corpus
  SHA-256 is `498e422a7bec503f9040f2115461984fa0100c9df9d6ce541ad9bb1e2bcac9d9`.
  Metadata and source fingerprints are in `../docs/lazy-dpa/TASK-J-SEARCH.json`.
  These tests exercise C's canonicalization, factoring and complete DPA; they
  do not test every unnormalized class permitted by the Lean proposition.

For this run, the four current `src/lib/dpa*.c` translation units and the
current harness were compiled serially with GCC 15.3.1 (`make -j1`), linking
existing OxiDD and unchanged library infrastructure from the sibling
`tlsf-proofs/build`. No C compilation overlapped Lean. With a normal build of
this checkout, reproduce the corpus/checks with:

```sh
meson compile -C build -j1 dpa_equivalence
python3 tools/golden/build_legacy.py build
python3 tools/golden/dpa_pi2_converse.py build/golden-legacy \
  --output /tmp/tlsf-task-j-search
```

The bounded negative search is implementation evidence only; it is independent
of the new kernel proof. The proof-only Task J follow-up did not rerun the
C/Spot search; the research-mode alignment below does.

Validation: `LEAN_NUM_THREADS=1 lake build` succeeds with zero warnings. The
`\b(sorry|admit|axiom|native_decide)\b` scan of every Lean source is empty.
The dependency audit of the new general converse/language, protected-constraint
and first-pass results, together with `admitted_grammar`, contains
only `propext`, `Classical.choice` and `Quot.sound`.

### Extractor correspondence in both modes after review

`src/lib/dpa_formula.c:891` walks the retained NNF syntax to collect X
subformulas; `src/lib/dpa_formula.c:914` starts that walk only at supported
non-X modal atoms of the current reduced class (F/U/M in research mode).
This implements `subformulas` and `Protected` at
`TlsfProofs/Dpa/Classes.lean:503` and `:520`. Boolean materialization of a
protector's operands cannot remove a protected X. Only X atoms are interned,
with their operands frozen. `src/lib/dpa_formula.c:938` still performs
REDUCE, repeated simultaneous DROP_X with protection recomputed after each
removal, unfolding, and the finite-result retry in that order, matching
`reduce`, `dropX`, `extractPass`, and `rho` at
`TlsfProofs/Dpa/Classes.lean:578`–`:596`. Stepping and the ordered transition
table at `src/lib/dpa_dela.c:5`, including renewal with retained finite
remainders, are unchanged.

In research mode, `src/lib/dpa_formula.c:81` intersects the structural tags
of frozen atoms over exact class support. It does not recursively materialize
modal operands to refine those tags, during admission or expansion. Thus the
Π₂ branch of `src/lib/dpa_formula.c:189` tests `HasTag Pi2` on
`Class.ofFormula` of the transported NNF syntax: `HasTag` is at
`TlsfProofs/Dpa/Classes.lean:489` and `Pi2` at
`TlsfProofs/Dpa/Converse.lean:35`. The Σ₂ branch uses the structural dual
classification; component orientation and sharing at `src/lib/dpa_dela.c:93`
select the corresponding Π₂ run. These are the syntax/tag and extractor
algorithms assumed by `general_pi2_language` at
`TlsfProofs/Dpa/GeneralConverse.lean:862`. This correspondence still trusts
the C-to-Lean representation bridge described below.

The regressions in `test/unit/dpa_stage2.c` check the exact initial rejecting
class for `G(F(a | (a & X F b)) | X F b)`, which must be
`a | F(a | (a & X F b)) | X F b`, not true. They also exercise both operands
of U/M protectors. `G(F a | (F a & F(G b)))` and its NNF dual decline in
research mode: absorption inside a frozen operand alone cannot establish
`HasTag Pi2`. Default admission still accepts its existing canonical fragment,
so some formulas accepted by default can now decline in research mode.
Absorption in the outer class support remains available in both modes.

The syntactic-protection change also applies with `allow_unproved=false`.
**The default admission predicate is unchanged, but the automata can differ.**
The default theorems use the same extractor: `initial` and `transition` in
`Stage1.lean` call `rho`; `marks` and `run` refer to that table.
`flat_global_language`, the GF/FG corollaries and `admitted_grammar` in
`Converse.lean` consequently concern `Classes.lean`'s syntactic `Protected`,
`dropX`, `extractPass` and `rho`. There is no mode-parameterized extractor in
Lean. Safety/co-safety runs bypass extraction by `simple_run`; this does not
make the complete admitted fragment insensitive to protection. The flat
converse explicitly uses `flat_constraint_protected` and
`minimal_extractPass_constraint` during simultaneous X removal.

For example, `G(F(a | (a & X X b)) | X X b)` is in `Admitted`: the F body
and `X X b` are finite windows, so its body is `FlatQ`. The supported F atom
protects `X X b` syntactically although its operand materializes to `a`.
The Lean initial rejecting class is `a | F(a | (a & X X b)) | X X b`,
not true. HEAD `ea89484` implements this extractor in both modes; parent
`b149ef5` instead loses this protection when it materializes the F operand.
The existing theorems do not establish correspondence for that older
extractor. Keep the syntactic walk in both modes, subject to the same trusted
C representation/tag/constructor bridge as the other correspondence claims.
This is not a new certification of the whole C implementation.

The example expands to **4 states on the parent and 5 on HEAD** in either
mode. At `max_states=4`, the parent completes and HEAD declines with
`TLSF_DPA_STATE_LIMIT`; both unrestricted automata pass Spot equivalence.
`default_syntactic_protection` in `test/unit/dpa_stage2.c` pins the initial
rejecting field, the five-state result and the four-state budget decline in
both modes. The equivalence suite also checks the example and its negation.
See [the default-effect audit](../docs/lazy-dpa/DEFAULT-PROTECTION.md) for
the paired measurements and their resource limits.

The matched existing equivalence invocations (110 fixtures and 72 random
cases) pass on both revisions with all 182 state counts unchanged. The 24
inventory names recoverable from `STAGE2-INVENTORY.md` decline as unsupported
by default on both; all admit in research mode and hit expansion budgets
(five host, two BDD, seventeen deadlines). The complete 69-objective rerun is
pending the missing external name list, especially its 45 default-admitted
objectives; the historical admission totals are not a new measurement.

Validation of this alignment, with builds and tests serialized in a 5 GiB
cgroup and no OOM events:

- All **378 Meson tests pass**, including the failure-path gates,
  `dpa_equivalence_research` (107 Spot equivalences and three expected admission
  declines) and `dpa_random_research` (72 Spot equivalences).
- The full `dpa_pi2_converse.py` run checks **11,060 Spot equivalences**:
  7,060 small/targeted cases and 4,000 deeper cases, including duals, with
  seed 80002931. There are no mismatches, declines or timeouts. Corpus SHA-256:
  `7cd9a574eb6145e889651d9b321729d253972cc449262cc31cbfda91c2854cee`.
- A clean `LEAN_NUM_THREADS=1 lake build`, with Lean invocations serialized
  by `flock`, passes all 19 jobs with zero warnings.
- CI's pinned clang-format **22.1.8** passes on every changed C/C++ source
  and header. The final C build check and Meson test run are warning-free;
  the initial full GCC 15.3.1 compile reports existing warnings in unrelated
  lexer, AST and GR(1) code. The changed DPA C code emits none.

Before general admission can become the default, the reviewer's remaining
obligations are:

- Close the C-to-model correspondence for nested tags and protection,
  preserving stepping, extraction, retry, renewal, and acceptance. The
  operational algorithms now align; a verified representation refinement is
  still required.
- Extend the conservative constructor/admission results to general Π₂/Σ₂,
  including NNF dual classification and component sharing, and instantiate
  the existing product/parity results.
- Validate that implementation and policy change against the required C/Spot
  and failure-path gates.

### Task T: executable representation and research component

`TlsfProofs/Dpa/Impl/Classes.lean` provides executable truth tables over an
explicit finite ordered list of modal atoms. `table_exact` proves that, on
that alphabet, equality of the emitted vectors is exactly equality of the
semantic `Class` values. `equivalent_exact` supplies an executable equality
test for any two formulas by covering both alphabets. `uses_exact` proves that
the executable support test is exactly `Uses`; `hasTag_exact` lifts any
executable atom predicate to the semantic `HasTag`. These tests account for
Boolean absorption and keep frozen modal operands and temporal duals
independent. Duplicate atoms are removed before enumeration.

Run the diagnostic executable from `proofs/`, using the Task T resource limits:

```sh
mkdir -p ../build-scratch-t/tmp
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  env TMPDIR="$PWD/../build-scratch-t/tmp" LEAN_NUM_THREADS=1 \
  lake exe dpaImplChecks
```

The 106 checks exercise absorption, constants, essential and absent support,
frozen operands, independent duals, both U/M protector operands, nested X,
protector loss, the review-k/l initial remainders, retry, simultaneous STEP,
and nonconstant finite retention at renewal. They also cover canonical dual
congruence, Σ₂ orientation with absorbed unsupported syntax, mixed Π₂/Σ₂
canonical admission and review-i's nonempty co-safety identity case. Ten
additional Büchi checks cover alternating conjuncts/disjuncts, a missing
conjunct, constant true/false (including zero colours), the initial bit,
the incoming-mark delay, source priorities, and the state split. Eleven store
checks cover fresh Π₂/Σ₂ orientation, absorbed equal-class hits, cached-dual
hits, repeated Σ₂ insertion, append indices, preservation of old entries,
weak-dual sharing in parity mode, its separation in Büchi mode, and lookup
order when an earlier cached-dual hit precedes a later equal-class hit. Eight
assembly checks cover constant acceptance, canonical tautology folding,
mixed Π₂/Σ₂ literals, shared leaves, a Shannon branch sharing a cached dual,
old indices, and both grouped identity branches. Twenty-eight transport checks
cover ID sorting, duplicate/constant folding, accumulated X through Boolean
nodes, resets under frozen modal operands, preservation of frozen absorption,
all temporal duals, implication/equivalence polarities, and strong-next rejection
inside an absorbed branch. The X-distribution check explicitly distinguishes
language preservation from frozen-class equality. Ten canonical selection
checks cover constant/whole fast paths, mixed Π₂/Σ₂ Shannon plans in both
variable orders, skipped absorbed variables, absorbed unsupported syntax,
unsupported declines, and frozen cofactor operands.
`class_checks`, `component_checks`, `dual_admission_checks`, `buchi_checks`,
`store_checks`, `assembly_checks`, `transport_checks`, and `selection_checks`
check these same executable definitions by kernel reduction.

**Task T3, item 1 proved at the decoded-syntax boundary.**
`Impl/Transport.lean` follows `formula_impl` at `src/lib/dpa_formula.c:394`
directly, with C's negation flag and pending X count. It does not call
`to_nnf` or use `nnf_sat` to stand in for the traversal. `termBoolean_language`
and `termBoolean_nnf` model ID sorting, duplicate elimination and constant
folding in `term` at `src/lib/dpa_formula.c:254`. The rank parameter is the
permanent ID in an append-only term arena; the proofs work for every rank.
`termUnary_language` covers the X/F/G constant branch, and
`wrapNext_language` proves C's repeated wrapping at `src/lib/dpa_formula.c:388`.
The direct successful-traversal invariant is:

```lean
Impl.transport_language (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
  (negate : Bool) (pending : Nat) (t : Formula (Fin ap))
  (ht : Impl.transport rank f negate pending = some t) (w : Word (Fin ap)) (j : Nat) :
  Sat none w t j ↔
    (if negate then ¬Sat none w f (j + pending) else Sat none w f (j + pending))
```

Boolean children inherit `pending`; modal children restart at zero before
wrapping the frozen result. All implication/equivalence branches follow C's
operand/polarity choices. `transport_domain` identifies exactly the expanded
syntax without strong-next, before resource/invalid-input failures.
`transport_nnf` supplies NNF for every successful result.
`transport_class_language` gives `NNFClass (Class.ofFormula t)` and its original
input language at every word/position, matching materialization's frozen
modal operands at `src/lib/dpa_formula.c:366`. The result is language equality:
X(p ∧ q) and X p ∧ X q are still different classes over independent frozen
atoms. C hash-consed IDs, pointer memoization, AP-name resolution and bounded
successful-execution refinement remain representation obligations; no numeric
C ID equality or automaton-constructor theorem is claimed here.

`Impl/Tags.lean` proves all five executable structural classifiers exact,
including `pi2b_exact` and `sigma2b_exact`. `classTag_exact` identifies their
canonical-support intersection with `HasTag`; `researchAdmitted_exact` covers
the research whole-class fast path. It does not identify this fast path with
the full Boolean acceptance recursion. As in current C, absorption inside a
frozen operand does not grant a research tag.

`Impl/Extractor.lean` proves `protected_exact`, `reduce_exact`, `dropX_exact`,
`elide_exact`, `extractPass_exact`, and `rho_exact`. The executable fuel is the
length of its actual syntax's modal-atom list. `semantic_elideFuel_unique`
proves agreement with the semantic model's representative-dependent fuel:
both reach the same stable result. Retry uses canonical equality and the
exact finite-support predicate.

`Impl/Component.lean` proves `initial_exact`, `transition_exact`, `run_exact`,
and `marks_exact`. Every transition row is covered, including retained finite
remainders. Its main executable component theorem is:

```lean
Impl.pi2_language (f : Formula (Fin ap)) (hn : NNF f)
  (hpi : Impl.classTag .pi2 f = true) (w : Word (Fin ap)) :
  Inf (Impl.marks f w) ↔ Sat none w f 0
```

`pi2_complement` gives Fin acceptance on the same run. `pi2_parity` and
`pi2_complement_parity` give Stage 1's one-set numeric min-even/max-odd
languages. These do not identify that numeric table with C's global tree or
its terminal shortcuts. All new main theorem dependency audits contain only
`propext`, `Classical.choice`, and `Quot.sound` (some use fewer).

`Impl/Dual.lean` proves `dual_class_congr`: NNF dualization respects semantic
class equality. `class_sigma2_dual_pi2` proves that exact Σ₂ support becomes
exact Π₂ support under dualization; it does not assume the chosen syntax is
itself Σ₂. The key substitution is
`dualAssignment σ a = !propEval σ (dual a)`, with
`propEval σ (dual f) = !propEval (dualAssignment σ) f` for NNF f. Support
locality and the structural dual grammar then prove the classification.
Thus `sigma2_language` gives `FinMarks (Impl.marks (Impl.dual f) w) ↔ Sat none
w f 0` for every NNF f with `Impl.classTag .sigma2 f = true`.

`research_component_language` covers every NNF whole class accepted by
`researchAdmitted`: C's Π₂-first orientation, followed by Fin acceptance on
the Σ₂ dual, has both one-set numeric parity languages equal to the formula.
`Impl/Admission.lean` checks the full canonical research support-union
predicate and its Shannon recursion, and proves the executable grouping
decision equal to §9.1's corrected reference. This includes the folded-class
identity branch, rather than a test of list nonemptiness.

**Task T2, item 1 proved.** `Impl/Buchi.lean` models the Shannon walk of
`src/lib/dpa_dela.c:203`, the residual/reset and target completion bit at
`:272`, the source-state priority at `:278`, and the initial incoming bit at
`src/lib/dpa.c:300`. Canonical true/false tests enumerate the finite colour
truth table; the BDD canonicity boundary is unchanged. `seenColours_exact`
proves substitution of all colours on an edge. `roundRun_residual` identifies
every residual with the original acceptance after substitution of the colours
seen since the last reset. For every positive Boolean acceptance β and every
colour stream (without any bounded-gap assumption):

```lean
Impl.completedRounds_language (β : Impl.ColourDag m)
  (hp : Impl.PositiveColours β.eval) (colours : Nat → Fin m → Bool) :
  Inf (Impl.completedRounds β colours) ↔ EmersonLei β.eval colours
```

The proof uses a common last-occurrence bound for nonrecurring colours in one
direction and eventual visits to all recurring colours in the other. It does
not test β on individual edges. `PositiveAcceptance.positive` discharges hp
for constants, positive component colours, and conjunction/disjunction, the
grammar used by `src/lib/dpa_formula.c:622` (dual sharing is disabled at
`src/lib/dpa_dela.c:99`). `incoming_state_split` proves equal residuals with
different incoming bits have the same next state but different source
priorities. `incomingMarks_inf` proves the one-step delay and finite initial
bit preserve Inf. `incomingMarks_language`, `buchiPriority_language` and
`positive_buchi_language` give the state-based Büchi and actual 0/1 max-odd
languages. Constant true/false and an empty colour alphabet are included.
No counterexample, C change, narrowing, or coverage impact was needed.
This closes the round-monitor obligation, independently of the still-open
syntax transport and constructor correspondence.

`Impl/Store.lean` now models the component loop at `src/lib/dpa_dela.c:93`.
`StoreValid` requires NNF Π₂-oriented stored formulas and a cached temporal
dual related in the direction in which the pair was constructed. It does
not require a temporal dual to be Boolean complementation, or syntactic
double-dual identity before constant normalization. `lookupComponent_represents`
checks the exact insertion-order equal-class / cached-dual tests.
`internComponent_valid`, `internComponent_represents` and
`internComponent_language` prove invariant preservation and exact literal
language after either cache hit or fresh Π₂/Σ₂ insertion. The result's index
is in bounds. `internComponent_preserves_index`,
`internComponent_preserves_colours` and `internComponent_preserves_literal`
preserve every previous coordinate, its entire complete stream, and its
oriented recurrent truth. `internComponent_buchi_positive` proves that
Büchi mode's Π₂ insertions return positive literals, including cache hits.
`store_productColours` identifies these permanent coordinates with the
abstract fixed product; `storeTruth_componentTruth` identifies their truth
vectors in a valid store. Selection of the full constructor remains separate.

`Impl/Assembly.lean` compiles explicit successful construction plans containing
constants, whole classes, binary Boolean combinations and Shannon branches.
Canonical constant classes return constant acceptance without adding a
component, as in `src/lib/dpa_dela.c:117`. `assemble_spec` proves store growth,
validity, index bounds and exact acceptance language throughout this recursion.
`ColourAcceptance.eval_extends` is the intermediate acceptance invariant:
later insertions cannot change the truth of earlier branches. Consequently
`assemble_presentation` gives `ProductPresentation` for the actual returned
store and indexed acceptance. `assemble_shannon_presentation` instantiates
this result for a source class's Boolean cofactor decomposition.
`groupedPlan` uses the executable folded-class identity test; its language
theorem reduces to `compatibleGroups_language`. `assemble_grouped_presentation`
proves a concrete shared-store presentation for safety/co-safety/finite
groups and valid recursive rest plans, for either Boolean operator and both
identity branches. This closes the assembly lemma from the previous boundary.

`Impl/Selection.lean` now selects the **uncached canonical fallback** at
`src/lib/dpa_dela.c:117`. `cofactor_eval` proves the executable Boolean
cofactors exact, without descending into frozen modalities; `cofactor_nnf`
preserves NNF. `cofactor_shannon` reconstructs the original class.
`selectCanonicalPlan` checks constants, whole-class admission, and then the
first essential atom in the supplied variable order. `canonicalPlan` supplies
the syntax's finite alphabet sorted by permanent atom ID. `orderAtoms_mem`
and `orderAtoms_sorted` prove the structural sorting reference preserves
membership and gives increasing ranks. The proof covers
every rank/order, including variables removed by canonical absorption.

`canonicalPlan_domain` proves success exactly when `canonicalResearchCheck`
accepts. `canonicalPlan_spec` proves `AcceptancePlan.Valid` and source-class
equality for the plan returned by this executable selector; neither is an
assumption about an arbitrary plan. `transported_canonical_source` proves
that selected plan valid and its source language equal to the original input
at every word and position. `transported_canonical_presentation` composes
that result with shared-store assembly to give `ProductPresentation` for
the original input formula and the compiled selected plan.
`admitted_canonical_presentation` supplies the actual successful selector
result from executable research admission, without assuming a valid plan or
choosing fresh existential components.

`Impl/Cache.lean` now executes the canonical constructor with the acceptance
cache in its C position, before whole-class admission. `lookupAcceptance_spec`
proves class-key hits, and `AcceptanceCache.Valid.extends` preserves both
index bounds and languages as the store grows. `runCanonical_refines` proves
successful construction, store extension, store/cache validity, index bounds
and exact input language for every selected canonical plan. Its `highFirst`
parameter allows either order of C's nested Shannon child arguments; the top
atom's component call always comes first. The executable `calls` list records
component calls in that order, including component-store hits and excluding
acceptance-cache hits. `runCanonical_hit` proves a hit leaves the complete
state unchanged and makes no component calls. Unread constant-cache writes
are omitted, and canonical cache keys use the same decoded class equality
as the rest of the model.

`cached_uncached_language` refines the earlier uncached assembly, interpreting
each acceptance in its own actual store rather than equating different colour
numberings. `runCanonical_presentation` supplies `ProductPresentation` for the
cached constructor on the complete canonical research domain;
`transported_cached_presentation` supplies the original input language after
transport. The diagnostic checks cover both child orders with different
store numbering, a shared nontrivial cofactor, equivalent cache-key syntax,
cache reuse after growth and constants taking precedence over cache entries.
The complete grouped syntax selector and its rest-before-groups store-call
order remain separate; the earlier `groupedPlan` compiles groups first.

The repeatable dependency audit is `tools/golden/dpa_impl_audit.lean`:

```sh
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  env TMPDIR="$PWD/../build-scratch-t/tmp" LEAN_NUM_THREADS=1 \
  lake env lean -DwarningAsError=true ../tools/golden/dpa_impl_audit.lean
```

All 122 dependency reports contain only the three permitted axioms; the nine
concrete diagnostic proofs use only `propext`. Lean 4.35.0 builds the complete
library and `dpaImplChecks` with warnings as errors (64 Lake jobs). The 116 executable/kernel checks pass. The proof
source scan has no prohibited declarations or decision shortcuts. The source
reference guard now scans the executable modules as well as this README:
163 references / 121 anchored C/Lean targets pass. Both documentation gates
and the existing C Büchi golden gate pass (3/3, no rebuild): 313 admitted / 228
declined formulas, with 512 memberships per admitted formula.

**Current boundary for Task T/T2/T3/T4.** These are proved executable
transport, component, decision and canonical-cache milestones. Task T3 item 1
is proved at the decoded-syntax boundary; its item 2 canonical selector now
includes acceptance-cache hits and either per-execution Shannon child order.
Task T4 item 1's grouped syntax selection and store-call order remain open.
Its items 2–4 remain open and item 5 is deliberately not enabled. The
executable is a diagnostic, not a BFS automaton exporter; there is no matching
C dump or new C↔Lean automaton golden. The 30 existing golden files remain
unchanged at 2,986,929 bytes, including 541 DPA membership records; zero new
automaton goldens were generated. Recorded corpus coverage remains 148/217
by default and 155/217 with research admission; these milestones did not
rerun or change that corpus inventory. No new language counterexample or
narrowing of C was found. The frozen-operand absorption example was already
declined in research mode by the earlier review-l alignment.

The smallest remaining constructor lemma is **selecting and executing the
grouped syntax branch in C's rest-before-groups order**. The canonical
fallback, including its acceptance cache, now gives a concrete shared-store
presentation. `groupedPlan` and `assemble_grouped_presentation` still require
an explicit partition and recursive plans and compile the two groups before
the recursive rest. C's syntax traversal selects and executes rest operands
first, then calls canonical acceptance on the two folded groups in either
argument order. Language correctness of an arbitrary grouped plan cannot
identify those colour indices or supply the syntax-selected recursive plans.
The smart-constructor/transport and canonical-cache prerequisites are proved
above, but do not justify reordering those calls. Cached NNF duals cannot be
replaced by `Class.compl`, and an existential `admitted_grammar` witness does
not identify the constructor trace.

Further independent bridges remain: default recursive canonical tag refinement; the complete grouped constructor and
terminal product shortcut; C's lexicographically ordered tree/export; and
the offline BFS automaton goldens for corpus conjuncts and equivalence cases.
The independent `dpa_buchi_create` round-monitor obligation, incoming-mark
state split, component-store preservation and explicit-plan assembly are now
proved above. The concrete constructor selector and syntax bridge remain
necessary to identify its constructed positive acceptance with the transported
input. The transport language theorem now connects that input to the original
formula once the concrete selector is proved.
C code, production admission, and the remaining trusted
boundary below remain unchanged.

### C ↔ Lean correspondence

These are semantic correspondences, not a C verification certificate. Line
numbers refer to the merged worktree's formatted sources.

| C implementation | Lean model / result |
| --- | --- |
| `src/lib/dpa_formula.c:3`, `:50`, `:57`, `:64` — interned BDD classes, Boolean operations, cofactors | `Class`, `Class.meet`, `Class.join`, `Class.Implies`, `Uses`, `falseCofactor` |
| `src/lib/dpa_formula.c:81`, `:118`, `:127`, `:157` — exact tags and cached bounds | `finite`, `safety`, `cosafety`, `HasTag`, `syntax_tag_lower`, `syntax_operator_upper`, `tags_shannon_intersection`, `bounded_tag_test_exact` |
| `src/lib/dpa_formula.c:189`, `:505`, `:552` — admission and grouping guard | `FlatQ`, `FlatR`, `Admitted`, `check_admission_exact`, `canonicalCheck_shannon`, `canonicalCheck_admitted`, `groupable_all_leaves` |
| `src/lib/dpa_formula.c:563`, `:597` — operand partition and canonical identity comparison | `flattenOperands`, `partitionOperands`, `compatibleGroups_identity`, `compatibleGroups_nonidentity`, `compatibleGroups_sat` |
| `src/lib/dpa_formula.c:583`, `:617`; `src/lib/dpa_dela.c:117` — syntax construction, grouped branch and canonical acceptance | `canonicalAcceptance`, `groupedAcceptance`, `syntaxAcceptance`, `factoredAdmission`, `syntaxAcceptance_success`, `factoring_admission_exact`, `factoring_grouped_success`, `factoring_language`, `factoring_grouped_parity` |
| `src/lib/dpa_formula.c:254`, `:388`, `:394`, `:366` — smart constructors, pending-X transport, frozen materialization | `Impl.termBoolean_language`, `Impl.termUnary_language`, `Impl.wrapNext_language`, `Impl.transport_domain`, `Impl.transport_language`, `Impl.transport_nnf`, `Impl.transport_class_language`; numeric syntax-ID/memo refinement pending |
| `src/lib/dpa_formula.c:524`, `:610` — factoring | `compatibleGroups_parity`, `distribute_G_context`, `distribute_F_context`; concrete selector pending |
| `src/lib/dpa_formula.c:664`, `:876` — frozen STEP / current AP decision DAG | `stepSyntax`, `D`, `derivative` |
| `src/lib/dpa_formula.c:700`, `:761`, `:817` — frozen unfolding / current-AP care | `unfoldSyntax`, `U`, `unfolding_care_exact`, `unfolding_care_root`, `care_shannon`, `care_modal_shannon` |
| `src/lib/dpa_formula.c:664`, `:891`/`:914`, `:938` — REDUCE, protected X walk, repeated DROP_X and retry | `reduce`, `Protected`, `dropX`, `elide`, `rho`, `elide_stable`, `rho_retry_stops` |
| `src/lib/dpa_dela.c:5` — ordered table | `transition`, `transition_invariant`, `no_false_renewal`, `resume_unreachable` |
| `src/lib/dpa_dela.c:72`, `:327` — pair interning / initialization | `Pair`, `initial`, `initial_invariant` |
| `src/lib/dpa_dela.c:93`, `:117` — component/complement acceptance | `Inf`, `FinMarks`, `complete_complement`, `product_complement` |
| `src/lib/dpa_dela.c:93` — executable interning, ordered lookup, oriented cache and stable indices | `Impl.internComponent_valid`, `Impl.internComponent_language`, `Impl.internComponent_preserves_index`, `Impl.internComponent_preserves_colours`, `Impl.internComponent_preserves_literal`, `Impl.internComponent_buchi_positive` |
| `src/lib/dpa_dela.c:117` — executable uncached canonical plan selection and transport composition | `Impl.cofactor_eval`, `Impl.cofactor_nnf`, `Impl.cofactor_shannon`, `Impl.canonicalPlan_domain`, `Impl.canonicalPlan_spec`, `Impl.transported_canonical_source`, `Impl.admitted_canonical_presentation`; uncached reference |
| `src/lib/dpa_dela.c:117` — acceptance cache, top-atom call and either Shannon argument order | `Impl.lookupAcceptance_spec`, `Impl.AcceptanceCache.Valid.extends`, `Impl.runCanonical_hit`, `Impl.runCanonical_refines`, `Impl.cached_uncached_language`, `Impl.runCanonical_presentation`, `Impl.transported_cached_presentation`; grouped syntax execution pending |
| `src/lib/dpa_dela.c:117`; `src/lib/dpa_formula.c:583` — shared-store acceptance assembly from explicit valid plans | `Impl.assemble_spec`, `Impl.assemble_presentation`, `Impl.assemble_shannon_presentation`, `Impl.assemble_grouped_presentation`; complete selector/order refinement pending |
| `src/lib/dpa_dela.c:222`, `:308` — joint product and all-component progression | `productRun`, `productColours`, `product_projection`, `product_language` |
| `src/lib/dpa_dela.c:203`, `:272`, `:278`; `src/lib/dpa.c:300` — seen-colour residual, reset, incoming state split and initial bit | `Impl.seenColours_exact`, `Impl.roundRun_residual`, `Impl.completedRounds_language`, `Impl.incoming_state_split`, `Impl.incomingMarks_language`, `Impl.buchiPriority_language` |
| `src/lib/dpa_dela.c:170`, `:257`; `src/lib/dpa.c:536` — terminal substitution / absorbing products | `terminal_product_decided`, `absorbing_maxOdd`, `terminal_absorption` |
| `src/lib/dpa_zielonka.c:27`, `:39`, `:66` — models, upward blockers, maximal-child enumeration | `MaximalOpposite`, `unblocked_upward`, `maximal_under_blocks`, `maximal_builder_complete`, `buildTree` |
| `src/lib/dpa_zielonka.c:48`, `:153`, `:177`, `:187` — child ordering / paths / leftmost | `ZTree`, `ZTree.leftmost`, `ZTree.ValidPath`; C ordering/path-ID refinement pending |
| `src/lib/dpa_zielonka.c:198` — deepest containing anchor, one sibling, leftmost descent | `ZTree.step`, `ZTree.step_valid`, `treeRun`, `treePriority`, `ZTree.recurrent_run`, `tree_minEven` |
| `src/lib/dpa.c:246`; `src/lib/dpa_zielonka.c:231` — odd P and P−p | `exportBound`, `exportBound_odd`, `exportBound_large`, `parity_export`, `tree_maxOdd` |

### Trusted gaps and evidence boundary

- **BDD representation.** There is no verified refinement from OxiDD identities,
  complemented edges, interning, cofactors, support walks, or Shannon DAGs to
  the extensional Boolean functions used here. Allocation, host budgets,
  cancellation and failure propagation are also outside these Lean results.
- **Canonical NNF representation.** The executable decoded-syntax traversal
  now proves NNF and the exact original language, including C's smart
  constructors, constant folding and pending X placement. Its rank parameter
  abstracts permanent syntax IDs; hash-consing, pointer-memo keys, AP-name
  lookup, resource bounds and a representation refinement of successful C
  executions remain outside this theorem.
  Research-mode tags now inspect structural frozen syntax, and the protected
  walk inspects all syntactic X subformulas of supported modal atoms, as in
  `Protected`. Their imperative syntax IDs, support traversal and memo epochs
  still require representation refinement. Default admission retains its
  canonical operand refinement and conservative component theorem boundary.
- **Maximal-model builder.** The abstract upward-blocking completeness result
  and a terminating exhaustive semantic reference tree builder are proved.
  The C BDD/SAT query loop, model extraction, termination on successful bounded
  execution, and lexicographic child order are not refined. The reference tree
  uses its fixed Boolean-vector enumeration order; a C correspondence must
  map child occurrences to C's sorted-list lexicographic order.
- **Spot equivalence tests.** They provide implementation evidence only. They
  are not hypotheses, external oracles or substitutes for any Lean theorem.
  Task J's serial C build and bounded Spot research search are recorded above.

- **Refinement algorithms.** §9 is proved for semantic reference algorithms:
  the canonical admission decision tree, exhaustive Boolean syntax leaf guard,
  recursive grouped construction with canonical-class identity tests, terminal
  truth substitution, current-AP restriction and tag bounds. `canonicalCheck`
  tests exact support for the proved `Admitted` component grammar;
  `canonicalCheck_shannon` proves the original supported-atom/cofactor recursion,
  and `canonicalCheck_product` constructs a correct semantic product even for
  canonically absorbed unsupported syntax. The syntax constructor returns an
  optional formula denoting its acceptance language, rather than C colour IDs.
  Its `whole` parameter supplies C's whole-class fast-path test; the success and
  language results hold for every such test. Its structural fuel bound is
  `sizeOf(factored)+1` and is proved sufficient, not assumed to succeed.
  Identifying these with the C shared DAGs, owned IDs, AP order,
  memo epochs/cubes, cancellation, budgets and failure statuses remains a C
  refinement obligation. Resource failures are excluded from the admission
  success equivalence, as in the Markdown. These concrete constructor/language
  results concern conservative admission. `check_admission_exact` remains
  mode-independent. `general_pi2_language` now supplies the general Π₂
  component theorem separately; the §9 constructor/admission model has not
  been extended to `allow_unproved` Π₂/Σ₂.

Ancillary obligations retained from the earlier audit are the literal STAGE1
GF extractor case-split equality and identification of the one-set priority
table with the built one-colour tree path. The language theorems use the proved
sufficient GF seed bound and full global tree theorem, respectively; neither
ancillary statement is used as an unproved premise. The fixed-input finite
reachable-class closure is now proved by `finite_component_states`.

### Findings in the natural-language proofs

The requested §§5–9 language claims hold on the stated proved domain.
The §9.1 grouping rule needed correction, and its earlier Lean admission
audit omitted a constructor-success obligation:

- **§9.1 grouping condition.** Both the Markdown's former “C is nonempty”
  rule and Lean's former `C ≠ []` branch differed from C at
  `src/lib/dpa_formula.c:597`. C compares the folded canonical co-safety
  class with the outer operator's Boolean identity. For conjunction,
  `τ = F q ∨ (p ∨ ¬p)` is a co-safety operand whose class is true, despite
  `[τ]` being nonempty (`nonempty_cosafety_identity`). With safety operand
  `G s`, finite operand `p`, and remaining operand `GF r`, C therefore joins
  `p` to `G s`; the old rule joined it to `τ`. Both preserve language but
  choose different components. The reference and STAGE2-PROOF §9.1 now use
  C's canonical-class comparison for both Boolean operators.
- **§9.1 constructor success.** The former `factoredAdmission` returned
  `true` unconditionally after a successful grouping guard. Its theorem
  proved only the outer control-flow identity, not success of C's
  `syntax_acceptance` call at `src/lib/dpa_formula.c:617`. The replacement
  propagates optional failures from recursive remaining syntax and canonical
  acceptance of both grouped classes. `syntaxAcceptance_success` proves all
  these calls succeed under the exhaustive leaf guard; original admission,
  exact factoring and that guard imply successful grouped construction with
  the original language (`factoring_grouped_success`), including an exact
  complete product and both parity orientations (`factoring_grouped_parity`).
  `factoring_admission_exact` also covers the original fallback and rejection.
  Thus there is no counterexample under all three hypotheses in the
  conservative semantic model. Original admission alone cannot justify
  visiting canonically absorbed unsupported syntax; the leaf guard remains
  necessary for this implication. Language preservation explicitly requires
  factoring equivalence, while success-domain preservation does not.

The other distinctions concern proof organization and C correspondence:

- §5 is proved by tree induction. Infinite depth-zero anchors force ordinary
  rotation through every child (`rotation_visits`); otherwise a finite prefix
  leaves a stable child, to which the induction applies. Finite colour support
  supplies a common last-occurrence cutoff for colours outside S. This proves
  the stated recurrent-set argument, including constant acceptance and m=0.
- §§6.1–6.4 follow (6)–(9). The proof chooses a least-size failed clause among
  all reachable proof constraints. Equation (8) would strictly reduce this size,
  so every selected H survives every intermediate extraction pass after the
  old finite candidates have flushed. This is the finite-descent argument
  without choosing a numerical bound for the last protector loss. The
  per-window h+1 flush is proved by `flush_false_window`; `badFlat_flush`
  also handles arbitrary finite class remainders via the checked bad-prefix
  theorem. No candidate is discarded by the automaton, and no finite marked
  remainder is replaced by true.
- The general Π₂ component theorem is now checked by closed-alphabet descent
  (Task J above). The canonical frozen-operand/support distinction and
  imperative §9 bridge remain as described above; no C verification is claimed.

### Validation

Run the project with `LEAN_NUM_THREADS=1 $HOME/.elan/bin/lake build` from
`proofs/`. `TlsfProofs.lean` imports `Dpa.Refinements`, whose dependency chain
checks the original six Dpa modules and then the §9 module in the requested
order. The existing Lake settings
keep warnings as errors, one Lean worker thread, and asynchronous elaboration
disabled. No meson build or C tests run alongside Lean.

A successful build certifies the stated semantic theorems and their explicit
hypotheses; it does not verify the implementation bridges listed above.

On 2026-10-31 the full `lake build` succeeded with zero warnings. A whole-word
scan of Lean sources for prohibited proof placeholders/declarations and native
decision shortcuts returned no matches. Dependency audits of the derivative,
safety/co-safety/GF/FG languages, forward inclusion, accepting renewal seeds,
product language, full tree min-even/max-odd equivalence, flat G/F languages,
eventual false seeds, admitted grammar and §9 refinements contain only `propext`,
`Classical.choice` and `Quot.sound`. The existing 5 GiB cgroup was retained,
`LEAN_NUM_THREADS=1` was set for every build, and only one Lean process ran at
a time. All seven Dpa modules were also re-elaborated serially with warnings
treated as errors. The new grouping, canonical support, recursive constructor,
success-domain and grouped product/parity theorems were included in the
dependency audit.
