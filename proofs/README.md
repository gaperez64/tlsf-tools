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
When C collapses the decomposition to one cluster, keeping every entry gives
the original game directly, including for finite and output-dependent cases (`collapsed_cluster`,
`collapsed_cluster_realizable_fin`).

## Issue obligations

Names without an explicit namespace belong to `Tlsf`; counterexamples and
fixtures belong to `Tlsf.Examples`.

| Issue | Obligation | Theorem or definition |
| --- | --- | --- |
| #79 | Keep every environment entry; split only disjoint system outputs | `Clustered`, `cluster`, `cluster_same_environment`, `clusters_realizable` |
| #79 | Compose strategies with independent histories | `replay_ignores_outputs`, `replay_history`, `product_plays`, `cluster_product` |
| #79 | Empty system key is realizable | `empty_cluster_objective`, `empty_cluster_realizable` |
| #79 | Inconsistent disjoint assumptions cannot be pruned | `recurrence_conflict`, `issue79_original`, `issue79_pruned` |
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
| `src/lib/residual.c:16–25` | `substPass`, `substPasses`; instantiate `passes = ds.length + 1` |
| `src/lib/residual_plan.c:23–39` | `residual`, `residual_objective`; optional additional rewrites require separate semantic correctness |
| `src/lib/residual.c:27–56,65–74` | `Formula.atoms`, `normalize_untouched`; support collection and unused-output declaration removal |
| `src/lib/section_pattern.c:81–114,173–225` | `sectionFormula`, `objectiveFormula`, `objective_sat`; empty sections are true, all section conjuncts are included |
| `src/lib/residual.c:76–107` | `cluster`, `cluster_same_environment`; every cluster retains every environment entry |
| `src/lib/residual.c:125–230` | `Clustered`, `owner`, `clusters_realizable`; union-find gives disjoint output classes; the finite/output-dependent fallback keeps a single game |
| `src/lib/print_ltlxba.c:214–249`; `src/lib/nnf.c:75–86` | `Sat` for `next` and `strongNext`, `next_neg_dual`, `strong_next_neg_dual` |
| `src/lib/rewrite.c:101–116`; `src/lib/normalize.c:815–819` | `issue85_weak_next`, `issue85_negation`; finite next must retain its terminal behavior |
| `src/lib/decompose.c:69–75` | `elim_realizable_inf`, `elim_realizable_fin`, `clusters_realizable` delimit the mathematical basis of exactness |

The textual controller `ctl o := theta` is emitted outside `src/lib`, in
`src/tools/tlsfcompose/main.c:1027` in this working tree. `normalize_definitions` proves
that reconstruction by the composed letter map satisfies every such equation;
`play_decorate` supplies its Mealy implementation.

## Trusted gap

For CSNF decomposition, **only definition elimination and clustering are
proved**. The other CSNF templates—Phase B Skolem values, registers, reaction
and liveness schedulers—are guarded but unproved. The rewrite theorems above
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

Union-find and cluster-key construction must establish `Clustered`, and every
cluster must keep every environment entry. If an environment entry mentions an
output, or the semantics is finite, the C fallback must retain one full game,
including input-only system constraints. The `clusters_realizable` theorem is
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
for module in LTL Game Objective Passes Definition Cluster Examples Rewrites; do
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
trusted. The §9 constructor and admission results have not been extended to
the general Π₂/Σ₂ grammar. General admission remains opt-in through
`allow_unproved`; default admission is unchanged.

The repeatable search is `test/unit/dpa_pi2_converse.py`. The recorded run
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
python3 test/unit/dpa_pi2_converse.py build/test/unit/dpa_equivalence \
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

`src/lib/dpa_formula.c:866` walks the retained NNF syntax to collect X
subformulas; `src/lib/dpa_formula.c:889` starts that walk only at supported
non-X modal atoms of the current reduced class (F/U/M in research mode).
This implements `subformulas` and `Protected` at
`TlsfProofs/Dpa/Classes.lean:503` and `:520`. Boolean materialization of a
protector's operands cannot remove a protected X. Only X atoms are interned,
with their operands frozen. `src/lib/dpa_formula.c:913` still performs
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
| `src/lib/dpa_formula.c:394`, `:524`, `:610` — NNF/X transport and factoring | existing `Tlsf.Rewrites.nnf_sat`; `compatibleGroups_parity`, `distribute_G_context`, `distribute_F_context`; C traversal bridge trusted |
| `src/lib/dpa_formula.c:639`, `:851` — frozen STEP / current AP decision DAG | `stepSyntax`, `D`, `derivative` |
| `src/lib/dpa_formula.c:675`, `:736`, `:792` — frozen unfolding / current-AP care | `unfoldSyntax`, `U`, `unfolding_care_exact`, `unfolding_care_root`, `care_shannon`, `care_modal_shannon` |
| `src/lib/dpa_formula.c:639`, `:866`/`:889`, `:913` — REDUCE, protected X walk, repeated DROP_X and retry | `reduce`, `Protected`, `dropX`, `elide`, `rho`, `elide_stable`, `rho_retry_stops` |
| `src/lib/dpa_dela.c:5` — ordered table | `transition`, `transition_invariant`, `no_false_renewal`, `resume_unreachable` |
| `src/lib/dpa_dela.c:72`, `:292` — pair interning / initialization | `Pair`, `initial`, `initial_invariant` |
| `src/lib/dpa_dela.c:93`, `:117` — component/complement acceptance | `Inf`, `FinMarks`, `complete_complement`, `product_complement` |
| `src/lib/dpa_dela.c:198`, `:273` — joint product and all-component progression | `productRun`, `productColours`, `product_projection`, `product_language` |
| `src/lib/dpa_dela.c:170`, `:231`; `src/lib/dpa.c:365` — terminal substitution / absorbing products | `terminal_product_decided`, `absorbing_maxOdd`, `terminal_absorption` |
| `src/lib/dpa_zielonka.c:27`, `:39`, `:66` — models, upward blockers, maximal-child enumeration | `MaximalOpposite`, `unblocked_upward`, `maximal_under_blocks`, `maximal_builder_complete`, `buildTree` |
| `src/lib/dpa_zielonka.c:48`, `:153`, `:177`, `:187` — child ordering / paths / leftmost | `ZTree`, `ZTree.leftmost`, `ZTree.ValidPath`; C ordering/path-ID refinement pending |
| `src/lib/dpa_zielonka.c:198` — deepest containing anchor, one sibling, leftmost descent | `ZTree.step`, `ZTree.step_valid`, `treeRun`, `treePriority`, `ZTree.recurrent_run`, `tree_minEven` |
| `src/lib/dpa.c:244`; `src/lib/dpa_zielonka.c:231` — odd P and P−p | `exportBound`, `exportBound_odd`, `exportBound_large`, `parity_export`, `tree_maxOdd` |

### Trusted gaps and evidence boundary

- **BDD representation.** There is no verified refinement from OxiDD identities,
  complemented edges, interning, cofactors, support walks, or Shannon DAGs to
  the extensional Boolean functions used here. Allocation, host budgets,
  cancellation and failure propagation are also outside these Lean results.
- **Canonical NNF.** The existing core proves NNF semantic identities, but the
  lazy-DPA transport, constant folding, modal-operand canonicalization and
  canonical X placement are not connected to `NNFClass` by a C refinement.
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
  `src/lib/dpa_formula.c:596`. C compares the folded canonical co-safety
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
  `syntax_acceptance` call at `src/lib/dpa_formula.c:616`. The replacement
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
