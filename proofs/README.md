# TLSF decomposition and automaton proofs

This standalone Lean 4.35.0 project uses only core (`import Init`). `TlsfProofs`
checks every module and `Examples.lean` with warnings as errors. The kernel
checks all proof steps; there are no external packages or executable decision
shortcuts. Classical reasoning handles proposition cases, least witnesses,
and component-strategy choice. Main-result audits permit only `propext`,
`Classical.choice`, and `Quot.sound`.

The proofs establish mathematical ports of definition elimination, clustering,
conditional assumption pruning, selected rewrites, and an independent automaton
construction/validator. They do not verify the C binary or other CSNF controllers.

## Build

From `proofs/`, run one Lean compiler at a time. Dependencies make the default
build serial. As in acacia, library arguments are `-j1`, `-s2048`,
`-DElab.async=false`, with `warningAsError = true`. Do not impose a virtual-memory cap.

```sh
export PATH=$HOME/.elan/bin:$PATH
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=2048 LEAN_MAIN_USE_THREAD=0
lake build

# Sequential per-module diagnostics
for module in LTL Game Objective Passes Definition Cluster Pruning Examples Rewrites; do
  timeout 300 lake env lean "TlsfProofs/$module.lean" || exit $?
  timeout 300 lake build "TlsfProofs.$module" || exit $?
done
timeout 1500 lake build
```

## Decomposition model and guarantees

| Module | Model and guarantee |
|---|---|
| `LTL.lean` | Expanded constants/atoms, five Boolean connectives, weak/strong next, F/G/U/R/W/M. `Sat len w f j` uses `none` for infinite words and `some n` below n; out-of-word queries are false. Final weak next is true, strong next false. Locality reads only formula atoms at in-range positions from j; Boolean substitution is exact. |
| `Game.lean` | Input-first Mealy strategies use history and current masked inputs. `play` supplies infinite environment choices. `Realizable` wins at zero on every play; `FinRealizable` wins some nonempty prefix per play (`FinWin` order). Replay reconstructs each strategy's own history; decoration maps current letters; products play owned outputs. |
| `Objective.lean` | `objective_sat` connects ordinary `I -> (P && ((G Req && A) -> (G As && Gu)))` and strict `I -> (P && (As W !Req) && ((G Req && A) -> Gu))` to enabled section obligations, including safety before REQUIRE fails. |
| `Passes.lean` | One list-ordered substitution pass repeated exactly `passes` times. Substituting d then e means `setLetter d (setLetter e v)`. Ranked dependencies converge in any list order; enough passes establish every definition, including flipped equivalences. |
| `Definition.lean` | Realizability equivalence for both word kinds and ordinary/strict semantics, using the actual pass structure on retained entries. Decoration reconstructs a winning original strategy; the reverse uses section coverage and dependency-closed support, without requiring inactive conditional definitions. |
| `Cluster.lean` | Infinite-word realizability iff every cluster wins, for ordinary/strict semantics. All environment entries stay and use inputs only; each system entry's outputs share its key class. Unused keys win trivially, even with inconsistent environments. |
| `Pruning.lean` | `prune_realizable` for infinite ordinary/strict Mealy games. `Prunable isIn K D` requires input-only environment entries in D, disjoint from every K entry. `EnvSat D` witnesses `Initial D && G Require D && Assume D`; `envSat_of_word` bridges any satisfying infinite word, including lassos. Pinning D inputs and replay/locality transfer K obligations; adding D is pointwise weakening, also for strict safety. No finite theorem. |
| `Examples.lean` | Game counterexamples, rejected guards, finite-next boundaries/split failure, both Boolean-fixture orientations, and a list order needing multiple passes. |
| `Rewrites.lean` | NNF, weak/local/bottom-up rewrites, capped driver, pre-weak simplification, and spine decomposition. Exactness covers every valid position and word: both kinds in finite mode, infinite otherwise. |

`Admissible isIn strict kept ds passes` requires declared output definitions,
Boolean right-hand sides, distinct names, decreasing dependency ranks below
`passes`, and a covering system role for every entry mentioning a defined name.
`covers` allows equal roles, PRESET definitions, GUARANTEE uses of ASSERT, and
ordinary ASSERT uses of GUARANTEES. `covers_trans` checks every Boolean/role case
by kernel reduction; `Admissible.not_self` excludes self-dependence. The C loop's
`nelim + 1` passes instantiate `ds.length + 1`; any explicit valid rank bound works.

`Clustered isIn owner es` records input-only environments and system-output
ownership. `whole es` keeps every entry; `cluster es k` keeps all environments
and key-k system entries, including unused keys. After splitting,
`prune_realizable` compares K ++ D with K; all kept roles participate in
disjointness, and only witness input atoms matter. Without `EnvSat`,
`pruning_without_envSat_changes_verdict` refutes equivalence in both shapes.
Finite prefixes may end incompatibly, so no finite split is claimed. Keeping
one full cluster preserves finite/output-dependent games (`collapsed_cluster`,
`collapsed_cluster_realizable_fin`).

Names below are in `Tlsf`; fixtures/counterexamples are in `Tlsf.Examples`.

| Obligation | Theorem or definition |
| --- | --- |
| First split with every environment entry and disjoint system outputs | `Clustered`, `cluster`, `cluster_same_environment`, `clusters_realizable` |
| Compose strategies with independent histories | `replay_ignores_outputs`, `replay_history`, `product_plays`, `cluster_product` |
| Empty system key is realizable | `empty_cluster_objective`, `empty_cluster_realizable` |
| Prune input-only environment entries disjoint from all kept entries, given a joint infinite witness | `Prunable`, `EnvSat`, `prune_realizable` |
| Pinned-input strategy is causal and its replay matches the original play | `pinStrategy`, `replay_pin_history`, `play_pinStrategy` |
| Inconsistent disjoint assumptions can change the verdict in either shape | `recurrence_conflict`, `issue79_original`, `issue79_pruned`, `issue79_env_unsat`, `pruning_without_envSat_changes_verdict` |
| No eliminated output occurs on the environment side | `Admissible.occurrences`, `normalize_environment`, `elim_backward` |
| Original game wins by falsifying an output assumption; residual loses; guard rejects | `issue84_original`, `issue84_residual`, `issue84_rejected` |
| PRESET and strict ASSERT uses require a covering definition | `covers`, `covers_trans`, `enabled_cover`, `normalize_kept` |
| Unconditional preset counterexample and rejection | `issue86_original`, `input_q_unrealizable`, `issue86_rejected` |
| Exact Boolean elimination for both semantics and word kinds | `elim_realizable_inf`, `elim_realizable_fin` |
| Same C pass structure; every reconstructed equality holds | `sat_substPass`, `sat_substPasses`, `normalize_definitions`, `definition_sat`, `pass_order` |
| Current-letter Boolean decoder is causal and keeps inputs | `boolean_sat`, `normalize_inputs`, `play_decorate`, `transfer_inf`, `transfer_fin` |
| Future-dependent decoder loses against an answering environment; Boolean guard rejects | `issue91_noncausal`, `issue91_rejected` |
| One-letter weak next and the negation counterexample | `issue85_weak_next`, `issue85_negation` |
| Correct weak/strong next dualities | `next_neg_dual`, `strong_next_neg_dual` |
| Finite realizability distinguishes weak-next false from false | `issue85_finite_realizable`, `false_finite_unrealizable` |
| Conservative one-cluster finite fallback preserves the game | `collapsed_cluster`, `collapsed_cluster_realizable_fin` |
| Each component wins at a different length; conjunction loses | `finite_short_realizable`, `finite_long_realizable`, `finite_split_fails` |
| In-range future locality and exact Boolean substitution | `sat_locality`, `sat_subst`, `subst_absent` |
| Literal ordinary/strict section objective | `section_sat`, `weakUntil_guard`, `objective_sat` |
| Input-preserving causal strategy transfer | `transfer`, `transfer_inf`, `transfer_fin` |
| Guard is satisfiable for either equivalence orientation | `boolean_fixture` |

## Rewrite exactness

`TlsfProofs/Rewrites.lean` uses namespace `Tlsf.Rewrites`; `Ltl` abbreviates
`Formula` rather than introducing syntax.

```text
Exact fin f g := ∀ len, (fin = true ∨ len = none) → ∀ w j,
  InRange len j → (Sat len w f j ↔ Sat len w g j)
```

A valid finite position implies a nonempty word. Infinite mode requires `none`;
no valuation, core-shape, or flag-combination assumptions are added.

| Obligation | Theorem statement (implicit type/equality parameters omitted) |
| --- | --- |
| Congruence before pass soundness | `exact_congr` lifts Exact equivalences of immediate children; `bind_exact` and `context_exact` replace holes in arbitrary nested contexts, including negation and implication |
| Both NNF polarities | `nnf_exact f fin : Exact fin (to_nnf f true fin) f ∧ Exact fin (to_nnf f false fin) (neg f)` |
| Infinite-mode NNF is unsafe on finite words | `nnf_infinite_mode_finite_failure w` refutes equivalence for `not (X p)` on a one-letter word, reusing `Examples.issue85_negation` |
| Every local constant/redundancy rule | `simplify_exact f : Exact fin (simplify_weak_local f fin) f` |
| Every combination of local-rule flags | `apply_local_exact f flags : Exact flags.finite (apply_local f flags) f` |
| Bottom-up subformula replacement | `rw_pass_exact f flags : Exact flags.finite (rw_pass f flags) f`, using `bottom_up_exact` and `exact_congr` |
| NNF first, structural stability test, cap 200 | `apply_rewrites_exact f flags : Exact flags.finite (apply_rewrites f flags) f`; `rewrite_loop_exact` proves this for every fuel, even when no fixpoint is reached |
| High-level weak simplifier on core constructors | `pre_weak_exact f : Exact fin (pre_weak f fin) f` |
| Conjunction of all decomposed parts | `decompose_exact f : Exact fin (conjoin (rewrite_decompose f)) f`; `decompose_has_part` supplies the nonempty-list premise needed for strong next |
| Finite-safe temporal RULES rows | `route_push_g_in`, `route_push_x_in`, `route_push_strong_x_in`, `or_to_guarded_next_impl`, `or_to_guarded_strong_next_impl`, `or_to_response_impl`, `pre_spine_split_exact` |
| Expanded indexed-next identities | `pre_x0`, `pre_xn_flatten`, `pre_xn_bool_distribute` for `next_power`, with both-word exactness |
| Reject all three finite-disabled metadata rows | `sickert_rules_refused`, `sickert_limit_lift_refused`, `sickert_gf_w_refused`, `sickert_fg_u_refused` show the finite guard returns false |
| Counterexample to the unrestricted context equation | `sickert_finite_counterexample`: on one letter with p=true, `C[GF p]` is false and `(GF p && C[true]) || C[false]` is true for `C[z] = G(!z)` |

The distribution/guarded-implication biconditionals cover every valid position
of either word kind: `G(a&&b)=Ga&&Gb`, weak/strong `X(a&&b)=Xa&&Xb`, and
`!r||T a = r->T a` for either next or eventually. Taking the operand as the
remaining next chain covers chains too.

The Sickert example uses a nonpositive context. It refutes the unrestricted
context equation, not C's positive-NNF premise or a finite-only version of the
monotone identity. The three finite-refusal results independently establish the
metadata guard. No infinite-word Sickert soundness theorem is claimed.

Ports preserve first-rule order and structural equality. `Flags` has one Bool
per C flag; local traversals ignore `nnf`, matching removal of RW_NNF/RW_FINITE
and restoration of RW_FINITE. Pointer reuse/allocation are outside the model.
`pre_local` shares only NOT/AND/OR simplification: implication folding is smaller,
FF/GG are retained, and `pre_walk` leaves strong-next subtrees untouched like C.

| C source in this worktree | Lean correspondence |
| --- | --- |
| `src/lib/nnf.c:9–126` | `to_nnf`, `nnf_sat`, `nnf_exact`; weak-next polarity/finite test at lines 83–89 |
| `src/lib/rewrite.c:15–38,46–181` | Structural `DecidableEq (Formula α)`, `simplify_weak_local`, `simplify_exact`; finite weak-X-false guard at lines 101–106 |
| `src/lib/rewrite.h:36–62`; `src/lib/rewrite.c:189–245` | `Flags`, ordered `apply_local`, `apply_local_exact` |
| `src/lib/rewrite.c:248–330` | `bottom_up`, `rw_pass`, `rw_pass_exact`; atom cases bypass local rewriting |
| `src/lib/rewrite.c:10,332–359` | `RW_FIXPOINT_CAP = 200`, `rewrite_loop`, `apply_rewrites`, `apply_rewrites_exact` |
| `src/lib/rewrite.c:380–415` | `rewrite_decompose`, `conjoin`, `decompose_sat`, `decompose_exact` |
| `src/lib/normalize.c:770–860` | `pre_local`, `pre_walk`, `pre_weak`, `pre_weak_exact` on expanded constructors |
| `src/lib/normalize.c:864–899` | `pre_spine_split`, `pre_spine_split_exact` on the core; indexed-X high-level branch excluded |
| `src/lib/normalize.c:88–142,419–435` | Temporal RULES identities; `SickertRule.equivalence_finite` and `finite_rule_allowed` model the finite-admission projection |
| `src/lib/normalize.c:1006–1022` | `or_to_impl` and named response/guarded-next identities, valid in both operand orders by disjunction commutativity |
| `src/lib/normalize.c:1381–1413` | Finite mode propagated to NNF, weak and route-safe rewrites; supported passes compose by `Exact.trans` |
| `src/lib/print_ltlxba.c:214–216,242–249` | Trusted printer correspondence: NODE_X is weak X and NODE_X_STRONG uses X[!] for finite rendering |

These ports require matching C/Lean ASTs, interned AP identifiers, and structural
equality. They cover successful expanded unbounded core transformations, not
malformed/high-level ASTs, integers, bounded metadata, allocation exhaustion,
or machine-size behavior. `NODE_NEXT_N` only recurses into its body
(`src/lib/normalize.c:840–843`) and is outside `Formula`; indexed spine splitting,
arithmetic, bounded quantifiers, and expansion to nexts remain unverified.
`next_power` proves identities of the expanded mathematical sequence.

RULES/finite-guard ports do not verify scheduler phases/growth checks, CLI
plumbing, other passes, or Sickert transformations. Callers must check finite
admission before infinite-mode passes. Printing/escaping and downstream X/X[!]
interpretation (`print_ltlxba.c:242–249`) remain trusted; theorems neither execute
C nor establish emitted trust tags.

## C and Lean correspondence

Locations are relative to this repository. They identify guarded mathematical
ports, not verification of C or other CSNF template families.

| C source in this working tree | Lean port / correspondence obligation |
| --- | --- |
| `src/lib/ast_query.h:14–35,52–79`; `src/lib/cover.c:35–77` | `Formula`, `Formula.atoms`, `Boolean`, `isIn`; cover support must match the expanded formula |
| `src/lib/templates.c:72–136` | `subst`, `setLetter`, `setWord`, `sat_subst`, `subst_absent` |
| `src/lib/recognize.c` (`match_definition`); `src/lib/templates_certify.c` (`certify_definition`) | `Definition.entry`, `flip`, `Admissible.outputs`, `Admissible.boolean`; the certifier rejects every temporal theta using `ast_has_temporal` |
| `src/lib/templates.c:316–377,518–533` | `Ranked`, `Admissible.ranked`; accepted decoder dependency graph has a bounded topological rank |
| `src/lib/templates.c:422–426,496–514` | `Admissible.occurrences`, `covers`, `covers_trans`; the composition guard checks every affected section and rejects environment-side definitions |
| `src/lib/templates.c:534–560` | `Admissible.distinct`, `original`, `residual`; one chosen provider per output, defining entries dropped |
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
| `src/lib/print_ltlxba.c:214–249`; `src/lib/nnf.c:78–89` | `Sat` for `next` and `strongNext`, `next_neg_dual`, `strong_next_neg_dual` |
| `src/lib/rewrite.c:101–116`; `src/lib/normalize.c:834–838` | `issue85_weak_next`, `issue85_negation`; finite next must retain its terminal behavior |
| `src/lib/decompose.c:69–75` | `elim_realizable_inf`, `elim_realizable_fin`, `clusters_realizable` delimit the mathematical basis of exactness |

The textual `ctl o := theta` emission is `src/tools/tlsfcompose/main.c:1063`.
`normalize_definitions` establishes every reconstructed equation;
`play_decorate` supplies its Mealy implementation.

## Decomposition trusted boundary

Definition elimination, clustering, and conditional pruning are proved.
Phase B Skolem values, registers, reactions, and liveness schedulers remain
guarded C implementations without Lean controller proofs. Rewrite equivalence
does not prove their controllers. `TRUST_EXACT` means realizability equivalence
under certifier/composition guards; free reactions/registers may choose a winning
strategy without forcing a unique value on every trace.

C sets, lists, AP identifiers, AST constructors, and roles must match Lean.
Cover output sets must equal formula output atoms, including normalized/matching
formulas: recognizing an equality must recover the same constraint/support.
Expansion, preprocessing, other normalization, memory/allocation behavior, and
machine bounds remain C obligations. Cycles must yield ranks below `nelim + 1`,
providers distinct names, and section guards inspect every occurrence, including
other definitions, exactly as `covers`. Boolean guards must reject all temporal
constructors. Definition games are Mealy only; their certifier must decline Moore.

| Unproved controller family | Required runtime guard |
|---|---|
| Output-fixing non-definitions | `output_is_free` in `src/lib/templates_certify.c` (directly or through `output_constrained_elsewhere`) requires a declared output, no environment occurrence even inside the block, and no outside use, including PRESET/strict ASSERT. This covers invariant, reaction, reachability, persistence, delayed/fixed-delay, recurrence switch, server/response, arbiter, round-robin, set/reset, toggle, and guarded-next. Standalone mutex fixes/discharges nothing. |
| Round-robin/arbiter | Every mutex member and every output of every block constraint must be free outside the whole block, even without recurrence/response. Reject self-pairs `!(p && p)` before distinct-member construction. Arbiter grants are outputs, requests plain inputs; free unscheduled members can stay false. |
| Assigned values and guards | Definition/register values and both polarities of reaction, guarded-next, set/reset, toggle, and fixed-delay guards are temporal-free. Reactions reject self-reference. Combinational definitions/reactions and Skolem invariants reject Moore; registers may read current Boolean inputs for later outputs. Server requests are plain inputs; other/output/temporal requests stay residual. |
| Invariants and implicit inputs | Decline unflagged atoms. Cover support, residual interfaces, monitor eligibility, and timing adaptation treat them as environment inputs; the bounded Boolean solver must not assign omitted inputs false, even in input-only bodies. |
| Phase B ownership | Support closes transitively under committed definition theta (`src/lib/templates.c:442–472,576–623`), including newly exposed dependencies; rejected blocks stay residual. `phase_b_probe` injects solved blocks to bypass local free-output guards, checking direct and reversed-order transitive dependencies. This is not a Lean proof. |
| Finite registers/schedulers | `src/lib/templates_certify.c` rejects weak/strong next for delayed definitions, set/reset, toggle, fixed-delay, and guarded-next. Final weak next is true and strong next false independently of output; transition registers cannot discharge equivalence boundaries. Even vacuous weak-next implications are conservatively declined. Round-robin/arbiter/recurrence-switch also decline: infinite schedules cannot discharge final GF/F requests; two final grants may violate mutex. Free F/FG outputs and plain-input single-grant servers can stay true on all nonempty prefixes; Boolean invariants/reactions have no temporal boundary. |

Before cover construction, `tlsf_pipeline_build_cover` (`src/lib/pipeline.c`)
calls `spec_adapt_target` once after expansion. The pipeline, decomposition API,
tlsfresidual, tlsfcompose, tlsftemplates, and tlsfbenchgraph share it;
`conversion_prepare`/tlsf2ltl share validation. Differing finite SEMANTICS/TARGET,
including overrides, are refused explicitly; no finite adaptation is proved.
Infinite adaptation, including implicit inputs, remains trusted. Drivers use
effective TARGET: Moore bypasses input-first OxiDD; finite and Moore residuals
return UNKNOWN unless a command is explicitly selected. Moore verdict exports
use input-delay encoding; finite commands carry explicit Mealy/Moore semantics. Controller export
refuses finite/Moore contracts it does not implement.

Empty Lean sections are `tt`; absent/dropped C sections must agree, including
strict empty REQUIRE (`As W false = G As`). Successful views must retain every
constraint/role. Only the listed expanded-core simplification/NNF/rewrites have
exactness theorems; bounded expansion and high-level lowering remain trusted.
Lean retains the full signal type; C's unused-output filtering must preserve
the game/formula under projection and arbitrary extension. Only decoder
reconstruction may then assign eliminated outputs. Locality/substitution support
this interface but do not verify declaration filtering.

Union-find/keys must establish `Clustered` before pruning the initially complete
environment. Pruning needs `Prunable` and `EnvSat` for the actual dropped set.
The native search uses at most four lasso positions, eight atoms, 128 source
nodes, and 200,000 shared candidate/node/fixpoint/section updates. The last
position loops to its chosen entry; F/U/M use least and G/R/W greatest fixpoints
on reachable positions. REQUIRE holds everywhere, INITIALLY/ASSUMPTIONS at zero.
Only a completed positive joint check certifies D. Failed candidates are skipped;
unsupported syntax, exhaustion, or no witness yield UNKNOWN and retain D, so
incompleteness cannot change realizability.

`envSat_of_word` and `prune_realizable` bridge any satisfying infinite word to
conditional equivalence. C evaluation, AST/sections, and lasso interpretation
remain trusted; search completeness is unnecessary. No external automata/SAT
library is used. Finite and Moore semantics/targets never prune. Finite or
output-dependent environments must first collapse to one game, retaining
input-only system constraints. `clusters_realizable` covers infinite input-only
environments; `finite_split_fails` prevents combining arbitrary finite prefixes.

Printers/escaping/AP names must preserve the AST and weak/strong next. Compiled
controllers must realize composed letter maps, not order-sensitive simultaneous
assignments of unexpanded values. Solver/export frontends need the positive
system objective and identical ownership. In particular, a finite-game command must implement
`FinWin`: some nonempty winning prefix for every play. External solvers, ending
conventions, printing, and reported trust labels remain unverified.

## Automaton translation validation

`Impl.uncached_construction_language` proves an independent executable symbolic
reference for admitted formulas: syntax transport, pure factoring/selection,
a fixed finite basis, product progression, Zielonka construction, and max-odd
export. It models no C caches, traces, memo phases, allocation/call order, or
compiler refinement. Positive Buchi rounds require `positiveb`; general parity
formulas such as `F G a` need not admit deterministic Buchi recognizers.

`Validation/Basis.lean` fixes distinct oriented components before execution.
`compileBasis_presentation` proves the indexed Boolean/Shannon plan's language;
repeated occurrences share coordinates to avoid duplicate-colour Zielonka work.
Selection minimizes colours first; whole admitted Boolean components use proved
terminal handling. `Impl.normalize` applies `equivalent_exact` below modalities;
`normalize_language` proves infinite-word preservation, including default-only
frozen-operand absorption. `normalized_finite_construction_language` composes
normalization, admission, and export; its Buchi conclusion requires positivity.

`Validation/Finite.lean` explores BFS representatives, merging all/rejecting
fields by proved Boolean class equality while retaining tree paths and round
residual/incoming bits. It independently checks initial correspondence and every
state/letter edge, including terminal loops. Fingerprints use mixed/biased
assignments only as hints: exact equality checks candidates, failed hints trigger
full scans, and closure is checked separately. `classFingerprint_congr` and
`configurationHint_congr` preserve hints under equality; `prepareParity_exact`
and `prepareBuchi_exact` preserve keys after materialization/constant reduction.
`exportParity_language`/`exportBuchi_language` prove returned closed tables exact.
Exhaustion is a validation failure; no fixed exploration limit is proved sufficient.

| Obligation | Result / status |
| --- | --- |
| Executable transport, factoring and successful plan selection | `referencePlan_success`, `factor_success`, `canonicalPlan_spec` |
| Complete Pi2 and dual Sigma2 component languages | `pi2_language`, `sigma2_language`, `general_pi2_language` |
| Fixed component basis and Boolean product | `compileBasis_presentation`, `assemble_presentation`, `Assembly.colours_exact`, `product_language` |
| Executable Zielonka construction and parity language | `buildTree`, `tree_maxOdd`, `Assembly.parity_language` |
| Positive Buchi round monitor | `positiveb_exact`, `completedRounds_language`, `Assembly.buchi_language` |
| Boolean simplification under modalities | `normalize_language` |
| Checked finite reference export | `exportParity_language`, `exportBuchi_language`, `normalized_finite_construction_language` |
| Language equality for arbitrary finite state counts | `Validation.check_language`, `Validation.checkBuchi_sound` |
| Checked alphabet compaction | `checkCompact_sound`, `checkBuchiCompact_sound` |
| Parsed C table recognizes the requested formula after successful validation | `validate_parity_sound`, `validate_buchi_sound`; `Buchi.toParity_language` covers nonpositive round skeletons |

The equivalence checker seeks reachable closed walks with conflicting recurrent
maximum parities, without state isomorphism. SCC traversal proposes ranks;
`rankClosedCheck_sound` proves closure/nondecreasing ranks, giving a reflexive,
transitive edge-containing order independently of SCC correctness. Marks/search
are per vertex, avoiding pairs of valuation-labelled edges.
`VertexIndex.index_exact` certifies the shared index across priority thresholds;
priorities are collected separately. Alphabet compaction checks identical
transitions/priorities at every state of both tables, then lifts proved
`check`/`checkBuchi` equality to the original alphabet.

Class equality flattens Boolean roots, deduplicates, cancels complements, and
propagates constants (`mergeConj_eval`, `mergeDisj_eval`), leaving frozen operands
verbatim. Mixed/single-atom/single-complement samples reject early;
`sampleAgreement_of_eq` preserves equals. `associationAgreement_sound` covers
root reassociation, commutation, and repeats; Shannon comparison decides the rest.
Simplified cofactors preserve classes/support (`reduceProp_class`,
`cofactor_unused`, `uses_exact`). Protection tests distinct modal atoms and
syntactic containment before support; `protectionSet_exact` builds its finite
set once per elision. Cheap tree/round keys precede Boolean comparisons; syntax
equality avoids atom-list construction. `productStep_exact` preserves targets/
colours when materializing edges once. AP valuations are decoded/materialized
once with pointwise preservation in both language proofs; `freeze_exact` and
`freezeBuchi_exact` preserve materialized transition tables.

### Protocol and trusted boundary

`test/unit/dpa_dump.c` accepts `TV1`: acceptance kind, admission mode, AP order,
and prefix formula. BFS discovery uses increasing valuations (AP i is bit i),
with sorted complete rows, max-odd priorities, and source-state Buchi acceptance.
Offline caps are 10,000 states, 256 MiB host storage, 2²² BDD nodes, and 2¹⁸
cache entries, separate from production budgets. A 5 GiB process scope uses
`MemoryHigh=4G`, `MemoryMax=5G`, `MemorySwapMax=0`, letting deadlines stop
allocation-heavy cases before OOM kills the writer.

`dpaValidate REQUEST DUMP` independently parses both, rejects AP/formula/mode
mismatches, duplicate APs, missing/unordered edges, invalid targets/acceptance,
and trailing data, then builds the same-formula/AP reference and checks language
equality. Positive skeletons use Buchi rounds; otherwise `Buchi.toParity_language`
embeds C Buchi exactly for comparison with the proved parity reference. This
does not assume nonpositive round soundness. Parse/construction/export/comparison
errors fail.

The kernel checks construction, export, and checker proofs; offline execution
also trusts the Lean compiler/runtime. Decoding, serialization, hashes, C memory
safety, and BDDs remain trusted. Successful checks cover only enumerated formulas,
modes, AP orders, and acceptance kinds, bound by canonical CI hashes. Other
runtime formulas rely on the reference plus sample evidence, not a C correctness
proof. Bounded lasso goldens alone do not prove unbounded language equality.

### Regeneration and recorded results

`tools/golden/translation_validate.py` requires Lean 4.35.0 and runs offline.
Its inventory includes every monitor constructor reached by 217 corpus specs
under both policies (also failed reductions), DPA equivalence/language-golden
formulas, pinned infinite-word verdicts, stored historical monitor formulas,
and review-k/l/i cases. Each formula/AP order/admission/acceptance request shares
a hard 17-second C-dump/Lean-check deadline (the default). Admitted outcomes are
pass/fail/timeout; C declines are separate `not_admitted`. Parse/AP errors,
reference rejection, export failures, and language mismatches fail. Timeouts are
recorded without minimization or failing the run. Only passing checks get hashes;
all real failures are retained/minimized and prevent general admission. Enablement
requires zero failures among completed cases.

```sh
mkdir -p build-sprint/tmp
export TMPDIR="$PWD/build-sprint/tmp" LEAN_NUM_THREADS=1
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_STACK_SIZE_KB=2048 LEAN_MAIN_USE_THREAD=0 CARGO_BUILD_JOBS=1
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  meson setup build-sprint/release -Dbuildtype=release -Dresearch_tools=true
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  meson compile -C build-sprint/release -j1 dpa_dump tv_inventory
systemd-run --user --scope -q -p MemoryHigh=4G -p MemoryMax=5G -p MemorySwapMax=0 \
  python3 tools/golden/translation_validate.py --build build-sprint/release
```

Transient validator files/TMPDIR/dumps stay in `build-sprint/`; only hashes, verdicts,
counts, failures, and provenance go to `test/fixtures/golden/translation/`.
The C-only CI gate recomputes identical dumps. Total golden budget is 4,400,000
bytes (4.4 MB). Runs always execute fresh C/Lean checks, retaining scratch
progress if interrupted. `--set` never publishes fixtures; full audits use the
unfiltered command without inventory reuse.

The [recorded report](../test/fixtures/golden/translation/report.json) covers
1,212 formula/AP orders and 4,848 requests: 4,134 pass, zero failures, 36 timeouts,
and 678 C declines outside validation outcomes. Sets overlap; table entries are
pass / fail / timeout, with declines separate in the report.

| Set | Default parity | Default Buchi | General parity | General Buchi |
| --- | ---: | ---: | ---: | ---: |
| Corpus (258) | 248 / 0 / 0 | 242 / 0 / 0 | 256 / 0 / 0 | 249 / 0 / 0 |
| Equivalence (108) | 90 / 0 / 1 | 51 / 0 / 0 | 104 / 0 / 1 | 59 / 0 / 0 |
| Golden (945) | 760 / 0 / 5 | 690 / 0 / 0 | 912 / 0 / 28 | 760 / 0 / 3 |
| Review (14) | 12 / 0 / 0 | 9 / 0 / 0 | 10 / 0 / 0 | 6 / 0 / 0 |

GR(1) tries general admission after default unsupported decline because the
predicates are not nested; standalone DPA defaults stay unchanged. Corpus
coverage rose from 148 to 155/217, unsupported fell from 54 to 47, and invalid
inputs stayed 15. Twelve exact/strict goldens and nine decomposition verdicts
retain independently confirmed archive hashes; only `normalization_sickert2.tlsf`
stays declined among fourteen archived native cases. No successful reference
artifact was regenerated. See [golden provenance](../test/fixtures/golden/README.md)
for recorded suite results.

The [fixed-rejection inventory](../tools/golden/translation-fixed-rejections.json)
retains `!(G F (b & X false))` under both admissions and
`true U (b -> (b xor G a))` under default admission. Original/minimized forms pass
with the proved Buchi-to-parity comparison. Both minimized formulas and complements
are permanent cases; protocol tests still reject a wrong acceptance table.

### Formula-DAG decoding and signed objectives (#103)

`TlsfProofs/Dpa/FormulaDag.lean` models the public record decoder independently
of automaton construction. `Node.valid` uses the public `TlsfAstKind` numbers:
0/1/2 are true/false/AP, 3/8/10/11 are NOT/X/F/G, and 4–7/12–15 are
AND/OR/IMPL/EQUIV/U/R/W/M. Kind 9 (strong next), negative/unknown enum values,
and high-level or quantified syntax are rejected. Exact arity is mandatory:
each used child is strictly smaller than its record index, each unused child
is `UINT32_MAX`, AP records have an in-range AP index, and every other record's
AP field is `UINT32_MAX`. The checks cover all records, including unreachable
ones. Sharing children, including two equal children, is allowed.

`Accepted` includes bounded uint32 records/counts, an in-range root, and
distinct usable names in the complete input-then-output array. Names are
abstract: the C correspondence instantiates them with byte strings up to the
first NUL, with usable meaning non-null and nonempty. It assumes valid readable
storage and a non-null output pointer. The corresponding C envelope also
rejects null nodes, zero nodes, missing nonempty input/output arrays, overflow
of the summed declaration counts, and acceptance kinds other than parity/Büchi.
`test/api/dpa_dag.c` regresses these rejections and every relied-on record/name
check, including unreachable invalid records and unused invalid declarations.
The mathematical acceptance predicate describes structural admission only;
it does not predict successful allocation, depth admission, supported monitor
grammar, cancellation, deadlines, or completion. C may decline structurally
valid inputs for those reasons. The public API still copies retained data.

`denoteNode` interprets the DAG directly on infinite words. `decodeNode_meaning`
proves its equality with formula satisfaction by strong induction on node
indices, at every word position. `decode_root_meaning` selects the supplied
root without requiring it to be last; `decode_indexed_meaning` connects the
validator's finite AP indices. `ordered_ap`, `input_order`, and `output_order`
retain the exact declaration map, including unused declarations. Totalizing
defaults for malformed indices do not relax `Node.valid`. No unique-parent or
tree-unfolding-size assumption is used. The main results are included in
`tools/golden/dag_decode_audit.lean`; validator results are audited in
`tools/golden/dpa_impl_audit.lean`. They use only the permitted core axioms.

The offline protocol adds this request form (whitespace separates tokens):

```text
TVD1 parity|buchi default|general input-count output-count names...
positive|negative objective <prefix whole effective-Mealy phi>
normalization caller-trusted
dag node-count root
<numeric kind left right ap, repeated node-count times>
```

Unlike the C API's arbitrary nonempty byte strings, this protocol supports
nonempty UTF-8 AP names without whitespace and at most 16 APs/4096 records.
The dump repeats the entire header, including the AP partition/order, signed
objective and every DAG record, then uses the existing complete sorted state
table. A changed root, unused record, acceptance kind, partition, AP order,
objective or polarity is rejected. `Request.source` computes normalized psi
from the DAG, so a separately supplied formula cannot override it.

`validate_dag_parity_sound` and `validate_dag_buchi_sound` establish that a
successfully checked decoded automaton recognizes the direct DAG denotation
for every infinite word. `validate_signed_parity_sound` and
`validate_signed_buchi_sound` separately require `NormalizationPremise`:
psi is equivalent to the signed **whole** objective (positive phi or negative
NOT phi). This premise is explicitly trusted from the caller. Neither the
validator nor its receipt proves the caller's normalization or extraction of
the whole effective-Mealy objective. The external normalizer is outside this
repository. A receipt against psi alone never certifies the original objective.

Only a successful full C expansion is serialized. Every enumerated letter
must match exactly one edge, every target must be valid, and rows must remain
closed and complete. The Lean reader independently rejects missing, duplicate,
unsorted, partial or out-of-range rows. Parity uses **max-odd**; Büchi uses
uniform source-state priorities 0/1 with recurring 1 accepting. Unsupported
inputs, resource declines, cancellations, deadlines and incomplete attempts
produce no validated hash. C regressions cover sticky declines and ownership;
protocol checks cover binding, malformed records, incomplete tables and wrong
languages. Historical TV1 successful dumps are unchanged.

Run a fresh serial check from the repository root after committing the input
and validator sources:

```sh
python3 tools/golden/translation_validate.py --build build-sprint/release --dag
```

The dedicated [DAG receipt](../test/fixtures/golden/translation/dag/provenance.json)
binds the source revision and SHA-256 inputs, C dumper and Lean validator
executables, build configuration, exact requests, successful dump hashes and
all outcomes. Fixtures cover sharing, a nonfinal root, reordered and unused
case-sensitive AP declarations, both whole-objective polarities, both admission
policies, and parity/Büchi (including unsupported Büchi outcomes). The ordinary
whole objective in these fixtures keeps all section defaults and varies its
guarantee. The normalization premise is recorded separately from the checked
language claim. These are fresh per-instance, unbounded-language checks; they
do **not** establish universal C implementation refinement, memory safety, BDD
refinement, compiler correctness, or correctness of unvalidated runtime inputs.

### Source map

These locations identify semantic algorithms and C operations covered by dump
validation. BDD allocation/failure handling/decoding remain outside language
theorems; no cache, trace, store-order, or compiler refinement is asserted.

| Source | Relevant definitions / boundary |
| --- | --- |
| `TlsfProofs/Dpa/Classes.lean:489` | `def HasTag (tag : Formula (Fin ap) → Prop) (x : Class ap) : Prop` |
| `TlsfProofs/Dpa/Classes.lean:503` | `def subformulas : Formula α → List (Formula α)` |
| `TlsfProofs/Dpa/Classes.lean:520` | `def Protected (x : Class ap) (t : Formula (Fin ap)) : Prop` |
| `TlsfProofs/Dpa/Classes.lean:578` | `noncomputable def reduce (x : Class ap) : Class ap` |
| `TlsfProofs/Dpa/Classes.lean:596` | `noncomputable def rho (x : Class ap) : Class ap` |
| `TlsfProofs/Dpa/Converse.lean:35` | `inductive Pi2 : Formula α → Prop where` |
| `TlsfProofs/Dpa/GeneralConverse.lean:862` | `theorem general_pi2_language (x : Class ap) (hx : NNFClass x) (hpi : HasTag Pi2 x)` |
| `src/lib/dpa.c:294` | `c->max_priority = (c->components.n + 2) \| 1u;` |
| `src/lib/dpa.c:339` | `uint32_t round = dpa_pair(c, c->acceptance, c->acceptance != 0);` |
| `src/lib/dpa.c:715` | `if (!c->started) {` |
| `src/lib/dpa.c:743` | `s->edges[0] = (TlsfDpaEdge){label, id, c->max_priority - !s->leaf};` |
| `src/lib/dpa_dela.c:5` | `static uint32_t transition(TlsfDpa *c, uint32_t a, uint32_t r) {` |
| `src/lib/dpa_dela.c:72` | `uint32_t dpa_pair(TlsfDpa *c, uint32_t a, uint32_t r) {` |
| `src/lib/dpa_dela.c:91` | `static uint32_t component(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_dela.c:100` | `if (!c->buchi) {` |
| `src/lib/dpa_dela.c:126` | `uint32_t dpa_acceptance(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_dela.c:178` | `static uint32_t terminal_condition(TlsfDpa *c, uint32_t f,` |
| `src/lib/dpa_dela.c:212` | `static uint32_t seen_colours(TlsfDpa *c, uint32_t f, const uint64_t *colours) {` |
| `src/lib/dpa_dela.c:231` | `static uint32_t joint(TlsfDpa *c, uint32_t tuple, uint32_t leaf, DpaJointScratch **scratch) {` |
| `src/lib/dpa_dela.c:277` | `result = dpa_dag(c, 2, 0, target, c->max_priority - !truth);` |
| `src/lib/dpa_dela.c:290` | `if (c->buchi) {` |
| `src/lib/dpa_dela.c:296` | `priority = round->rejecting;` |
| `src/lib/dpa_dela.c:324` | `uint32_t dpa_dela_step(TlsfDpa *c, uint32_t tuple, uint32_t leaf) {` |
| `src/lib/dpa_dela.c:345` | `uint32_t dpa_dela_initial(TlsfDpa *c) {` |
| `src/lib/dpa_formula.c:3` | `uint32_t dpa_class(TlsfDpa *c, Bdd owned) {` |
| `src/lib/dpa_formula.c:46` | `uint32_t dpa_boolean(TlsfDpa *c, bool conjunction, uint32_t a, uint32_t b) {` |
| `src/lib/dpa_formula.c:53` | `uint32_t dpa_ite(TlsfDpa *c, uint32_t v, uint32_t hi, uint32_t lo) {` |
| `src/lib/dpa_formula.c:60` | `bool dpa_children(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:77` | `static unsigned tags_impl(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:116` | `unsigned dpa_tags(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:125` | `static void tag_bounds(TlsfDpa *c, uint32_t f, unsigned *lo, unsigned *hi) {` |
| `src/lib/dpa_formula.c:155` | `bool dpa_has_tags(TlsfDpa *c, uint32_t f, unsigned mask) {` |
| `src/lib/dpa_formula.c:187` | `bool dpa_admitted(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:205` | `uint32_t dpa_atom(TlsfDpa *c, TlsfAstKind op, uint32_t a, uint32_t b) {` |
| `src/lib/dpa_formula.c:251` | `static uint32_t term(TlsfDpa *c, TlsfAstKind op, uint32_t a, uint32_t b) {` |
| `src/lib/dpa_formula.c:362` | `static uint32_t materialize(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:385` | `static uint32_t wrap_next(TlsfDpa *c, uint32_t f, unsigned next) {` |
| `src/lib/dpa_formula.c:391` | `static uint32_t formula_impl(TlsfDpa *c, const TlsfAstNode *n, bool neg,` |
| `src/lib/dpa_formula.c:501` | `static bool check_admission(TlsfDpa *c, uint32_t f, uint64_t epoch) {` |
| `src/lib/dpa_formula.c:520` | `static uint32_t factor_term(TlsfDpa *c, uint32_t id) {` |
| `src/lib/dpa_formula.c:549` | `static bool groupable(TlsfDpa *c, uint32_t id, uint64_t epoch) {` |
| `src/lib/dpa_formula.c:560` | `static void group_operands(TlsfDpa *c, uint32_t id, TlsfAstKind op,` |
| `src/lib/dpa_formula.c:580` | `static uint32_t syntax_acceptance(TlsfDpa *c, uint32_t id) {` |
| `src/lib/dpa_formula.c:594` | `if (cosafety != (uint32_t)conjunction)` |
| `src/lib/dpa_formula.c:608` | `uint32_t dpa_grouped_acceptance(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:615` | `return grouped ? syntax_acceptance(c, id) : dpa_acceptance(c, f);` |
| `src/lib/dpa_formula.c:620` | `static uint32_t buchi_syntax(TlsfDpa *c, uint32_t id) {` |
| `src/lib/dpa_formula.c:652` | `static uint32_t map_impl(TlsfDpa *c, uint32_t f, unsigned mode, uint64_t epoch,` |
| `src/lib/dpa_formula.c:698` | `static uint32_t unfold_atom_care(TlsfDpa *c, DpaAtom *atom, uint32_t cube,` |
| `src/lib/dpa_formula.c:759` | `static uint32_t unfold_class_care(TlsfDpa *c, uint32_t f, uint32_t cube,` |
| `src/lib/dpa_formula.c:814` | `uint32_t dpa_unfold(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:872` | `uint32_t dpa_step_dag(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:887` | `static void protected_term(TlsfDpa *c, uint32_t id, bool *protect,` |
| `src/lib/dpa_formula.c:910` | `static void protected_x(TlsfDpa *c, uint32_t f, bool *protect, uint64_t epoch) {` |
| `src/lib/dpa_formula.c:934` | `uint32_t dpa_remainder(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:967` | `uint32_t dpa_dual(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_zielonka.c:27` | `static void model(TlsfDpa *c, uint32_t f, uint64_t *set) {` |
| `src/lib/dpa_zielonka.c:39` | `static uint32_t outside(TlsfDpa *c, const uint64_t *set,` |
| `src/lib/dpa_zielonka.c:48` | `static bool before(TlsfDpa *c, const uint64_t *a, const uint64_t *b) {` |
| `src/lib/dpa_zielonka.c:66` | `static uint32_t tree(TlsfDpa *c, const uint64_t *set) {` |
| `src/lib/dpa_zielonka.c:154` | `static uint32_t path(TlsfDpa *c, uint32_t node, uint32_t parent, uint32_t pos) {` |
| `src/lib/dpa_zielonka.c:177` | `static uint32_t leftmost(TlsfDpa *c, uint32_t id) {` |
| `src/lib/dpa_zielonka.c:187` | `void dpa_tree_init(TlsfDpa *c) {` |
| `src/lib/dpa_zielonka.c:198` | `uint32_t dpa_tree_step(TlsfDpa *c, uint32_t *leaf, const uint64_t *colours) {` |
| `src/lib/dpa_zielonka.c:231` | `return c->max_priority - priority;` |

Offline verification now uses `tools/golden/regenerate.py --build
build-sprint/release --translation` to replay the frozen passing receipts
without changing dates, hashes or claims. Membership expectations are independently
rederived by direct word semantics. General realizability and historical exact
normalization equivalence stay frozen where native checks cannot renew them;
see [the golden guide](../test/fixtures/golden/README.md).
