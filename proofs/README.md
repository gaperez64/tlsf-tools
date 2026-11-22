# TLSF decomposition and automaton proofs

Lean 4.35.0, using only core (`import Init`). These are mathematical ports and
per-instance automaton checks. They do not verify the C binary, memory safety,
BDD implementation, compiler, TLSF-to-game reduction or unlisted controllers.
C ASTs, signal ownership, section assembly, guards and printers must match the
models. Unvalidated runtime formulas have no per-instance language proof.

## Build

Run from `proofs/`, one compiler at a time. CI does not build the proofs.
Audits permit only `propext`, `Classical.choice`, and `Quot.sound`.

```bash
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=2048 LEAN_MAIN_USE_THREAD=0
lake build
timeout 300 lake env lean ../tools/golden/gr1_region_audit.lean || exit $?
timeout 300 lake env lean ../tools/golden/restriction_audit.lean || exit $?
```

## Decomposition model and guarantees

Names are in `Tlsf`; counterexamples are in `Tlsf.Examples`.

| Module | Scope |
|---|---|
| `LTL.lean` | Finite/infinite satisfaction, weak/strong next, locality and substitution. |
| `Game.lean` | Input-first Mealy strategies, replay and products; finite wins use a nonempty prefix per play. |
| `Objective.lean` | Ordinary and strict six-section objectives. |
| `Restriction.lean` | One-sided causal Boolean restrictions on infinite Mealy games. |
| `Passes.lean`, `Definition.lean` | Ranked substitution and definition elimination. |
| `Cluster.lean`, `Pruning.lean` | Infinite clustering and conditional assumption pruning. |
| `Examples.lean` | Guard and finite-split counterexamples. |
| `Rewrites.lean` | NNF, local rewrites and spine decomposition. |
| `SetDedup.lean` | Structural/core equality and formula-set deduplication. |
| `IntegerLiteral.lean`, `CheckedArithmetic.lean` | Signed-64 decoding, checked evaluation and range reductions. |
| `NextStrength.lean` | Indexed-next guards, strength and reconstruction. |

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

## One-sided restrictions

Names are in `Tlsf.Restriction`. Apply substitutions to the whole positive,
effective Mealy objective under the original ownership map. Solver verdicts
and any player/timing transformation must establish that same frame. Controller
export must reconstruct the simultaneous causal decoder.

| Obligation | Theorem or definition |
| --- | --- |
| Exact simultaneous Boolean substitution | `substAll`, `decode`, `mapWord`, `substAll_sat` |
| Decoder changes only inputs, using only current inputs | `InputDecoder`, `input_decoder`, `OwnershipPreserving` |
| Explicit system simulation on decoded input/history | `restrictSystem`, `replay_decode_history`, `play_input_decoder` |
| Original realizability implies input-restricted realizability; contraposition gives UNREAL only | `realizable_input_restriction`, `unrealizable_input_restriction` |
| Output-restricted realizability implies original realizability, via `decorate` | `realizable_output_restriction`, `play_decorate` |
| Every input in S is replaced by r in S, with input ownership | `identify`, `identify_boolean`, `identify_ownership`, `input_identification_decoder` |
| Every selected output is set to its Boolean constant | `constants`, `constants_boolean`, `constants_ownership`, `constant_output_decoder` |
| Input constants and output representatives of the same ownership | `constant_input_decoder`, `output_identification_decoder` |
| Complete ordinary/strict effective objective | `substAll_objective_sat`, `objective_input_restriction`, `objective_output_restriction` |
| Opposite verdict polarities fail | `input_identification_polarity`, `output_constant_polarity` |

## Rewrite exactness

Names are in `Tlsf.Rewrites`. `Exact fin f g` requires equal satisfaction at
every in-range position: finite and infinite words when `fin`, infinite otherwise.
High-level expansion and infinite-word Sickert soundness remain unproved.

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
| High-level pre-indexed-X reduction | `NextStrength.preIndexedX_lower`, `preIndexedX_sat`; zero, homogeneous merges, mixed-chain refusal, representability and reconstruction are covered by NextStrength |
| Reject all three finite-disabled metadata rows | `sickert_rules_refused`, `sickert_limit_lift_refused`, `sickert_gf_w_refused`, `sickert_fg_u_refused` show the finite guard returns false |
| Counterexample to the unrestricted context equation | `sickert_finite_counterexample`: on one letter with p=true, `C[GF p]` is false and `(GF p && C[true]) || C[false]` is true for `C[z] = G(!z)` |

| C source in this worktree | Lean correspondence |
| --- | --- |
| `src/lib/nnf.c:9–126` | `to_nnf`, `nnf_sat`, `nnf_exact`; weak-next polarity/finite test at lines 83-89 |
| `src/lib/formula_equal.h:12–50`; `src/lib/rewrite.c:22–157` | Structural `DecidableEq (Formula α)`, `simplify_weak_local`, `simplify_exact`; finite weak-X-false guard at lines 77-82 |
| `src/lib/rewrite.h:36–62`; `src/lib/rewrite.c:165–221` | `Flags`, ordered `apply_local`, `apply_local_exact` |
| `src/lib/rewrite.c:224–306` | `bottom_up`, `rw_pass`, `rw_pass_exact`; atom cases bypass local rewriting |
| `src/lib/rewrite.c:11,308–335` | `RW_FIXPOINT_CAP = 200`, `rewrite_loop`, `apply_rewrites`, `apply_rewrites_exact` |
| `src/lib/rewrite.c:356–391` | `rewrite_decompose`, `conjoin`, `decompose_sat`, `decompose_exact` |
| `src/lib/normalize.c:761–854` | `pre_local`, `pre_walk`, `pre_weak`, `pre_weak_exact` on expanded constructors; local indexed reconstruction is covered by NextStrength |
| `src/lib/normalize.c:628–701` | `NextStrength.indexed`, `weakUnary`, `preIndexedX`; `preIndexedX_lower` and branch equivalences |
| `src/lib/normalize.c:860–892` | `pre_spine_split`, `pre_spine_split_exact` on the core; local indexed distribution is covered by NextStrength |
| `src/lib/normalize.c:84–138,390–406` | Temporal RULES identities; `SickertRule.equivalence_finite` and `finite_rule_allowed` model the finite-admission projection |
| `src/lib/normalize.c:1008–1017` | `or_to_impl` and named response/guarded-next identities, valid in both operand orders by disjunction commutativity |
| `src/lib/normalize.c:1376–1402` | Finite mode propagated to NNF, weak and route-safe rewrites; supported passes compose by `Exact.trans` |
| `src/lib/print_ltlxba.c:214–216,242–249` | Trusted printer correspondence: NODE_X is weak X and NODE_X_STRONG uses X[!] for finite rendering |

## Set deduplication

Names are in `Tlsf.SetDedup`. Lowering uses a fixed environment; correctness of
C evaluators, capture avoidance and expansion remains trusted.

| Claim | Theorem |
| --- | --- |
| Structural equality implies identical syntax and denotation | `structEq_eq`, `nodesEq_eq`, `structEq_denotation` |
| Equal captures permit substitution | `structEq_substitution` |
| Duplicate formula folds preserve meaning | `dedup_conj`, `dedup_disj` |
| Desugared core equality permits deduplication | `coreEq_denotation`, `dedup_core_conj`, `dedup_core_disj` |
| Weak/strong next differ on one-letter words | `issue108_not_structEq`, `issue108_terminal`, `issue108_denotations_differ` |
| Indexed-next sugar has the same core | `issue110_next_sugar` |

## Integer literals and range domains

Names are in `Tlsf.IntegerLiteral`. The model covers successful materialization;
resource limits may reject additional inputs.

| C source | Lean correspondence / executable enforcement |
| --- | --- |
| `src/lib/tlsf.l` (`INT`, integer action) | `Digits`, `decimal`, `lex`; `integer_literal_116` calls the generated lexer, including stale `errno`, the unsigned-64 overflow boundary and long leading-zero spellings |
| `src/lib/tlsf.y` (`TOK_INTEGER`, unary `TOK_MINUS`, `TOK_MIN_MAGNITUDE`, parentheses) | `Syntax`, `parse`, `parse_exact`, explicit minimum/rejection lemmas; C unit inspects actual parsed node kinds and children |
| `src/lib/expand.c` (`eval_int`, `NODE_INT`/`NODE_INT_NEG`) | `checked`, `eval`, `decode_exact`; unit checks payloads and negation overflow |
| `src/lib/expand.c` (`eval_domain`) | `endpoints`, `values`, `domainValues`, membership/safety lemmas; unit compares every enumerated member of tiny extreme, middle, singleton and inverted domains under all four strictness combinations |
| `test/cli/check_integer_literal.py` | Issue reproducer and adjacent singleton ranges, direct/zero-prefixed/comment-separated/arithmetic minimum spellings, reprinting and pre-bounded normalization, rejection diagnostics and empty stdout, under both word kinds |

## Checked arithmetic and reductions

Names are in `Tlsf.CheckedArithmetic`. Division/remainder truncate toward zero;
zero divisors and MIN / -1 or MIN % -1 reject. Every reduction prefix must fit
signed-64, including prefixes later cancelled or multiplied by zero.

| C source / executable check | Lean correspondence |
| --- | --- |
| `src/lib/expand.c` (`eval_int`, negation and binary operator switch) | `operation`, `Allowed`, `apply_iff`, `eval_iff`, `eval_exact`, `eval_rejects` |
| `src/lib/expand.c` (`eval_domain`) | `evalDomain`, `eval_domain_exact`, `domain_rejects_endpoint`; reuses #116 endpoint/list safety |
| `src/lib/expand.c` (`bind_reduction_body`, `eval_int_reduction`) | `bind`, `evalFold`, `FoldDefined`, `evalFold_iff`, `eval_range_reduction`, `sum_exact`, `product_exact` |
| `src/lib/expand.c` (`expand_quantifier`, `eval_set_reduction`) | `formulaReduce`, `setReduce`, the four Boolean/set fold exactness results and `six_empty_cases` |
| `test/unit/checked_arithmetic.c` (`checked_arithmetic_115`) | Calls the actual private evaluator: wide-integer operator oracle, binding shadowing, reduction prefixes/empty seeds/nesting, computed-domain membership under every strictness flag, and failed-domain/formula publication. `boundary_witnesses` and `issue115_rejected` are kernel-computed matching examples. |
| `test/cli/check_checked_arithmetic.py` (`checked_arithmetic_cli_115`) | All three original small-final-endpoint reproducers, division/remainder overflow and zero, sum/product prefix overflow, all six reductions over computed/reversed/extreme bounds, all strictness flags, both word kinds and the input-assumption/output-guarantee objective orientation. Failures require diagnostics and empty stdout. |

## Indexed-next strength

Names are in `Tlsf.NextStrength`. `preIndexedX_lower` and `preIndexedX_sat`
cover the pass under `LiteralCounts`; symbolic count evaluation and C expansion
remain trusted.

| Actual C branch | Guarantee |
| --- | --- |
| Indexed count zero, either strength | `indexed_zero`, `indexed_zero_sat`: return the rewritten body |
| Weak indexed next over unary weak X | `indexed_unary_merge`, `indexed_unary_sat`: exact `c+1`, guarded by `0 <= c < INT64_MAX` (zero returns earlier) |
| Indexed over indexed, matching strengths | `indexed_indexed_merge`, `indexed_indexed_sat`: exact `c+d`, including zero inner count and either homogeneous strength, under C's nonnegative/sum guard; outer zero takes the earlier branch |
| Unary weak X over weak indexed next | `unary_indexed_merge`, `unary_indexed_sat`: exact `d+1` under C's increment guard |
| Positive mixed indexed strengths, or indexed over strong unary X | `indexed_mixed`, `indexed_strongUnary`: retain both constructors; `weakUnary_strongIndexed` retains weak over strong indexed next |
| Changed child without a merge, including strong outer nodes | `indexed_rebuild_sat`, `strongUnary_rebuild_sat`; whole-pass `preIndexedX_lower` supplies the child equality at every recursion depth |
| Count representability | `increment_fits`, `addition_fits`: each admitted result fits signed-64 and conversion to Nat preserves the exact sum; `increment_guard_exact`, `addition_guard_exact` characterize representability and prove the guard's subtraction safe; failed guards reconstruct without arithmetic |

### Indexed pre-weak and spine steps

| Claim | Theorem |
| --- | --- |
| Rebuild indexed next with an equivalent body | `indexedNext_congr`, `preWeak_indexed_rebuild` |
| Distribute indexed next over conjunction, including count zero and terminal positions | `indexedNext_conj`, `preSpine_indexed_split` |

These are local steps, not whole-pass proofs of high-level C pre-weak/spine
traversals or normalization's conservative `node_eq` comparator.

## GR(1) region certificates

`Tlsf.Gr1.region_conditions_sound` proves a winning causal Mealy strategy
from `RegionConditions` on a finite deterministic acceptance-sampled arena.
`strategy_invariant` preserves W. See the [certificate format](../docs/gr1-region-method.md).

| Model / condition | C source |
| --- | --- |
| State-only W/X/Y, enforced by `RegionCertificate` argument types | `src/lib/gr1_check.c:2330–2331,2339–2357` |
| `goal_eq`: certificate goal equals actual goal on every state | `src/lib/gr1_check.c:3322–3334` |
| `y_union`: Y equals the union of its X lanes on every state | `src/lib/gr1_check.c:2349–2351,2363–2378` |
| `y_mono`: adjacent Y levels are monotone | `src/lib/gr1_check.c:2335,2379–2401` |
| `reset_mem`: concrete reset belongs to W | `src/lib/gr1_check.c:2408–2424,3336–3343` |
| `coverage`: X levels cover W for every goal | `src/lib/gr1_check.c:3344–3368` |
| `goal_total`: one safe, W-preserving control for each input at a goal | `src/lib/gr1_check.c:3135–3148,3194–3196,3228–3234` |
| `rank_total`: one joint safe/progress control in the least lexicographic layer | `src/lib/gr1_check.c:3135–3148,3236–3274` |

`Progress` uses successor justice, lower Y, or the selected X with successor
fairness false. No fairness means a synthetic true lane, disabling stuttering.
`alternating_wins`, `sampled_wins`, and `ranked_wins` check example certificates.

## C and Lean correspondence

`test/cli/check_proof_references.py` checks these locations. Update them when
sources move; historical source hashes do not replace this check.

| C source in this working tree | Lean port / correspondence obligation |
| --- | --- |
| `src/lib/ast_query.h:14–35,52–79`; `src/lib/cover.c:33–68` | `Formula`, `Formula.atoms`, `Boolean`, `isIn`; cover support must match the expanded formula |
| `src/lib/expand.c:737–865` | Field census, `HNode`, `HNodes`, `structEq`, `structEq_eq`, `nodesEq_eq`; enforced by `set_dedup` and `set_dedup_field_inventory` |
| `src/lib/expand.c:867–908,998–1012` | Formula identity keys / duplicate removal: equal core implies `coreEq_denotation`, `dedup_core_conj`, `dedup_core_disj`; C lowering correspondence remains trusted |
| `src/lib/expand.c:1155–1183,1282–1342,1376–1392` | Stored-element substitution and repeated pattern captures: `structEq_eq`, `structEq_substitution`; no change to pattern equality |
| `src/lib/expand.c:1530–1578,1703–1818` | Core/indexed-next/range/ITE port: `lower`, `indexedNext`, `boundedRange`, `literalRange`; `issue108_terminal`, `issue108_denotations_differ`, `issue110_next_sugar` |
| `src/lib/normalize.c:628–701`; `src/lib/expand.c:1729–1754` | `NextStrength.preIndexedX_lower`, `preIndexedX_sat`: guarded pre-indexed-X reduction preserves exact expanded weak/strong sequences; expansion execution remains trusted |
| `src/lib/templates.c:72–136` | `subst`, `setLetter`, `setWord`, `sat_subst`, `subst_absent` |
| `src/lib/recognize.c` (`match_definition`); `src/lib/templates_certify.c` (`certify_definition`) | `Definition.entry`, `flip`, `Admissible.outputs`, `Admissible.boolean`; the certifier rejects every temporal theta using `ast_has_temporal` |
| `src/lib/templates.c:316–377,518–533` | `Ranked`, `Admissible.ranked`; accepted decoder dependency graph has a bounded topological rank |
| `src/lib/templates.c:422–426,496–514` | `Admissible.occurrences`, `covers`, `covers_trans`; the composition guard checks every affected section and rejects environment-side definitions |
| `src/lib/templates.c:534–560` | `Admissible.distinct`, `original`, `residual`; one chosen provider per output, defining entries dropped |
| `src/lib/residual.c:19–28` | `substPass`, `substPasses`; instantiate `passes = ds.length + 1` |
| `src/lib/residual_plan.c:23–39` | `residual`, `residual_objective`; optional additional rewrites require separate semantic correctness |
| `src/lib/residual_plan.c:44–53,72–115` | Freeze the first pruned/retained view across routing, solving and export; cache allocation failure disables pruning for the plan |
| `src/lib/residual.c:30–59,61–66` | `Formula.atoms`, `normalize_untouched`; support collection and unused-output declaration removal |
| `src/lib/section_pattern.c:81–114,173–225` | `sectionFormula`, `objectiveFormula`, `objective_sat`; empty sections are true, all section conjuncts are included |
| `src/lib/residual.c:100–175,177–225` | `Prunable`, `EnvSat`, `prune_realizable`; the transitive cone includes all kept roles, asserts dropped input support/disjointness, and prunes only infinite ordinary/strict Mealy games after a positive joint check |
| `src/lib/env_witness.c:20–88` | Expanded AST/section compilation for `environmentFormula`; rejects other roles and unsupported syntax |
| `src/lib/env_witness.c:90–188` | Lasso successor and least/greatest fixed points implement `Sat none`; REQUIRE holds at every reachable position, INITIALLY/ASSUMPTIONS at zero; `environment_sat_iff` in `proofs/TlsfProofs/Pruning.lean:11–27` |
| `src/lib/env_witness.c:190–229`; `src/lib/env_witness.h:6–7` | Only a completed positive witness check returns SATISFIABLE; `envSat_of_word` in `proofs/TlsfProofs/Pruning.lean:29–31` supplies `EnvSat` for `prune_realizable`; incomplete search keeps D |
| `src/lib/residual.c:243–348` | `Clustered`, `owner`, `clusters_realizable`; union-find gives disjoint output classes; the finite/output-dependent fallback keeps a single game |
| `src/lib/print_ltlxba.c:214–249`; `src/lib/nnf.c:78–89` | `Sat` for `next` and `strongNext`, `next_neg_dual`, `strong_next_neg_dual` |
| `src/lib/rewrite.c:77–92`; `src/lib/normalize.c:825–830` | `issue85_weak_next`, `issue85_negation`; finite next must retain its terminal behavior |
| `src/lib/decompose.c:66–72` | `elim_realizable_inf`, `elim_realizable_fin`, `clusters_realizable` delimit the mathematical basis of exactness |

| C source | Lean correspondence |
| --- | --- |
| `src/tools/tlsfcompose/main.c:1063` | Controller emission; `normalize_definitions`, `play_decorate`. |

## Automaton translation validation

The executable reference proves language preservation for admitted formulas;
positive Buchi rounds require `positiveb`. Successful translation validation
proves language equality for the supplied formula, mode, AP order and table.
Exhaustion or incomplete tables yield no proof. Execution additionally trusts
the Lean compiler/runtime and serialization.

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

### Formula-DAG validation

| Claim | Theorem |
| --- | --- |
| Direct DAG semantics equals decoded formula semantics | `decodeNode_meaning`, `decode_root_meaning`, `decode_indexed_meaning` |
| Checked automaton recognizes the DAG | `validate_dag_parity_sound`, `validate_dag_buchi_sound` |
| Checked automaton recognizes the signed whole objective | `validate_signed_parity_sound`, `validate_signed_buchi_sound`, requiring `NormalizationPremise` |

The caller must supply the complete effective Mealy objective and prove its
normalization to the DAG. A receipt for the DAG alone does not prove that bridge.
TVD1 records this as `normalization caller-trusted`.

From `proofs/`, build with `lake build dpaValidate`, then run
`.lake/build/bin/dpaValidate REQUEST DUMP`. The C dumper is
`build/test/unit/dpa_dump REQUEST > DUMP`, run from the repository root.

Requests use whitespace-separated tokens:

```text
TV1 parity|buchi default|general AP-count names... <prefix formula>

TVD1 parity|buchi default|general input-count output-count names...
positive|negative objective <prefix whole effective-Mealy formula>
normalization caller-trusted
dag node-count root
<numeric kind left right ap, repeated node-count times>
```

The alternatives and angle-bracketed fields above are notation. AP names are
nonempty UTF-8 without whitespace; requests allow at most 16 APs and 4096 DAG
records. See `include/tlsf/dpa.h` for record constraints. Dumps bind the request
and contain complete sorted rows; parity is max-odd, Büchi uses recurring 1.
The caller's whole-objective normalization remains trusted.

GR(1) retries general admission after an unsupported default result;
the standalone DPA API defaults remain restricted.

### Replay

From the repository root, with a research build and Lean available:

```sh
python3 tools/golden/regenerate.py --build build-sprint/release --translation
```

Replay checks frozen passing TV1/TVD1 receipts without replacing historical
hashes or claims. See the [golden guide](../test/fixtures/golden/README.md).
`translation_validate.py` creates new receipts; use it only for new evidence.

### Source map

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
| `src/lib/dpa.c:715` | `if (!c->started) {` |
| `src/lib/dpa.c:743` | `s->edges[0] = (TlsfDpaEdge){label, id, c->max_priority - !s->leaf};` |
| `src/lib/dpa_dela.c:72` | `uint32_t dpa_pair(TlsfDpa *c, uint32_t a, uint32_t r) {` |
| `src/lib/dpa_dela.c:178` | `static uint32_t terminal_condition(TlsfDpa *c, uint32_t f,` |
| `src/lib/dpa_dela.c:231` | `static uint32_t joint(TlsfDpa *c, uint32_t tuple, uint32_t leaf, DpaJointScratch **scratch) {` |
| `src/lib/dpa_dela.c:277` | `result = dpa_dag(c, 2, 0, target, c->max_priority - !truth);` |
| `src/lib/dpa_dela.c:324` | `uint32_t dpa_dela_step(TlsfDpa *c, uint32_t tuple, uint32_t leaf) {` |
| `src/lib/dpa_formula.c:46` | `uint32_t dpa_boolean(TlsfDpa *c, bool conjunction, uint32_t a, uint32_t b) {` |
| `src/lib/dpa_formula.c:53` | `uint32_t dpa_ite(TlsfDpa *c, uint32_t v, uint32_t hi, uint32_t lo) {` |
| `src/lib/dpa_formula.c:116` | `unsigned dpa_tags(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:125` | `static void tag_bounds(TlsfDpa *c, uint32_t f, unsigned *lo, unsigned *hi) {` |
| `src/lib/dpa_formula.c:155` | `bool dpa_has_tags(TlsfDpa *c, uint32_t f, unsigned mask) {` |
| `src/lib/dpa_formula.c:187` | `bool dpa_admitted(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:549` | `static bool groupable(TlsfDpa *c, uint32_t id, uint64_t epoch) {` |
| `src/lib/dpa_formula.c:560` | `static void group_operands(TlsfDpa *c, uint32_t id, TlsfAstKind op,` |
| `src/lib/dpa_formula.c:580` | `static uint32_t syntax_acceptance(TlsfDpa *c, uint32_t id) {` |
| `src/lib/dpa_formula.c:608` | `uint32_t dpa_grouped_acceptance(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:615` | `return grouped ? syntax_acceptance(c, id) : dpa_acceptance(c, f);` |
| `src/lib/dpa_formula.c:759` | `static uint32_t unfold_class_care(TlsfDpa *c, uint32_t f, uint32_t cube,` |
| `src/lib/dpa_formula.c:814` | `uint32_t dpa_unfold(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_formula.c:872` | `uint32_t dpa_step_dag(TlsfDpa *c, uint32_t f) {` |
| `src/lib/dpa_zielonka.c:27` | `static void model(TlsfDpa *c, uint32_t f, uint64_t *set) {` |
| `src/lib/dpa_zielonka.c:39` | `static uint32_t outside(TlsfDpa *c, const uint64_t *set,` |
| `src/lib/dpa_zielonka.c:48` | `static bool before(TlsfDpa *c, const uint64_t *a, const uint64_t *b) {` |
| `src/lib/dpa_zielonka.c:66` | `static uint32_t tree(TlsfDpa *c, const uint64_t *set) {` |
| `src/lib/dpa_zielonka.c:154` | `static uint32_t path(TlsfDpa *c, uint32_t node, uint32_t parent, uint32_t pos) {` |
| `src/lib/dpa_zielonka.c:177` | `static uint32_t leftmost(TlsfDpa *c, uint32_t id) {` |
| `src/lib/dpa_zielonka.c:187` | `void dpa_tree_init(TlsfDpa *c) {` |
| `src/lib/dpa_zielonka.c:198` | `uint32_t dpa_tree_step(TlsfDpa *c, uint32_t *leaf, const uint64_t *colours) {` |
| `src/lib/dpa_zielonka.c:231` | `return c->max_priority - priority;` |
