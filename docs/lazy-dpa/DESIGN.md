# State-by-state LTL → DPA in tlsf-tools

> Design for [#78](https://github.com/gaperez64/tlsf-tools/issues/78), approved after two reviews in October 2026. `T/` paths are this repository and `A/` paths are Acacia-Bonsai. Relative links such as `../PLAN.md`, `../probe/` and `review-issues/` point to that sprint's working files, which are not in this repository; the review drafts became issues #79–#87.

Build one bounded, lazy C23 construction: ground TLSF AST → Boolean Π₂/Σ₂ components → deterministic
Emerson–Lei automaton (DELA) → Zielonka tree → DPA. Add one complete Δ₂ normalizer only if the
target inventory needs it. Eager translation is BFS over that API. Rebuild its symbolic labels
in acacia's `bddx`, then reuse the existing split and solve.
No new dependency, Java runtime, Spot in libtlsf, alphabet enumeration, or second eager constructor.

This is justified by [the measured M0](../PLAN.md): 43/69 full Owl DPAs fit 120 s, median 1,883
states, with almost all states explored on most of those inputs. Measure the simpler product first;
these results do not promise it will complete the same 43. The other 26 motivate
later lazy game arms; this design does not implement their solver or claim their soundness.
The owner's decisions supersede the older route/API descriptions in
[tlsf-tools#78](https://github.com/gaperez64/tlsf-tools/issues/78) and
[acacia-bonsai#340](https://github.com/gaperez64/acacia-bonsai/issues/340).

## 1. What SemML actually constructs

Source references below are `file:line` in the inspected 2026-10-29 checkouts. Roots:
`S=/home/gperez/GIT-repos/semml/src/main/java/semml`,
`O=/home/gperez/GIT-repos/semml/src/main/java/owl`,
`T=/home/gperez/GIT-repos/acacia-bonsai/subprojects/tlsf-tools`,
`A=/home/gperez/GIT-repos/acacia-bonsai`.
In this section, basenames resolve to these files: `O/translations/ltl2dela/NormalformDELAConstruction.java`,
`O/translations/canonical/DeterministicConstructions.java`, and
`O/automaton/acceptance/transformer/ZielonkaTreeTransformations.java`.

1. **Input and preprocessing.** `S/semmlCommands/synthesisCommands/util/SemmlSynthesisRunner.java:60`
   prepares the input, calls `ltl2Dela`, `dela2Dpa`, then builds the game; its TLSF branch is at :93.
   `S/thirdparty/SyfcoWrapper.java:58` runs syfco with `-os mealy -ot mealy -m fully -q double -f ltl`;
   :33 parses with inputs before outputs. Default `simplify=true`
   (`S/semmlCommands/synthesisCommands/util/TechnicalArgumentPresets.java:29`).
   `S/util/Input.java:77` first heuristically reorders APs within each partition, using unfolded
   formula sizes under substitutions, then :108 calls `OwlUtil.pureLiteralSimplifications`.
   `S/smarterOwl/OwlUtil.java:47` pushes X through Boolean structure, applies restricted NNF, and
   iterates polarity substitution plus syntactic simplification up to ten times. Single-polarity
   input literals become false and output literals true (`O/cinterface/CLabelledFormula.java:226`).
   **This preserves the synthesis problem, not the word language.** Keep it outside the DPA API.
   `OwlUtil.java:82` subsequently applies `SYNTACTIC_FIXPOINT`: NNF, propositional and syntactic
   simplification, and pull-up-X, until stable or 100 iterations
   (`O/ltl/rewriter/SimplifierRepository.java:43`).

2. **Normal form.** `NormalformDELAConstruction.java:97` pushes X through Boolean connectives and removes negations while retaining
   useful top-level biconditionals. `NormalformDELAConstruction.java:851` keeps Π₂ (safety-co-safety) components and negations of
   Π₂ components (Σ₂). For anything else it tries both non-strict normalizations,
   `SE20_SIGMA_2_AND_GF_SIGMA_1` and `SE20_PI_2_AND_FG_PI_1` (`NormalformDELAConstruction.java:86`), simplifies each, then chooses by
   the exact outer-connective/operand-count heuristic at `NormalformDELAConstruction.java:897` (ties favour the second).
   `O/translations/mastertheorem/Normalisation.java:127` enumerates selected fixpoint subsets,
   constructs the rewritten Π₂/Σ₂ obligation with GF/FG side conditions, and converts to DNF.
   Its selectors and U/R/W/M-to-F/G mapping are at :311 and :395; the substitutions are in
   `O/translations/mastertheorem/Rewriter.java:68`. This is a Boolean combination of Π₂ components
   and their complements, not an LDBA determinizer. Normalization can already be exponential.

3. **Components and DELA states.** `NormalformDELAConstruction.java:175` creates a complete `SafetyCoSafety` Büchi construction
   with initial-formula-specific suspension disabled; the generic blocking checks remain active.
   `NormalformDELAConstruction.java:950` shares equal/complementary components, groups weak and suitable unique operands, and
   identifies unique GF-co-safety/FG-safety obligations for round robin. A component is the pair
   `(all, rejecting)` of propositional-equivalence classes; `rejecting=false` means suspended
   (`DeterministicConstructions.java:782`). `all` carries the residual obligation; `rejecting` tracks the current breakpoint.
   `DeterministicConstructions.java:746` extracts rejecting runs by replacing non-co-safety temporal atoms by true, removes
   unprotected X obligations, and unfolds. `DeterministicConstructions.java:682` combines symbolic temporal steps of both fields:
   false/true sinks; safety/transient/co-safety suspension; restart the breakpoint after suspension;
   otherwise progress it, marking Büchi set 0 when rejecting runs become finite and are renewed.
   The exact renewal also intersects the finite remainder with the new rejecting obligation
   (`DeterministicConstructions.java:727`); merely testing `rejecting == true` would miss this case.
   A DELA state is `(stateFormula, sorted component-index → breakpoint map, roundRobinCounters)`
   (`NormalformDELAConstruction.java:1094`), not just the derivative of the original LTL formula.

4. **Symbolic successors and Emerson–Lei acceptance.** `NormalformDELAConstruction.java:215` traverses the component decision
   DAGs together on their next AP; leaf tuples produce successors, never one call per valuation.
   Terminal components become constants in `stateFormula`; unused components disappear (`NormalformDELAConstruction.java:445`).
   Transient blocking suspends everything; weak accepting/rejecting blocking substitutes constants
   in a local acceptance formula `alpha`; round robin suspends all but the selected chain member
   and identifies the chain's acceptance variables (`NormalformDELAConstruction.java:481`, `NormalformDELAConstruction.java:589`). Component Büchi marks become
   DELA colours. The global acceptance is the initial Boolean skeleton, interpreting component i
   as `Inf(i)` and its negation as `Fin(i)` (`NormalformDELAConstruction.java:208`). On an edge changing `stateFormula`, colours
   are empty. Otherwise retain colours in `alpha` and add a fixed padding assignment outside it,
   chosen so restricting global acceptance gives `alpha` (`NormalformDELAConstruction.java:426`, `NormalformDELAConstruction.java:370`).

5. **DPA.** `S/smarterOwl/OwlUtil.java:87` passes `OptionalInt.of(0)` and the local `alpha`.
   In `ZielonkaTreeTransformations.java:168`, the initial state consumes the zero lookahead budget before successor exploration;
   therefore only conditional Zielonka trees are used. **Do not implement bounded SCC exploration,
   ACD selection, or `State.inDifferentSccs`.** The latter's warning is at `NormalformDELAConstruction.java:1170`; see the
   [prove-dela-scc-separation](review-issues/prove-dela-scc-separation.md).
   For `alpha`, `ZielonkaTreeTransformations.java:772` builds a tree rooted at its colour set. Children are the lexicographically
   ordered inclusion-maximal subsets with opposite acceptance; subtrees are shared. A DPA state
   is `(DELA state, child-index path to a leaf)` (`ZielonkaTreeTransformations.java:851`), initially the leftmost leaf (`ZielonkaTreeTransformations.java:223`).
   Equal source/target trees use `ZielonkaTreeTransformations.java:314`: descend while colours fit the current child; at the
   first failure rotate through siblings, skipping non-containing siblings (`stutter=true`),
   reset to child 0 on a full turn, and descend again when possible. The emitted **min-even**
   priority is the first anchor depth plus 0 for an accepting root, 1 otherwise. Recursive
   descent retains that first priority (`ZielonkaTreeTransformations.java:355`). Different trees reset to the new leftmost leaf
   with no colour (`ZielonkaTreeTransformations.java:234`); this comparison is tree equality, not the forbidden SCC predicate.
   `ZielonkaTreeTransformations.java:394` reserves `m+2` priorities for `m` DELA acceptance sets. SemML completes missing edges
   with a rejecting sink (`S/smarterOwl/SmarterGameViews.java:50`); the probe counts that sink.

**Relevant to counts near Owl, not prerequisites for eager admission:** canonical formula constructors and propositional classes;
syntactic fixpoint/X placement; both normalizations and their selection; component/complement
sharing and grouping; terminal pruning, weak/transient suspension, round robin; local-alpha trees;
stuttering/path reset. After the component proof gate, a plain product with a global tree is a
correctness baseline; its counts may differ from the measured construction. AP reordering affects traversal and ties;
match it in comparisons. Pure-literal preprocessing explains a separate input-language difference.

**Can wait:** the second normalizer/selection heuristic and extensive simplifier matching; grouping,
round robin, local alpha/trees and stuttering; product short-circuiting
(`NormalformDELAConstruction.java:309`, saves work without changing leaf results), extra
cache tuning, dynamic BDD ordering, acceptance minimization and game advice. Redundant-conjunct
pruning is disabled at `NormalformDELAConstruction.java:470`; do not port it. Initial-formula-specific blocking is disabled here.

**Arguments still needed:** `DeterministicConstructions.java:723` *does* call a separate component support-change shortcut,
`O/translations/BlockingElements.java:160`; blocking checks at :39/:80/:121 also discard successors
using support-size decrease (:165). Zero lookahead does not disable these. The baseline omits them;
its precise replacement is below. Stronger blocking needs
[prove-component-support-blocking](review-issues/prove-component-support-blocking.md).
Cross-component suspension, round robin and padding need
[prove-dela-suspension-round-robin](review-issues/prove-dela-suspension-round-robin.md).
Stuttering and local-tree resets need
[prove-zielonka-stutter-and-resets](review-issues/prove-zielonka-stutter-and-resets.md), including
eventual tree stability or another sufficient run invariant. The source's “switched SCC” comment
is not that argument. Keep a complete product, fixed global acceptance/tree and the ordinary
one-sibling Zielonka update until these obligations are reviewed. Tests do not discharge them.

### Conservative component: exact rules and proof gate

For an NNF syntactic Π₂ formula χ, use a **complete** deterministic Büchi component Bχ with
one transition set 0. Classes use the AP_COMBINED abstraction described in §2. Write U(c) for
unfolding with frozen modal continuations and Dᵥ(c) for one temporal step on valuation v:
evaluate current APs, unwrap X once, retain the other frozen continuations. Their combination
must represent the LTL derivative. `finite`, `safety`, `co-safety` mean the direct syntactic
Δ₀, Π₁, Σ₁ tests on every atom in non-nested class support, as in
`O/ltl/SyntacticFragments.java:42`, :64, :80; finite includes bounded X formulas.

Define R(c), matching `DeterministicConstructions.java:746–779`, precisely:

1. In c substitute true for each supported non-co-safety temporal atom; keep co-safety atoms/APs.
2. Repeatedly compute the set of X subformulas inside non-X temporal atoms of the current
   non-nested support. Replace each supported X atom outside that protected set by true, until
   the class is unchanged. In the co-safety remainder the protectors are F/U/M. This uses the
   current reduced support, not every syntactic occurrence in the original formula.
3. If U(remainder) is finite and c ≠ U(c), retry on U(c); otherwise return U(remainder).
   Unfolding is idempotent, so this retry terminates. All iterations remain budgeted.

States are `(A,R)` with unfolded A and R; R=false is the suspension sentinel, never a failed
allocation. Initialization: let c be χ's canonical NNF class; start `(U(c),false)` if U(c) is
syntactically safety or co-safety, otherwise `(U(c),R(c))`. Constants use `(false,false)` and
`(true,false)`. No initial-formula blocking heuristic is used.

For each symbolic leaf compute raw a=Dᵥ(A), r=Dᵥ(R), then a′=U(a). Apply this ordered table;
“mark” means emit set 0, and every unmarked edge emits the empty set.

| First applicable condition | Target | Mark? |
| --- | --- | --- |
| a′=false | `(false,false)` | no |
| a′=true | `(true,false)` | yes |
| a′ syntactically safety | `(a′,false)` | yes |
| a′ syntactically co-safety | `(a′,false)` | no |
| U(r)=false (resume from suspension) | `(a′,R(a))` | no |
| U(r) finite, including true | let q=U(r) ∧ R(a); if q=false use `(false,false)`, else `(a′,q)` | yes unless q=false |
| otherwise | `(a′,U(r))` | no |

Thus the false sink never marks and the true sink always marks. Renewal keeps the finite
nonconstant remainder: it is **not** replaced by true. R is extracted from raw a, not a′, using
the retry rule above. There is no transient test, support-triggered reset, external suspension,
state replacement or DELA-level pruning in this variant.

**Required theorem: L(Bχ) = L(χ)** for every admitted χ, on all infinite AP words. A completed
complement uses the same run with Fin(0), so realizes ¬χ. The proof plan is:

- Establish the derivative invariant `w[n:] ⊨ Aₙ ⇔ w ⊨ χ` until a rejecting sink, and the
  semantic implication Aₙ ⇒ Rₙ whenever Rₙ is active. Show that a renewal yielding false
  means the residual objective is false. Propositional equality alone is insufficient.
- Forward (χ ⇒ Inf(0)): in a satisfying run false is unreachable. A persistent safety
  residual marks forever; a satisfying co-safety residual reaches true after a finite witness.
  Otherwise the Π₂ alternating weak-automaton interpretation says each tracked rejecting
  cohort has no infinite rejecting branch. Finite branching then gives a finite cut by König's
  lemma, permitting renewal repeatedly, provided the cohort correspondence below is proved.
- Reverse (Inf(0) ⇒ χ): an accepting safety/true suffix satisfies the derivative. Otherwise
  infinitely many completed breakpoint rounds exclude an infinite rejecting branch; the
  Π₂ run interpretation then satisfies χ. Keeping the finite remainder in the new cohort
  must ensure a mark cannot forgive a failed delayed obligation.
- In both directions justify X deletion by relating each deleted X chain to finite delay in
  a cohort, with F/U/M-protected obligations retained. A single finite-delay observation is
  insufficient: prove that repeated deletion/renewal cannot hide an infinite rejecting branch
  or prevent a satisfying run from completing rounds. Prove the suspension/resumption cases
  and this argument **without** any support-based reset.

The derivative lemma is standard; the cohort correspondence, repeated X-elision, finite-remainder
renewal and suspension lemmas for this exact variant **remain proof obligations**, tracked by
[prove-breakpoint-x-elision](review-issues/prove-breakpoint-x-elision.md). This is a proof sketch,
not a claimed proof of those lemmas. Stage 2 cannot admit general Π₂ until their written proof
is reviewed. Stage 1 must discharge the restriction needed for its finite-window GF recurrence
(successive finite witnesses, including overlap/delay) and complement before admitting it;
unsupported cases decline. If that restriction cannot be proved, Stage 1 stays open.

## 2. C implementation and contract

**Stage 0: repair objective assembly first.** `T/src/lib/print_ltlxba.c:347` currently falls back
to true on section-pattern failure; `T/src/lib/section_pattern.c:76`, :84, :165 conflate absent
sections with failed construction. `T/src/lib/arena.c:75` does not remember allocation failure.
Fix these in tlsf-tools, not in the importer: add a sticky failure bit to the conversion arena,
set it on every failed/overflowed allocation, and never clear it during conversion. Propagate
section-assembly errors explicitly; reserve “absent” for an actually empty section. Remove the
failure-to-true fallback and stop conjunction assembly on a failed node. Check the sticky bit
and explicit status before rendering, and again before returning any conversion result; publish
neither text nor AST on failure. Printing callers must report failure before emitting objective
text. Existing non-arena allocation errors must also propagate, with cleanup. The success
postcondition is the **complete** original TLSF objective under its recorded effective timing
and semantics, not just a non-null root. See
[propagate-objective-allocation-failures](review-issues/propagate-objective-allocation-failures.md).
Every later stage depends on this repair and its fault-injection gate; disable the new arm
for conversion results lacking that contract.

**Retain the input we already have, after Stage 0.** Today `T/src/lib/conversion.c:334` parses once,
`conversion_prepare` (:223) expands and adapts the target, and :369 assembles the whole objective
with `build_spec_formula`; :380 frees its AST after printing. `TlsfConversionResult` currently
exports only text and metadata (`T/include/tlsf/convert.h:17`). Extend it with an owned
`TlsfAst *ast`, holding that same spec/root; free it with the result. Add a small internal
conversion-owned form of `TlsfAst` and use the existing node accessors/Visitor. Do not call
`tlsf_ast_from_string`: it builds a cover, residual plan and decomposition
(`T/src/lib/ast_api.c:43`), unnecessary for this arm. Retain the owner in `convert.hpp` and
`A/src/tlsf_frontend.hh` using a shared RAII handle so specification copies remain cheap.
Expose the root with the same lowercase AP spelling as the existing conversion text/partition;
apply the existing spelling validation/mapping when retaining the AST. If needed, retain a clone
with lowercase AP names in the same owner; do not mutate the parser's nodes or remap in acacia.
Preserve semantics and original/effective target metadata. No print/reparse round trip in production.

**Files.** Public `T/include/tlsf/dpa.h`; private `src/lib/dpa_internal.h`, `dpa.c` (API, interning,
budgets, labels), `dpa_formula.c` (canonical formulas, equivalence classes, symbolic steps),
`dpa_dela.c`, `dpa_zielonka.c`, and only when needed `dpa_normalform.c`; register in the existing Meson library/header
lists. Use existing arena/NNF/normalization helpers where their contracts match. The existing
normalizer is not automatically equivalent to Owl's complete simplifier. Add missing rules locally
with named equivalence checks; keep the parser AST immutable. No generic automata framework.

**Public surface (names provisional, semantics fixed).**

| Operation/type | Contract |
| --- | --- |
| `tlsf_dpa_create(root, inputs, outputs, budget, &ctx)` | Copies/interns the borrowed ground AST and AP names; computes initial metadata/state only. Accepts all infinite-word ground LTL operators, including W/M; rejects finite semantics, strong-next, unknown nodes or an invalid partition. During staging, unsupported fragments decline explicitly. |
| `tlsf_dpa_initial(ctx)` | One stable integer state ID; AP table and fixed maximum priority are also queryable after successful creation. |
| `tlsf_dpa_successors(ctx, id, &edges, &count)` | Computes/caches the **whole** symbolic successor row. Each edge is `(label_id, successor_id, priority)`. Nonempty labels partition true; merge labels only for equal `(successor, priority)`. A discovered target need not be expanded. |
| `tlsf_dpa_label_node(ctx, label_id)` | Terminal false/true or `(ap_index, low_id, high_id)`; only AP variables, no temporal/acceptance variables or OxiDD types. |
| status / `tlsf_dpa_free(ctx)` | `OK`, `DECLINED` with reason (state/node/host/deadline/cancel/unsupported/priority limit), or `INVALID`/`INTERNAL`. Free accepts null and works after any failure. No failure means false or a losing game. |

Context-local integer IDs are never recycled, survive vector growth/GC, and are directly hashable.
They need not match across contexts or exploration orders. Rows, names and node descriptions are
borrowed until context destruction; calls never invalidate earlier rows. One calling thread per
context; distinct contexts are independent. Allocate rows separately; finish interning their entire
label DAG before publication, so `label_node` is an allocation-free read. A failed construction
publishes no context; a failed expansion publishes no row and makes the context permanently declined. Previously returned rows
remain valid to free/inspect, but the consumer must abandon that attempt. No resumable transactions,
serialization, edge callbacks exposing half a row, or solver verdict in this API.

**Representation.** One private OxiDD manager per context, created by
`T/src/lib/oxidd_runtime.h:13`, with checked operations/GC conventions from
`T/src/lib/oxidd_common.h:70`. No global safety/GR(1) session. Reserve AP variables first, inputs
then outputs; append tagged temporal-atom and acceptance-colour variables as needed. Disable
reordering initially. The three namespaces share a manager but never a meaning.

- Hash-cons formula DAG nodes by operator and canonical children: flattened/sorted/deduplicated
  Boolean operands, constants, complements and X rules. Keep U/W and R/M distinct. Fragment tags,
  duals, support, unfolding and substitutions are memoized. These IDs are structural, not parser
  pointers. Retain Boolean skeleton shape for grouping and chain discovery.
- An equivalence class is a retained canonical OxiDD handle plus a formula representative.
  Boolean structure uses BDD operations, AP negation shares the AP variable. Each distinct modal
  formula is an independent variable, **including its NNF dual**. This matches Owl's default
  AP_COMBINED encoding (`O/bdd/FactorySupplier.java:36`,
  `O/bdd/jbdd/JBddEquivalenceClassFactory.java:128`, :175). Logical negation of an LTL class goes
  through NNF/dual substitution, not `oxidd_bdd_not` on its modal abstraction (:1154). Do not add
  extra temporal equivalences. Equal retained handles mean propositional equivalence, not complete
  LTL-language equivalence. Use `bdd_same_identity`/explicit handle fields for keys, not struct padding.
- Intern breakpoint pairs of class IDs; baseline DELA tuples are fixed-index arrays of pair IDs;
  DPA tuples are DELA ID and leaf path. Hash all fields, compare on collision. A state contains
  BDD classes, not one BDD node. Only deferred reductions add skeleton IDs, round-robin bitsets
  and derived local `alpha`; equal keys must then yield equal alpha. Keep the fixed global
  acceptance skeleton/colour BDD on the context. Use growable word bitsets, not a 64-colour limit.

**Baseline composition.** Extract a Boolean skeleton of Π₂ components and complemented Π₂
components (Σ₂), share identical/complementary components, and advance **every** component on
every letter, including terminal components. Use one fixed global expression α, with component i
denoting Inf(i) and its complement Fin(i). Keep constant sinks in the tuple; no skeleton changes,
chain grouping, local alpha, padding or cross-component suspension. The component theorem and
Boolean evaluation prove this complete product recognizes the supplied skeleton. A formula
outside this fragment declines until the optional normalizer is available. That normalizer uses
one complete non-strict `SE20_SIGMA_2_AND_GF_SIGMA_1` construction, including all fixpoint choices
and side conditions; bounded partial normalization declines, never drops a disjunct.

**One symbolic expansion.** Cache a reduced decision DAG with AP decision nodes and terminal
residual-class/edge IDs (a small private tagged DAG, not a new MTBDD dependency). Unfold a class
with frozen continuations: e.g. `F f → unfold(f) ∨ [F f]`,
`f U g → unfold(g) ∨ (unfold(f) ∧ [f U g])`; W has the same unfolding but different acceptance,
and R/M use the dual conjunction form. X stays frozen. Shannon-walk only current AP variables;
once they are eliminated, temporal-step replaces `[X f]` by `f` and leaves other frozen modal
atoms as residuals. Do not inspect APs under X at the current time. Memoize unfolding and DAG
apply/product operations (`O/bdd/jbdd/JBddEquivalenceClassFactory.java:1136`, :1215).
Combine the two breakpoint DAGs using the exact table above, then all component DAGs; evaluate
the fixed product update at each distinct terminal tuple. Map DELA edges through the selected
Zielonka path. Deferred reductions may later use §1's optimized DELA update. Convert the final
DAG to OxiDD label BDDs by propagating/OR-merging guards through shared nodes, then coalesce rows.
Complexity follows the symbolic DAG and its product, which can still be exponential; there is
no `for letter in 2^AP`, even over the smaller support. Budget scratch DAGs and products too.

**Acceptance without a SAT dependency.** Store colour formulas as OxiDD BDDs, retaining skeletons
and their colour universe for Owl's structural rules; reduced BDD support alone loses that shape.
For a Zielonka node C, restrict colours outside C to false, find a model
of the opposite acceptance, and repeatedly ask for a strict satisfying superset until none exists.
Record that maximal model M, block all its subsets by requiring some colour in C∖M, and repeat;
sort the results lexicographically and intern subtrees. Single-variable greedy flips are insufficient for arbitrary
Boolean acceptance. Use one global tree from creation. Its ordinary update finds the deepest
node on the current leaf path whose colour set contains the edge colours; emit its depth plus
0 for an accepting root, 1 otherwise. At a non-leaf anchor advance exactly one sibling modulo
its child count and descend to that child's leftmost leaf; at a leaf retain the path. Do not
skip siblings or recursively process the same colour set. The usual recurrent-set argument
applies: the minimum recurring anchor depth, with the root offset, is even exactly when α
accepts the recurring colour set. Record that argument with the implementation, including empty marks
and empty leaf paths. Stage 1 uses this same routine on its one-set tree; Stage 2 generalizes
the tree builder, not the update semantics. Stuttering is separately proof-gated.
Only in deferred local-alpha work, for padding solve `forall active_colours: (global ↔ alpha)` for the dropped
colours; check the chosen cofactor equals alpha before caching it. This replaces Owl's SAT calls
with existing BDD quantification. All these loops are cancellable and bounded.

**Parity and completion.** Export **max-odd** (odd recurring maximum accepts), matching
`A/src/solver/parity/game.cc:125`. If there are m DELA acceptance sets, Owl's ordinary min-even
priorities are at most `m+1`. Fix P to the smallest odd integer greater than `m+1` at creation;
export `P-p`. For odd P, the recurring maximum is P minus the recurring minimum and is odd
exactly when that minimum is even. Empty DELA colour sets still get an ordinary path priority.
The baseline has no tree-reset edges. Deferred tree-reset edges get 0, smaller than every ordinary priority.
Missing valuations go to one lazily interned rejecting sink with a true/priority-0 self-loop.
The reviewed finite-reset argument is required before enabling those resets.
Keep the false initial DELA state if present, rather than identifying it with completion's sink,
when comparing counts. Check integer overflow; acacia also declines if Spot's acceptance width
cannot represent the declared priorities. Do not silently truncate priorities.

**Ownership and stopping.** The context owns formula storage, tables, DAGs, cached rows, exported
node IDs and every retained BDD reference; release BDDs before the manager. Exported label IDs
intern and pin their OxiDD functions so GC cannot reuse a memoized identity. Count C allocations
and scratch space before allocating, including arena slab capacity rather than just used bytes;
helpers using uncharged allocation need a bounded wrapper or a local implementation.
Bound DPA states on discovery (including the sink), and bound
BDD manager nodes/cache separately. Component/formula/tree tables count against host space, not
the DPA-state counter. Reuse `OxiddSolveOptions` deadline/cancellation conventions
(`T/include/tlsf/oxidd_options.h`); expose explicit state, host-byte and BDD-node/cache caps.
Poll cancellation callback (which may load an atomic flag) and monotonic deadline before/after
BDD operations and in normalization, model enumeration, hashing/expansion loops. Never call the
FFI with an invalid handle; OxiDD exhaustion is a decline. Creation uses the same budget as expansion.
Deadline/cancel is cooperative: an individual FFI operation is not interruptible. Node/cache caps
are not a hard RSS bound; retain the worker's existing process limit for that. The eager importer
also accounts for its BFS, memo and Spot graph, and returns UNKNOWN on any failure. Only an empty
BFS queue permits solving; a prefix graph is never an eager answer.

## 3. The bddx boundary and eager acacia arm

`A/src/tlsf_frontend.cc:40` currently copies conversion text/metadata. Retain the conversion AST
alongside it for TLSF input. Build from its **positive effective-Mealy objective**, exactly once;
retain the original target for the existing controller conversion. Initially decline text/HOA-only
requests lacking this AST. The DPA library never swaps players or rewrites timing.

Add `A/src/solver/parity/tlsf_dpa.{hh,cc}`: RAII context, BFS importer, and one label memo per
`(context, Spot dictionary, AP mapping)`. Register all declared APs, including unused ones, on the
destination graph. Map each library AP index by name to the returned Spot variable number, never
by numeric coincidence. False/true map to `bddfalse`/`bddtrue`; a node maps to
`bdd_ite(bdd_ithvar(ap_to_buddy[index]), memo[high], memo[low])`. Use an iterative postorder walk;
memo entries own `bddx` references. This is the small DAG counterpart of
`T/include/tlsf/ast_api.hpp:89`'s formula Visitor, with sharing across **all** labels/rows.
Cost is O(distinct exported nodes) bridge visits plus BuDDy ITE costs; no DNF, cubes, text or OxiDD
pointer crosses the boundary. Different variable orders work. Destroy the memo before its
dictionary; the finished Spot graph owns its own BDD references and can outlive the DPA context.

Expose an opt-in `both:parity:tlsf` arm in `parity_arm.cc`, portfolio parsing/naming and help.
Refactor a narrow “solve already-positive DPA” entry point in `solver/parity/route.{hh,cc}`.
For this arm, bounded BFS/import replaces **translate** (`route.cc:126`), worker orientation and
classification (:149), and **parity conversion** (:199); set the supplied acceptance directly.
Simply passing `request.automaton` to today's `run()` would still classify/ACD-transform it.
Reuse partition registration (:142), determinism/completeness checks, **split** (:211), **solve**
(:216), callbacks, strategy/controller extraction and verification (:225 onward). No complement
is needed: odd accepts the system's positive objective. Keep current source/frame semantics for
other callers. Preserve effective-Mealy→Moore controller handling in `parity_arm.cc:108`; never
also request native-Moore splitting for that input. Record construction/BFS/label/import sizes
and declines separately from split/solve. Leave portfolio defaults unchanged pending corpus gates.

Later #340 arms can consume the same IDs and complete rows. They need their own reviewed frontier
soundness note and can re-solve with doubling budgets; no incremental game solver is needed here.

## 4. Checks that decide whether this works

- **Language, the release gate.** In a C++ test linked to libtlsf and Spot, rebuild the input formula
  through the AST Visitor and labels through the production bridge. BFS to completion; check one
  initial state, disjoint guards, coverage=true, valid priorities, stable IDs and repeatable rows.
  Run `spot::are_equivalent` against an independent Spot translation of **that exact input formula**.
  Keep a counterexample lasso on failure. Check both acceptance orientations and negated formulas.
  Include true/false, unused APs, delayed obligations, all temporal duals, nested alternations,
  biconditionals/shared complements and GF/FG chains. Suspension/resumption and changing local
  trees are additional gates when those optimizations are proposed.
- **First-slice acceptance and bridge gate.** Include `GF(a & X b)` and its complement
  `FG(!a | X !b)`, using the real breakpoint recurrence and shared one-set Zielonka path code;
  include accepting/rejecting lassos with overlapping and delayed witnesses, plus
  `G(req → X grant)`, `F grant`, true/false. For each published source s and each `(target t,
  priority p)`, compare the OR of its exported C label guards with the bridge's bddx guard,
  using the importer's explicit source/target ID map and the same named-AP valuation.
  Exhaust small alphabets and assert equal truth values
  for **every** `(s,t,p)` (absent guards mean false), under several permuted AP→BuDDy maps,
  including gaps and unused declarations. A test evaluator walks the exported label DAG
  directly, independently of the bridge. Coverage, determinism and language equivalence do
  not replace this exact relation check. Require correct verdicts and verified controllers.
- **Objective failure gate (Stage 0).** Deterministically fail section entry-array growth for
  `GUARANTEES { false; }`, then conjunction construction for `GUARANTEES { p; !p; }`. Let later
  allocations succeed so the former successful-true fallback is exposed; also force arena slab
  failure with spare capacity for later small allocations. Check failure status, no published
  text/root, no solver verdict, and clean destruction. Run a fail-at-each-allocation sweep of
  the affected assembly/conversion paths and a following healthy conversion. Independently
  assert that both successful unfaulted objectives denote false; comparing Spot to the returned
  AST alone cannot detect the corrupted-objective bug. Cover empty sections and both strict
  and non-strict assembly so legitimate absence still succeeds.
- **Differentials per layer.** Compare unfolded/stepped obligations and Δ₂ results with Spot for
  equivalence; compare small component/DELA transition DAGs, alpha/padding and Zielonka paths against
  Owl. An exact SCC computation in tests can check proposed blocking certificates; production has
  no SCC exploration. Force cap/cancel/deadline/allocation failures at creation and midway through
  expansion/import: no published partial row, no solve call/verdict, clean destruction. Starting
  in Stage 1, force a later expansion to decline **after earlier complete rows were published**;
  check those rows remain inspectable and the context is permanently declined. Separately fail
  BFS/import after rows and labels have entered the Spot graph (including host allocation/cap
  or cancellation during label rebuild); discard that graph and return UNKNOWN without calling
  solve. Test reversed dictionary order, shared label subgraphs, repeated edges and GC between expansions.
  Use sanitizers and the existing build/tests. A large declared alphabet with tiny current support
  must remain small; include a DAG-sharing case so support-only valuation enumeration cannot pass.
- **Random and corpus.** Fixed-seed formulas stratified by depth, Π₂/Σ₂/Δ₂ and shared subformulas;
  thousands of small cases with complete equivalence checks, plus minimized saved regressions.
  Run all available SYNTCOMP inputs, explicitly the 69 M0 cases, under matched time/memory limits.
  Record completed states, symbolic edges/nodes, priorities, peak memory, construction/import time,
  solve time and verdict. A timeout/limit is censored data, never an equivalence pass or full count.
  Verify produced controllers against the original objective as the incumbent route does.
- **Owl counts and formula differences.** Run the existing `../probe/run.sh TLSF STATE_LIMIT`
  (`DpaProbe.java:29`, :63) unchanged as the M0 anchor; count reachable **completed DPA** states,
  not DELA states, game vertices or strategy states. Use its `-Xss64M` setup. FULL counts are exact;
  LIMIT/timeout counts are lower bounds. Report actual tlsf-tools-product/probe counts on the
  same TLSF as an end-to-end comparison, without attributing the whole difference to construction.
  A test-only helper must also capture syfco's raw formula and SemML's actual `Input.formula()`
  **after AP reorder/pure-literal simplification**, including the AP order/partition. Feed that
  post-Input formula into the C ground AST. “Exact” is structural: compare operator tags
  (including U/R/W/M and X nesting), constants/literal polarity, Boolean grouping and ordered
  children at construction entry, and the full ordered AP-name table/partition including unused
  APs. A TLSF wrapper is acceptable only after this transport check; language equivalence alone
  does not qualify. If transport canonicalizes the structure, feed the resulting **actual C
  input AST** to the direct Owl helper and compare those two counts instead of claiming identity
  with the original probe. For the product's unmodified objective, the same helper consumes that
  exact AST through a test-only structural transport, constructs the labelled formula with its
  AP order, then calls `OwlUtil.ltl2Dela/dela2Dpa`, without `Input.of`. Record input structure and
  AP-order fingerprints and each side's later preprocessing separately. Canonicalization inside
  the constructors is a construction difference to measure. Keep the probe/M0 logs unchanged. Do not reparse Owl's
  compact printed formula through `Input.of`; the probe already documents that stall.
  Spot-check language equivalence of syfco's **raw** effective-Mealy formula and tlsf-tools' formula
  after explicit AP-name/bus mapping, with strict semantics and target adaptation preserved.
  Non-equivalent conversions are separate frontend failures; quarantine their count comparison.
  SemML's pure-literal result need not be language-equivalent to either raw formula. No relabelling
  a synthesis-preserving change as language equivalence. Compare exact counts on agreed microcases;
  on structurally matched, jointly completed corpus formulas report median/p90/max ratios and
  explain material regressions. Always report completion coverage and unsupported/decline/timeout
  counts over **all 69**, so ratios cannot hide excluded hard inputs. Counts are diagnostic;
  paired time/memory and coverage decide whether the simpler baseline is useful.

## 5. Writer stages and estimates

Production estimates include C/C++ headers, helpers, build wiring and arm integration; exclude
tests, comments and blanks. Ranges allow for missing canonicalization/simplifier utilities.
Each row extends the same buildable constructor; unsupported cases decline. **Stage 0 is a
mandatory dependency of every later stage**, including optional/deferred work.

**Inventory before Stage 1, after Stage 0.** Join the 69 names in
`../../otfpar/semml-only.list` to `A/tests/suites/benchmarks/syntcomp26/tlsf-sources.tsv`, checking
one source per name and reporting any missing source. Reuse the existing conversion path to
obtain each complete, expanded effective-Mealy objective, with its AP table and semantics;
classify the whole implication, not just individual TLSF sections. Use Owl's existing
`SyntacticFragments.FormulaClass.classify` on NNF after the baseline's X-through-Boolean
transport; no normalizer or pure-literal substitution. This is a cheap syntax walk, with no
automaton construction. Reuse `ltl-inspect`/`ltl-utilities` if an Owl CLI is installed; otherwise
call the same existing parser, NNF/X visitor and classifier from JShell using `../probe/run.sh`'s
classpath. No new classifier, production code or dependency is needed. Preserve/verify the
transport structure as in §4. Separately classify SemML's post-Input formulas to explain the
M0 gap; those counts cannot substitute for the product-objective inventory.

Record, per input: syntax class, Stage 1 support, Boolean Π₂/Σ₂ product support (Δ₂), or needs
normalization; a parse/conversion/transport failure is “unknown”, not fragment membership.
NNF removes biconditionals for classification; X distributes through Boolean skeletons so a
Boolean combination under X is not falsely excluded. Record actual rewrites and any Owl-only
simplification separately. Summarize coverage over 69 and the M0 FULL-43 subset from `../PLAN.md`'s
logs. This inventory is planned work, not a claimed result here. If selected target inputs fall
outside the product fragment, schedule Stage 4 **after** the first Stage 3 experiment; if none
do, omit it. Missing/unknown rows must be resolved before deciding the normalizer is unnecessary.

| Stage | Production lines | Test/harness lines | Closing test |
| --- | ---: | ---: | --- |
| 0. Repair tlsf-tools objective allocation/error propagation, including arena, section assembly, conversion and printing callers. | 150–300 | 120–220 | §4's deterministic one-shot failures and allocation sweep: no successful text/AST/verdict on failure; healthy objectives independently checked. Prerequisite for every row below. |
| 1. Strengthened complete slice: retain AST; IDs/budgets; OxiDD classes/symbolic derivatives; safety/co-safety plus finite-window GF recurrence and complement; shared one-set Zielonka path; bridge, BFS and minimal opt-in eager arm. | 1,500–2,200 | 400–650 | Restricted breakpoint proof reviewed; `GF(a & X b)`/complement and §4 examples: full Spot equivalence, exact `(target,priority)` bridge relation under permuted AP maps, verified controller, and declines after publication and during import. |
| 2. Complete Boolean Π₂/Σ₂ product; completed components; fixed global acceptance/tree; generic maximal-model tree builder and ordinary one-sibling path update. | 1,400–2,200 | 350–600 | **Reviewed L(Bχ)=L(χ) proof for the exact variant**, including X elision, finite remainders and no support resets (`prove-breakpoint-x-elision`); mixed/shared/complement formulas, empty marks, full Spot equivalence and Owl layer checks. No general Π₂ admission before the proof gate. |
| 3. Hardening and first eager admission experiment, immediately after Stage 2: finish accounting/diagnostics and arm plumbing; fault paths and Spot width limits; paired corpus/controller measurements. | 300–600 | 250–450 | All 69 attempted with support/decline/coverage visible; no completed language/verdict mismatch or lost incumbent solve; paired construction/import/split/solve time and memory. Retain opt-in unless owner gates pass. |
| 4. Conditional: one complete Δ₂ normalizer, only if the inventory identifies needed unsupported targets. | 1,000–1,800 | 300–500 | Nested alternation and random LTL: normalization equivalence and composed DPA equivalence; all choices/side conditions included; blowup declines. Repeat admission measurements for the added coverage. |
| 5. Deferred (old Stage 4): grouping/pruning, suspension, round robin, local alpha/padding, local trees and stuttering; only reductions justified by measurements. | 1,400–2,400 | 400–700 | Separate reviewed proofs under `prove-component-support-blocking`, `prove-dela-suspension-round-robin` and `prove-zielonka-stutter-and-resets` before enabling affected reductions; full language suite and structural-input count diagnostics. Zero lookahead stays fixed. |

Through Stage 3: **3,350–5,300 production lines** and **1,120–1,920 test/harness lines**, including
Stage 0. With conditional Stage 4: **4,350–7,100 production**, **1,420–2,420 test/harness**.
Deferred Stage 5 is additional and is not an admission prerequisite. A second normalizer,
selection heuristic and extensive Owl simplifier matching are unscheduled; estimate them only
if measured count/coverage regressions justify that work. The eager experiment needs none of them.

The Stage 1 single-component wrapper uses the same state/edge/label machinery; extend it rather
than retaining a separate shortcut backend. Writers should submit the smallest counterexample
with any failed gate. The owner drives builds and measurements per `../PLAN.md`; this document
specifies them, and does not claim they have run for the proposed C implementation.

## 6. Owner questions (recommendations supplied; none blocks this design)

1. **Which coverage and paired time/memory gains admit the eager arm?** Recommend exact agreed
   microcases and zero completed language/verdict mismatches; use Owl counts diagnostically,
   with completion coverage and paired time/memory results deciding usefulness. Remove the
   provisional median ≤1.25/p90 ≤2 count thresholds as admission requirements. Owner to set the
   paired performance/coverage gates; conservative syntax/blocking may legitimately differ.
2. **Pure-literal simplification in the product?** Defer it. Keep the DPA language equal to its
   supplied AST; use SemML's simplified input only in the separate count experiment. Any later
   synthesis preprocessing must carry the fixed-output substitutions into controller extraction.
3. **Initial arm budgets?** Recommend configurable ceilings of 100,000 discovered DPA states,
   120 s and **min(existing worker memory allowance, 8 GiB)**. Share the deadline across
   construction/import and account for both, including BFS, label memo and Spot graph.
   Calibrate OxiDD/cache/host caps from C measurements within that process envelope; do not
   allocate the entire allowance to BDD nodes. Owner to confirm/calibrate these experimental
   ceilings; they are not a new default portfolio policy.

VERDICT: done
