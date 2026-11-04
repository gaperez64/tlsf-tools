# State-by-state LTL to DPA

The bounded lazy C23 API constructs ground TLSF AST → Boolean Π₂/Σ₂ components
→ deterministic Emerson–Lei automaton (DELA) → Zielonka tree → DPA. Eager
translation is BFS over that API; a consumer can rebuild symbolic labels in its
own Boolean representation and reuse splitting/solving. A complete Δ₂ normalizer is conditional on needed
inventory coverage. There is one constructor, no alphabet enumeration, Java
runtime, new dependency, or external automata in libtlsf.

The language proofs and C boundary are in [proofs/README.md](../../proofs/README.md#automaton-translation-validation).
This design also specifies external Acacia integration and original comparison
gates; it does not claim all those gates ran. Repository tests use
frozen goldens/native checks using only in-house tooling. External import and
comparison details below belong to external consumers/offline validation.

## Conservative component: exact rules and proof gate

For NNF Π₂ χ, Bχ is complete deterministic transition-Büchi with set 0.
Use the [AP_COMBINED classes, unfolding U, and simultaneous step Dᵥ](STAGE1-PROOF.md#fragment-and-classes).
Finite/safety/co-safety are direct syntactic Δ₀/Π₁/Σ₁ tests on non-nested
class support (`O/ltl/SyntacticFragments.java:42,64,80`); finite includes bounded X.
Define extractor ρ (called R in the original design):

1. Replace supported non-co-safety temporal atoms with true; keep co-safety/APs.
2. From current reduced support, collect syntactic X subformulas of non-X modal
   atoms. Simultaneously replace supported X atoms outside that set with true;
   repeat until unchanged. Surviving protectors are F/U/M. Traverse frozen
   syntax, including operands that materialization would absorb, and recompute
   protection after every changing pass.
3. Unfold the remainder. If finite and `c≠U(c)`, retry on U(c). Idempotent
   unfolding permits at most one retry; changing elision removes supported X
   variables. Budget every iteration.

States `(A,R)` have unfolded fields; R=false is suspension, never allocation
failure. Initialize χ's canonical class c as `(U(c),false)` when safety/co-safety,
otherwise `(U(c),ρ(c))`; constants use `(false,false)`/`(true,false)`.
For each symbolic leaf compute raw `a=Dᵥ(A)`, `r=Dᵥ(R)`, `a′=U(a)`, then use
the first applicable row. Marks emit set 0; unmarked edges emit ∅.

| First applicable condition | Target | Mark? |
| --- | --- | --- |
| a′=false | `(false,false)` | no |
| a′=true | `(true,false)` | yes |
| a′ syntactically safety | `(a′,false)` | yes |
| a′ syntactically co-safety | `(a′,false)` | no |
| U(r)=false (resume from suspension) | `(a′,ρ(a))` | no |
| U(r) finite, including true | let q=U(r) ∧ ρ(a); if q=false use `(false,false)`, else `(a′,q)` | yes unless q=false |
| otherwise | `(a′,U(r))` | no |

Renewal retains finite nonconstant `U(r)` and extracts raw a with retry.
False/true sinks never/always mark. There is no initial blocking, transient
support reset, external suspension, state replacement, or DELA pruning.
Completeness makes Fin(0) on the same run recognize the complement once
`L(Bχ)=L(χ)` is proved.

[The restricted proof](STAGE1-PROOF.md) covers safety/co-safety and finite-window
GF/FG; [the flat converse](STAGE2-PROOF.md#flat-converse) extends it.
`GeneralConverse.lean` proves the general reference theorem. These cover exact
derivatives, `A⇒R`, both language inclusions, repeated syntactic X elision,
finite-remainder renewal, and suspension without support resets. A finite-delay
observation alone would not suffice. C/bridge validation remains separate.
Support blocking, cross-component suspension/round robin/padding, stuttering,
and local-tree resets need their own reviewed proofs; tests do not discharge them.

## C implementation and contract

Successful conversion must publish the complete objective under effective timing
and semantics. Objective assembly needs sticky arena allocation/overflow failure,
explicit section-construction errors distinct from empty sections, no failure-to-true
fallback, and cleanup for non-arena failures. Check status before rendering and
return; publish neither text nor root on failure. This is mandatory before using
the DPA arm, with the fault-injection gate below. The audited repair sites were
`T/src/lib/print_ltlxba.c:347`, `T/src/lib/section_pattern.c:76,84,165`, and
`T/src/lib/arena.c:75`.

Retain the already parsed/expanded/adapted objective as owned `TlsfAst *ast` in
`TlsfConversionResult`; free it with the result. The audited flow is
`T/src/lib/conversion.c:334` parse, `conversion_prepare:223`, `build_spec_formula`
at 369, old post-print destruction at 380, and `T/include/tlsf/convert.h:17`.
Use a conversion-owned AST with existing accessors/Visitor; avoid
`tlsf_ast_from_string` (`T/src/lib/ast_api.c:43`), which constructs unnecessary
cover/residual decomposition. Shared RAII ownership in `convert.hpp` and
`A/src/tlsf_frontend.hh` keeps spec copies cheap. Apply existing lowercase AP
validation/mapping, cloning inside the owner if necessary; preserve original/
effective target and semantics. Do not mutate parser nodes, remap in Acacia,
or print/reparse in production.

Public header is `T/include/tlsf/dpa.h`; private files are `src/lib/dpa_internal.h`,
`dpa.c` (API/interning/budgets/labels), `dpa_formula.c` (classes/steps),
`dpa_dela.c`, `dpa_zielonka.c`, and conditional `dpa_normalform.c`.
Register existing Meson library/header lists and reuse helpers only where
contracts match. Missing simplifier rules need named equivalence checks;
existing normalization is not automatically Owl's complete simplifier.
No generic automata framework is needed. The proposed public surface is:

| Operation/type | Contract |
|---|---|
| `tlsf_dpa_create(root, inputs, outputs, budget, &ctx)` | Copy/intern borrowed ground AST/AP names; initialize metadata/state only. Infinite ground operators include W/M. Null, empty, or duplicate AP names return `INVALID`; finite semantics, strong-next, unknown nodes, and staged unsupported fragments decline. |
| `tlsf_dpa_initial(ctx)` | Stable integer state ID, AP table, fixed maximum priority after creation. |
| `tlsf_dpa_successors(ctx, id, &edges, &count)` | Cache/publish one complete symbolic row `(label_id, successor_id, priority)`. Nonempty labels partition true; merge only equal target/priority. Targets need not be expanded. |
| `tlsf_dpa_label_node(ctx, label_id)` | False/true or `(ap_index, low_id, high_id)`, with only AP variables and no OxiDD types. |
| Status / `tlsf_dpa_free(ctx)` | `OK`, reasoned `DECLINED` (state/node/host/deadline/cancel/unsupported/priority limit), `INVALID`, or `INTERNAL`. Free accepts null/failed attempts. Failure never means false or losing. |

Context IDs are hashable, unrecycled, GC/vector-growth stable, but may differ
by context/exploration order. Borrowed rows/names/nodes remain valid until
destruction. Allocate rows separately and intern whole label DAGs before
publication; label reads allocate nothing. One caller per context; contexts
are independent. Failed creation publishes no context; failed expansion publishes
no row and permanently declines the context. Old rows remain inspectable until
free, but consumers must abandon the attempt. No partial callbacks, resumable
transactions, serialization, or solver verdicts are provided.

One private OxiDD manager per context uses `T/src/lib/oxidd_runtime.h:13` and
checked/GC conventions in `T/src/lib/oxidd_common.h:70`, separate from safety/GR(1)
sessions. Variables are inputs, outputs, then tagged temporal/acceptance namespaces;
reordering is initially disabled. Hash-cons formulas by operator/canonical children
(flatten/sort/deduplicate Booleans, constants/complements/X rules), preserving
U/W and R/M distinctions and skeleton shape. Memoize tags, duals, support,
unfolding, substitutions; use structural IDs rather than parser pointers.

Classes retain OxiDD handles and formula representatives. Each distinct modal
formula and NNF dual is independent; AP negation shares its variable. This is
Owl AP_COMBINED (`O/bdd/FactorySupplier.java:36`,
`O/bdd/jbdd/JBddEquivalenceClassFactory.java:128,175`). Negate through NNF/dual
substitution, not `oxidd_bdd_not` (:1154); add no temporal equivalences.
Equal handles imply propositional equality only. Key explicit fields/
`bdd_same_identity`, never padding. Intern breakpoint pairs, fixed-index DELA
arrays, and DELA-ID/leaf-path DPA tuples; hash all fields and compare collisions.
States contain classes, not one BDD node. Deferred skeleton/counter/local-alpha
keys must determine alpha uniquely. Global acceptance stays on the context;
growable word bitsets avoid a 64-colour limit.

The baseline shares equal/complementary components, advances every component
including sinks on every letter, and uses fixed α interpreting i as Inf(i),
its complement Fin(i). There are no skeleton changes, local alpha, padding,
grouping, or cross-component suspension. Boolean evaluation and component
correctness prove the product language. Unsupported formulas decline until
needed complete `SE20_SIGMA_2_AND_GF_SIGMA_1` normalization supplies all fixpoint
choices/side conditions. Partial bounded normalization must decline, never
remove disjuncts.

Symbolic expansion uses a cached reduced private DAG of AP decisions and
terminal residual/edge IDs, without another MTBDD dependency. Unfold with
frozen continuations as defined above; W shares U's equation with different
acceptance, R/M use the dual, and X stays frozen. Shannon-split only current APs;
then replace `[X f]` by f without evaluating its exposed APs. Memoize unfolding/
DAG apply/products (`O/bdd/jbdd/JBddEquivalenceClassFactory.java:1136,1215`).
Combine both fields through the ordered table, then component DAGs; update each
distinct terminal tuple and map through the Zielonka path. Propagate/OR guards
through shared DAG nodes into OxiDD labels and coalesce rows. Complexity follows
DAG/products and may be exponential. Never loop over `2^AP`, even on support;
charge scratch DAGs/products too.

Store acceptance as BDD plus structural skeleton/universe. At tree label C,
set outside colours false, find an opposite-acceptance model, extend to a strict
satisfying superset until maximal, record M, and block all its subsets with
some colour in C∖M. Repeat, lexicographically sort, and share subtrees.
Single-bit greedy flips are insufficient. One global tree is fixed at creation.
The ordinary update anchors at the deepest path node containing edge colours,
emits depth plus accepting-root offset 0/rejecting offset 1, advances exactly
one sibling modulo child count, then descends leftmost; a leaf retains its path.
No skipping/reprocessing colours. The [recurrent-set proof](STAGE2-PROOF.md#global-zielonka-tree-and-parity)
includes empty marks/paths. Stage 1 uses this routine on one set; larger trees
change the builder, not update semantics. Deferred padding solves
`forall active_colours: (global ↔ alpha)` for dropped colours and checks the
chosen cofactor before caching, using BDD quantification instead of SAT.
All loops are bounded/cancellable.

Export max-odd, matching `A/src/solver/parity/game.cc:125`. With m colours,
min-even p is at most m+1; choose the smallest odd `P>m+1` at creation and
export `P-p`. Then recurring maximum is odd iff recurring minimum was even.
Empty marks get ordinary priorities. Deferred tree resets get 0 below every
ordinary priority and require a finite-reset proof. Missing valuations use
one lazy rejecting sink with true/priority-0 loop; retain a distinct false
initial DELA state for count comparisons. Check overflow and consumer acceptance
width; never truncate.

The context owns storage/tables/DAGs/rows/IDs and BDD references; release handles
before the manager. Exported labels pin functions against GC identity reuse.
Charge all C/scratch allocations before use, including arena slab capacity;
wrap uncharged helpers. Discovery counts DPA states including sink; formula/
component/tree tables count host bytes, and BDD nodes/cache have separate caps.
Reuse `OxiddSolveOptions` deadline/cancel conventions (`T/include/tlsf/oxidd_options.h`).
Creation shares expansion budgets. Poll callbacks/monotonic deadlines around
BDD calls and in normalization/model/hash/expansion loops; never pass invalid
handles. FFI calls are not interruptible, and node/cache caps do not bound RSS:
retain process limits. Importer BFS/memo/consumer graph also need accounting. Any
failure returns UNKNOWN; solving requires an empty BFS queue, never a prefix graph.

## Consumer import and eager arm

Retain TLSF conversion AST alongside text/metadata (`A/src/tlsf_frontend.cc:40`).
Build its positive effective-Mealy objective once; keep original target for
controller conversion. Text/HOA-only input lacking the AST initially declines.
The library never swaps players or adapts timing.

A consumer owns the RAII context, BFS, and a label memo keyed by context and
AP mapping. Preserve every declared AP, including unused declarations, and map
indices by name. Constants map to Boolean constants; a decision selects the
high or low child according to that AP. Iterative postorder memo entries own
the consumer's Boolean handles across all rows, analogous to
`T/include/tlsf/ast_api.hpp:89`'s Visitor. Bridge work scales with distinct
exported nodes plus Boolean-operation cost. No DNF/cubes/text/OxiDD pointers
cross this boundary. Destroy the memo before the consumer's Boolean manager.

Opt-in `both:parity:tlsf` needs `parity_arm.cc`, portfolio naming/parsing/help,
and a narrow already-positive-DPA entry in `solver/parity/route.{hh,cc}`.
BFS/import replaces translate (`route.cc:126`), orientation/classification (149),
and parity conversion (199); supplying `request.automaton` to old run() would
still classify/ACD-transform. Reuse partition registration (142), determinism/
completeness, split (211), solve (216), callbacks/extraction/verification (225+).
Odd already accepts the positive system objective; no complement is needed.
Other callers keep their frames. Preserve effective-Mealy→Moore handling
(`parity_arm.cc:108`), without also requesting native-Moore splitting. Record
construction/BFS/label/import costs and declines separately; defaults await
corpus gates. Later #340 frontier arms need independent soundness review and
may double budgets without an incremental solver.

## Validation gates

Finish BFS and check one initial state, guard partition, priorities, stable IDs,
and repeatable rows. Kernel-checked Lean translation validation checks completed
automata against formula semantics, while an independent direct word evaluator
reproduces memberships. Check both acceptance
orientations/negations, constants, unused APs, delayed obligations, temporal
duals/nesting, shared complements/biconditionals, GF/FG. Suspension/local-tree
optimizations add gates. Current repository replacements are documented in
[golden fixtures](../../test/fixtures/golden/README.md).

First-slice cases include `GF(a & X b)`, `FG(!a | X !b)`, `G(req → X grant)`,
`F grant`, constants, and overlapping/delayed accepting/rejecting lassos.
For every source/target/priority, compare OR-ed C guards against imported Boolean functions
using explicit state maps and named-AP valuations, with absent guards false.
Exhaust small alphabets under permuted/gapped AP maps including unused APs;
a separate evaluator walks label DAGs. Coverage/determinism/language equality
do not replace this relation check. Require correct verdicts/verified controllers.

Objective failure tests must independently show false objectives for
`GUARANTEES { false; }` and `GUARANTEES { p; !p; }`, then fail entry-array growth,
conjunction, and arena slabs while permitting later allocations. Require failure,
no text/root/verdict, clean destruction, fail-each-allocation sweeps, and a
healthy follow-up. Comparing only a returned AST to a reference cannot catch corrupt
objective assembly. Cover empty and ordinary/strict sections.

Layer checks compare unfolding/steps/Δ₂ with the Lean reference and small component/DELA
DAGs, alpha/padding, and Zielonka paths with Owl. Test-only SCC computations
may check blocking certificates; production has no SCC exploration. Force
caps/cancel/deadline/allocation failure at creation, mid-expansion, after rows
were published, and during BFS/label import. Old rows stay inspectable, context
stays declined, partial graphs are discarded, and solve is never called.
Test reversed dictionaries, shared labels/repeated edges, inter-expansion GC,
large alphabets/tiny support, and DAG sharing that defeats support enumeration.
Use sanitizers and existing builds/tests.

Fixed-seed random tests stratify depth, Π₂/Σ₂/Δ₂, and sharing; thousands of small
complete comparisons retain minimized regressions. Attempt all available
SYNTCOMP inputs and all 69 M0 cases under matched resources. Record completed
states, symbolic edges/nodes, priorities, peak memory, construction/import and
solve time/verdict. Timeouts/limits are censored, never equivalence passes/full
counts. Verify controllers against the original objective.

For Owl counts, retain `../probe/run.sh TLSF STATE_LIMIT` (`DpaProbe.java:29,63`)
and `-Xss64M`. Count completed reachable DPA states; FULL is exact, LIMIT/timeouts
lower bounds. End-to-end TLSF count differences include frontend differences.
A test-only helper captures raw syfco and post-`Input.formula()`/AP-reorder/
pure-literal formulas with full AP partition/order, including unused APs.
Transport must match operator tags (U/R/W/M, X depth), constants/polarities,
grouping, ordered children, and AP tables structurally; equivalence alone is
insufficient. If transport canonicalizes, compare direct Owl against actual C
AST, not the original probe. For unmodified objectives, directly call
`OwlUtil.ltl2Dela/dela2Dpa` on that exact AST without `Input.of`. Record structure/
AP fingerprints and later preprocessing separately; internal canonicalization
is a measured construction difference. Keep M0 logs; reparsing compact Owl
text through `Input.of` stalls.

Check raw syfco/tlsf-tools equivalence after explicit AP/bus mapping, preserving
strict/target semantics. Quarantine frontend mismatches. Pure-literal SemML
results preserve synthesis, not necessarily word language. Compare exact agreed
microcase counts; on structurally matched completed pairs report median/p90/max
ratios and material regressions. Always report coverage/unsupported/decline/
timeouts over all 69; ratios must not hide hard inputs. Paired time/memory and
coverage decide utility, not counts alone.

## Work scope and estimates

Each stage extends one constructor with explicit unsupported declines; objective
repair is mandatory for all. Estimates exclude tests/comments/blanks from
production, include headers/helpers/build/arm wiring, and allow missing utilities.
Join the 69 `../../otfpar/semml-only.list` names to
`A/tests/suites/benchmarks/syntcomp26/tlsf-sources.tsv` one-to-one; report missing
sources. Classify complete effective-Mealy objectives, not sections, after NNF/
Boolean X transport and without normalizer/pure literals. Use Owl's existing
`SyntacticFragments.FormulaClass.classify`, `ltl-inspect`/`ltl-utilities`, or JShell
with the probe classpath, preserving transport as above; no new classifier.
Separately classify post-Input formulas to explain M0, not replace this inventory.
Record syntax class, restricted support, Boolean Π₂/Σ₂ support, normalization
need, actual rewrites/Owl-only simplification, and unknown transport/parse failures.
NNF expands biconditionals; distributing X avoids false exclusions. Summarize
all 69 and FULL-43. Resolve unknowns before omitting the conditional normalizer;
if needed, schedule it after the first eager experiment.

| Stage | Production lines | Test/harness lines | Closing test |
| --- | ---: | ---: | --- |
| 0. Repair tlsf-tools objective allocation/error propagation, including arena, section assembly, conversion and printing callers. | 150–300 | 120–220 | Deterministic one-shot failures and allocation sweep: no successful text/AST/verdict on failure; healthy objectives independently checked. Prerequisite for every row below. |
| 1. Strengthened complete slice: retain AST; IDs/budgets; OxiDD classes/symbolic derivatives; safety/co-safety plus finite-window GF recurrence and complement; shared one-set Zielonka path; bridge, BFS and minimal opt-in eager arm. | 1,500–2,200 | 400–650 | Restricted breakpoint proof reviewed; `GF(a & X b)`/complement and the validation examples: kernel-checked translation validation, exact `(target,priority)` bridge relation under permuted AP maps, verified controller, and declines after publication and during import. |
| 2. Complete Boolean Π₂/Σ₂ product; completed components; fixed global acceptance/tree; generic maximal-model tree builder and ordinary one-sibling path update. | 1,400–2,200 | 350–600 | Reviewed L(Bχ)=L(χ) proof for the exact variant, including X elision, finite remainders and no support resets (`prove-breakpoint-x-elision`); mixed/shared/complement formulas, empty marks, kernel-checked translation validation and Owl layer checks. No general Π₂ admission before the proof gate. |
| 3. Hardening and first eager admission experiment, immediately after Stage 2: finish accounting/diagnostics and arm plumbing; fault paths and consumer width limits; paired corpus/controller measurements. | 300–600 | 250–450 | All 69 attempted with support/decline/coverage visible; no completed language/verdict mismatch or lost incumbent solve; paired construction/import/split/solve time and memory. Retain opt-in unless owner gates pass. |
| 4. Conditional: one complete Δ₂ normalizer, only if the inventory identifies needed unsupported targets. | 1,000–1,800 | 300–500 | Nested alternation and random LTL: normalization equivalence and composed DPA equivalence; all choices/side conditions included; blowup declines. Repeat admission measurements for the added coverage. |
| 5. Deferred: grouping/pruning, suspension, round robin, local alpha/padding, local trees and stuttering; only reductions justified by measurements. | 1,400–2,400 | 400–700 | Separate reviewed proofs under `prove-component-support-blocking`, `prove-dela-suspension-round-robin` and `prove-zielonka-stutter-and-resets` before enabling affected reductions; full language suite and structural-input count diagnostics. Zero lookahead stays fixed. |

Through Stage 3: 3,350–5,300 production and 1,120–1,920 test/harness lines,
including objective repair. With Stage 4: 4,350–7,100 and 1,420–2,420 respectively.
Deferred work is additional, not an eager-admission prerequisite.

Extend the single-component wrapper's state/edge/label machinery, without a
second shortcut backend. Failed gates need the smallest counterexample.
Proposed experimental ceilings are configurable: 100,000 discovered states,
120 s, and min(existing worker allowance, 8 GiB), sharing construction/import
budgets and accounting BFS/memo/graph. Calibrate BDD/cache/host caps within this
process envelope; do not spend all memory on BDDs. These are proposals, not new
portfolio defaults. Paired performance/coverage gates remain owner decisions;
provisional median ≤1.25/p90 ≤2 count thresholds are not admission requirements.
Keep pure-literal synthesis preprocessing outside this language-preserving API;
any future use must carry fixed outputs into extraction.

## Provenance and inspected SemML pipeline

This design originated with [#78](https://github.com/gaperez64/tlsf-tools/issues/78),
reviewed in October 2026. Owner decisions supersede older route/API descriptions
there and in [acacia-bonsai#340](https://github.com/gaperez64/acacia-bonsai/issues/340).
The external M0 recorded 43/69 full Owl DPAs within 120 s, median 1,883 states,
with most states explored on most completed cases. This does not promise the
plain product completes the same 43; the remaining 26 motivate later lazy arms
whose solvers/soundness are outside this design. Sprint `../PLAN.md`, `../probe/`,
`review-issues/`, and `../../otfpar/semml-only.list` are absent working files;
review drafts became issues #79–#87. They are provenance, not repository links.

The 2026-10-29 source audit used these roots:
`S=/home/gperez/GIT-repos/semml/src/main/java/semml`,
`O=/home/gperez/GIT-repos/semml/src/main/java/owl`,
`T=/home/gperez/GIT-repos/acacia-bonsai/subprojects/tlsf-tools`,
`A=/home/gperez/GIT-repos/acacia-bonsai`.
Basenames below mean `O/translations/ltl2dela/NormalformDELAConstruction.java`,
`O/translations/canonical/DeterministicConstructions.java`, and
`O/automaton/acceptance/transformer/ZielonkaTreeTransformations.java`.

`S/semmlCommands/synthesisCommands/util/SemmlSynthesisRunner.java:60,93` runs
TLSF preparation, `ltl2Dela`, `dela2Dpa`, game construction.
`S/thirdparty/SyfcoWrapper.java:58,33` uses
`-os mealy -ot mealy -m fully -q double -f ltl`, inputs before outputs;
`S/semmlCommands/synthesisCommands/util/TechnicalArgumentPresets.java:29` defaults
`simplify=true`. `S/util/Input.java:77,108` reorders APs within partitions by
unfolded substituted sizes, then calls `OwlUtil.pureLiteralSimplifications`.
`S/smarterOwl/OwlUtil.java:47` distributes X/restricts NNF and repeats polarity/
syntax simplification up to ten times. Single-polarity inputs become false,
outputs true (`O/cinterface/CLabelledFormula.java:226`): synthesis-preserving,
not language-preserving, and outside the API. `OwlUtil.java:82` applies
`SYNTACTIC_FIXPOINT` NNF/propositional/syntactic simplification/pull-up-X until
stable or 100 iterations (`O/ltl/rewriter/SimplifierRepository.java:43`).

`NormalformDELAConstruction.java:97,851` distributes X/removes negations while
retaining useful top biconditionals and Π₂/complement components. Otherwise
it simplifies both non-strict `SE20_SIGMA_2_AND_GF_SIGMA_1` and
`SE20_PI_2_AND_FG_PI_1` (:86), choosing by outer-connective/operand count
(:897), ties to the second. `O/translations/mastertheorem/Normalisation.java:127`
enumerates fixpoint subsets and GF/FG side conditions into DNF; selectors and
U/R/W/M mappings are at :311,395, substitutions in
`O/translations/mastertheorem/Rewriter.java:68`. This Boolean Π₂/complement
normalization can be exponential; it is not LDBA determinization.

`NormalformDELAConstruction.java:175,950` builds complete `SafetyCoSafety`
Buchi with initial-formula suspension disabled but generic blocking active,
shares equal/complementary components, groups weak/unique operands, and identifies
unique GF-co-safety/FG-safety round-robin chains. Components `(all,rejecting)`
carry residual/breakpoint with false suspension (`DeterministicConstructions.java:782`).
Extraction (:746) replaces non-co-safety atoms, elides X, unfolds; stepping
(:682) handles sinks, safety/transient/co-safety suspension, resume, progression,
and finite renewal with remainder intersection (:727), not just true testing.
DELA state is `(stateFormula, sorted component-index → breakpoint map, roundRobinCounters)`
(`NormalformDELAConstruction.java:1094`).

`NormalformDELAConstruction.java:215` jointly traverses component DAG AP decisions,
never valuations. At :445 terminals become constants and unused components vanish.
Transient blocking suspends all; weak blocking substitutes local alpha constants;
round robin suspends other chain members and shares acceptance variables (:481,589).
Buchi marks become colours; global initial skeleton interprets i as Inf(i),
negation Fin(i) (:208). Changed `stateFormula` edges have no colours; others
retain alpha colours and pad outside so global restriction equals alpha (:426,370).

`S/smarterOwl/OwlUtil.java:87` passes `OptionalInt.of(0)`/local alpha; the initial
state consumes lookahead before exploration (`ZielonkaTreeTransformations.java:168`).
Only conditional trees remain, without bounded SCC/ACD/`State.inDifferentSccs`
(the warning is `NormalformDELAConstruction.java:1170`, external
`review-issues/prove-dela-scc-separation.md`). Maximal opposite subsets form
lexicographic shared trees (:772); DPA states are DELA/leaf paths (:851), initially
leftmost (:223). Equal trees use :314: descend on containment, rotate past
non-containing siblings (`stutter=true`), reset child 0 after a full turn,
then descend. Min-even priority is first anchor depth plus root offset 0/1,
retained recursively (:355). Changed trees reset leftmost uncoloured (:234),
using equality rather than SCC predicates. Reserve m+2 priorities (:394);
SemML completion adds a rejecting sink counted by the probe
(`S/smarterOwl/SmarterGameViews.java:50`).

Owl-like counts depend on these preprocessing/reduction/order choices. Defer
second normalizer/selection, simplifier matching, grouping/suspension/local trees,
stuttering, caches/ordering/minimization/game advice until measurements justify
them. Product short-circuiting (`NormalformDELAConstruction.java:309`) only saves
work; redundant-conjunct pruning is disabled at 470 and must stay disabled.
Support shortcuts remain at `DeterministicConstructions.java:723` and
`O/translations/BlockingElements.java:160` (checks 39/80/121, decrease 165)
despite zero lookahead/disabled initial blocking. The baseline omits them.
Separate blocking, suspension/padding, and stuttering/reset proofs must establish
eventual tree stability or another sufficient invariant; a switched-SCC comment
is insufficient. Keep the complete fixed product/ordinary update until reviewed.
