# Breakpoint components and Boolean-product language proof

The flat component converse below proves `G(q)` for positive Boolean combinations
of finite windows and F-windows, plus F/G duals. Product/Zielonka correctness
gives the restricted grammar in §7. `GeneralConverse.lean` separately proves
general Π₂, and executable Π₂/Σ₂ simulation is documented in
[the proof overview](../../proofs/README.md#automaton-translation-validation).
General GR(1) admission uses bounded translation-validation evidence; no proof
of C correctness on every runtime input is claimed.

Use [Stage 1's classes and derivative/witness lemmas](STAGE1-PROOF.md), including
b/s/c, NNF duality, AP_COMBINED, frozen U, simultaneous Dᵥ, and extractor ρ.

## 1. Intended fragment

Let b/s/c be Stage 1’s finite/safety/co-safety grammars. After canonical NNF
and Boolean X distribution:

```text
π ::= c | π ∧ π | π ∨ π | X π | G π | π R π | π W π
σ ::= s | σ ∧ σ | σ ∨ σ | X σ | F σ | σ U σ | σ M σ
φ ::= π | σ | φ ∧ φ | φ ∨ φ
```

Thus `π=Π₂`, `σ=Σ₂`; negation exchanges them by NNF dualization. Arbitrary Boolean
combinations, including implication and equivalence, are expressed by these
dualities and Boolean truth tables. This is a syntactic fragment, tested on
canonical class support, without Δ₂ normalization or a language-equivalence
oracle. Its grammar is the intended Stage 2 scope, not an admission theorem.

## 2. Exact component and complement

Use [the canonical extractor and ordered component table](DESIGN.md#conservative-component-exact-rules-and-proof-gate).
Bχ for Π₂ χ is complete deterministic transition-Büchi over `2^AP`; states are
unfolded `(A,R)` and false R is suspension, never failure. Syntactic protection
includes nested X tails and absorbed frozen operands and is recomputed after
each elision; it also serves default theorems ([audit](DEFAULT-PROTECTION.md)).
Renewal retains finite nonconstant `U(r)` and extracts from raw a with retry.

Acceptance is Inf(0); for Σ₂ ψ, use χ=bar(ψ) and Fin(0) on the identical run.
Completeness makes this exactly the complement of L(Bχ), while equality to
L(ψ) needs component correctness. Finite modal closure/X tails, decreasing
elision, and idempotent U prove finiteness/termination. Shannon expansion
represents the total ordered function. No transient/support reset, external
suspension, replacement/pruning, round robin, local alpha, tree reset, or
stuttering is used.

## 3. General component invariants

Write `⇒ₚ` for propositional implication (sufficient, not necessary, for LTL
implication), `wₙ=w[n:]`, and `(Aₙ,Rₙ)` for the state before n. Unfolded x
steps to `Δᵥx=U Dᵥx`; U/stepping preserve Π₂ and finite/safety/co-safety.

```text
U(x) ⇒ₚ ρ(x),                  ρ(x) is unfolded and co-safety.       (1)
```

Positivity makes every true-substitution weakening, and U is monotone.
This proves (1) through every protection change; retry applies it to U(x)
using `U²=U`. Extraction is not claimed equivalent to x. Initially/while active:

```text
Aₙ ⇒ₚ Rₙ.                                                       (2)
```

Initialization uses (1). Stepping gives `a′⇒ₚU(r)` and (1) gives `a′⇒ₚρ(a)`,
preserving (2) on progression/renewal. False renewal q would force a′ false,
so the first row already applies; active resume likewise cannot occur.
Safety/co-safety suspension persists by derivative closure. Resumption becomes
a real obligation only with external suspension, outside this baseline.
Thus the all-field remains the exact iterated derivative, including false:

```text
wₙ ⊨ Aₙ  iff  w ⊨ χ.                                           (3)
```

If `w⊨χ`, (2)–(3) exclude false and satisfy every active R. Safety suffixes
mark forever; co-safety reaches true and then marks forever. Otherwise, finitely
many marks would leave satisfied co-safety R progressing by exact derivatives
forever, contradicting its finite witness to true and another mark. Hence:

```text
L(χ) ⊆ L(Bχ).                                                  (4)
```

This handles arbitrary deletions/rounds without cohorts or support resets.
During an active interval, progression differentiates R and renewal conjoins
a seed. Monotonicity and retained `U(r)` give, for every earlier active t:

```text
Rₙ ⇒ₚ Δ_{w[t:n]}Rₜ.                                            (5)
```

Equations (2)–(3) also give `Aₙ⇒ₚΔ_{w[t:n]}Rₜ` even after suspension, for all
earlier rounds simultaneously, without independent witnesses/disjuncts.
On an accepting active run, the first renewal after t makes
`E=Δ_{w[t:u]}Rₜ` finite. If false on `wᵤ`, E differentiates to false within
its X depth plus one letters, forcing A false by (5)/(2), a contradiction.
Thus `wₜ⊨Rₜ`; E eventually becomes propositionally true, witnessing Rₜ.
Marks can precede delayed checks but cannot forgive failure, through arbitrary
renewals with finite nonconstant E. E is not replaced by true at the mark.

An accepting suspended suffix satisfies A by the safety bad-prefix/co-safety
proof, hence also every earlier R. Accepting runs therefore satisfy all
extracted seeds, including renewal `ρ(a)`. This establishes retained-obligation
consistency, not coverage of every rejecting obligation of χ.

## 4. Fixed Boolean product

Fix skeleton `β(z₀,…,zₘ₋₁)` with zᵢ naming Π₂ χᵢ; Σ₂ uses its dual's negated
variable. Share equal/complementary occurrences and advance every complete
component, including sinks, on every letter. Edge colours and acceptance are:

```text
Cₙ={i : component i marks on letter n},
α = β(Inf(0),…,Inf(m−1)),       ¬Inf(i) = Fin(i).
```

For `S={i : i∈Cₙ infinitely often}`, the unique run satisfies α iff
`β(1_{i∈S})`. If every `L(Bχᵢ)=L(χᵢ)`, these are the formula's truth values,
proving product language equality. Stage 1 and §6 supply such components.
One-sided inclusion cannot justify arbitrary skeletons, especially complements.

<a id="global-zielonka-tree-and-parity"></a>

## 5. Global Zielonka tree and parity

For any fixed Boolean α/colour stream, keep `K={0,…,m−1}`. Node C has all
inclusion-maximal `M⊊C` of opposite acceptance as lexicographically ordered
children. Strict label decrease gives finite depth at most m. Share subtrees
without merging distinct path occurrences.

The maximal-model builder restricts outside colours false, finds a model of
`α(X)≠α(C)`, then repeatedly finds strict satisfying supersets inside C until
maximal M. Record M and conjoin `∨_{i∈C\M} i` to block its subsets; repeat.
Blocking clauses are upward closed, so ascent preserves them and remains
maximal for the original opposite-acceptance formula. Distinct maximal models
are not subsets of earlier ones, so all remain available until recorded.
Finiteness proves termination/completeness, including empty models; C=∅ has no
opposite model. Single-bit greedy ascent need not find a maximal model.

Start at the leftmost leaf (empty path for root leaf). For edge colours E,
anchor at the deepest path node v containing E, emit `p=depth(v)+ε` with
accepting-root ε=0/rejecting ε=1. At a leaf retain the path; otherwise keep
the prefix through v, advance exactly one child modulo its count, and descend
leftmost. Process E once, without skipping/reprocessing siblings.

Let d be the minimum infinitely recurring anchor depth. Eventually no shallower
anchors occur, fixing a depth-d node v/path prefix. Later E lies in label(v),
so `S⊆label(v)`. If v is a leaf, an opposite-acceptance subset would extend
to a maximal one and create a child; therefore `α(S)=α(label(v))`.
Otherwise infinitely many depth-d anchors cycle through every child.
No child D contains S: after the last colour outside S, all E would fit D;
the next D visit would remain there and prevent further anchors at v.
If S had opposite acceptance, a maximal opposite subset containing S would
be a child, contradiction. Again `α(S)=α(label(v))`.

Acceptance alternates with depth, so recurring minimum `d+ε` is even iff
α(S). Empty E anchors at the leaf; constant α yields an empty root path and
correct constant priority, including m=0. For smallest odd `P>m+1`, every
ordinary export `P−p` is positive, and

```text
max Inf(P−p) = P − min Inf(p)
```

is odd iff the minimum is even. Every edge gets a priority. No changing tree,
uncoloured reset, SCC lookahead, or stuttering is used.

<a id="flat-converse"></a>

## 6. Flat converse

Let `q ::= b | F b | q ∧ q | q ∨ q` with finite-window b, and `χ=G(q)`.
Finite bodies have maximum X depth h, unbounded across inputs. We prove
`L(Bχ)⊆L(χ)` with unchanged extraction/retry/renewal/suspension. Stage 1 handles
canonical safety/co-safety; §4 handles outer splits. Consider one remaining G.

Put `K=[G(q)]` and `Hᵢ=[F bᵢ]` for distinct eventualities. Before false:

```text
x₀ = K,     xₙ = D_{w[n−1]}Aₙ₋₁ = K ∧ Pₙ,     Aₙ = U(xₙ).
```

Induction from `U(K)=K∧U(q)` gives Pₙ containing only H and finite/AP atoms;
stepping retains K/H and unwraps finite X. Thus `Aₙ⇒ₚU(q)`; K is the only
non-co-safety atom and independent of Pₙ.

If `w⊭G(q)`, choose t violating q. A false conjunction selects a false operand;
a false disjunction combines both operands' clauses; a leaf selects itself.
This yields a propositional consequence, without constructing CNF:

```text
q ⇒ₚ C = B ∨ ⋁_{i∈I} Hᵢ,
```

where finite B and all selected H are false on `wₜ`; empty disjunction is false.
Selected `F bᵢ` and bᵢ are false at every suffix from t. From `Aₜ⇒ₚU(C)`,
raw all-fields from t+1 imply C's residual. Maintain:

```text
xₙ ⇒ₚ Cₙ = (⋁_{i∈I} Hᵢ) ∨ Eₙ,       wₙ ⊭ Cₙ,                  (6)
Cₙ₊₁ = D_{w[n]}U(Cₙ)
      = (⋁_{i∈I} Hᵢ) ∨ D_{w[n]}(Eₙ ∨ ⋁_{i∈I} bᵢ).             (7)
```

Eₙ is finite; monotonicity/derivatives preserve implication/falsity. Its initial
candidates come from false B, later ones from never-satisfied bᵢ.

Removing i from this proof constraint leaves its pending candidates in Eₙ,
but (7) introduces no more from bᵢ. Within h+1 letters old false candidates
and initial B become propositionally false. After initialization/latest removal
plus h+1 steps, every supported X in Cₙ is therefore a syntactic tail of a
remaining bᵢ. Exact finite derivatives and finite-disjunction support establish
this syntactically, not just semantically. The automaton itself is unchanged.

At such n, inspect extraction on raw xₙ. Substituting true for K gives Pₙ,
still implying Cₙ since Cₙ has no K. While every selected Hᵢ stays supported
in intermediate y, all Cₙ X atoms are protected, so simultaneous elision with
recomputed protection preserves `y⇒ₚCₙ`. At the first missing Hⱼ:

```text
y ⇒ₚ Cₙ,     y does not depend on Hⱼ
    imply y ⇒ₚ Cₙ[Hⱼ:=false],
    hence xₙ ⇒ₚ Cₙ[Hⱼ:=false].                                (8)
```

The last implication uses extraction weakening. False-substitution is a
support-independence proof step, never an extractor operation. Remove j from I,
propagate (7), and wait h+1 steps to flush its candidates. Falsity persists.
H may later reappear in the all-field, but removed indices never rejoin I;
protection losses consume finitely many loops.

Assume A never becomes false. No raw xₙ can imply a finite class false on wₙ,
since exact progression would force false within its horizon. This handles
initially empty I and prevents (8) from exhausting I. Inspection after each
finite wait either decreases I or preserves Cₙ throughout elision. At most
original |I| decreases occur, including intermediate losses, so beyond some N
all extraction passes preserve Cₙ. Their final y implies Cₙ; U(y) is false on
wₙ and `Aₙ⇒ₚU(y)`. Finite U(y) would force A false; thus retry is disabled,
and actual raw extraction returns this U(y):

```text
w ⊭ G(q), A never false  ⇒  ∃N ∀n≥N: wₙ ⊭ ρ(xₙ).               (9)
```

Only the number of decreases and h+1 flush are bounded, not their last time.
General nested Π₂ bodies invalidate finite flushing; (9) is not claimed there.

An accepting violating run cannot enter false or permanent suspension, whose
accepted A suffix would contradict (3). It therefore renews infinitely often.
Every seed is satisfied by §3, contradicting (9) at a renewal after N.
Retaining finite `U(r)` in `q=U(r)∧ρ(xₙ)` prevents delayed failed checks from
being forgiven. No independent round witnesses/disjuncts were chosen; overlap
or support changes cannot avoid late false seeds. With (4),
`L(BG(q))=L(G(q))`. For `r ::= b | G b | r∧r | r∨r`, bar(r) is q with the
same finite depths; the complete G(bar(r)) run with Fin(0) recognizes F(r),
proving both dual inclusions.

<a id="admitted-grammar"></a>

## 7. Admitted grammar

After canonical NNF and Boolean X distribution, using the b/s/c grammars from Stage 1, the proved extension is

```text
q   ::= b | F b | q ∧ q | q ∨ q
r   ::= b | G b | r ∧ r | r ∨ r
k   ::= s | c | G q | F r
φ   ::= k | φ ∧ φ | φ ∨ φ
```

Negation and other Boolean operations use NNF duality; the grammar is closed
under that duality. GF/FG finite-window components are included as special
cases. In q/r, X occurs only inside finite b: no nested unbounded temporal
body, X of an unbounded body, or U/M/R/W extension is inferred. Membership uses
the canonical syntax/support and outer Boolean skeleton, without additional
temporal distribution or a language-equivalence oracle. Under this restricted policy, decline
components outside the guard unless canonicalization places them inside. A
Π₂/Σ₂ tag or finite tests do not prove the general theorem. Proof review and
implementation/bridge validation remain separate gates.

## 8. Exact factoring and current-letter care

These changes preserve §7 admission. At nonconstant class x, `check_admission`
accepts `dpa_admitted(x)`, otherwise requires the supported top atom and both
cofactors admitted. This is original `dpa_acceptance` recursion without colours;
it runs on the original formula before factoring. Distribution cannot newly
admit `G(G a ∧ F b)` or `F(F a ∨ G b)`. `allow_unproved` retains its Π₂/Σ₂
guard. Successful transformations do not supply missing component theorems;
resource exhaustion declines without publishing partial rows.

### Grouping compatible obligations

Flatten siblings of the same outer ∧/∨ operator ⋄. Sound syntax tags partition
safety S, co-safety C, finite B (in both), and remaining T. Fold C to canonical c,
using identity e (true for ∧, false for ∨). If `c≠e`, join B to C; otherwise
join it to S. Compare classes, not list emptiness: nonempty C can absorb to e.
Associativity/commutativity/identity preserve grouped languages, and closure of
s/c under both Booleans plus `b⊆s∩c` makes Stage 1's component proof apply.
T keeps its component proof; §§4–5 compose the same product/parity language.
Joining finite terms to C rather than S is only a representation choice.

Canonical absorption may hide unsupported syntax. Before creating components,
`groupable` visits every ∧/∨ node of factored syntax, including absorbed branches,
and checks every non-Boolean leaf's canonical class. Unsupported support returns
false without context-status changes/colours. Failure uses original
`dpa_acceptance(c, original_class)`; resource failures retain status without retry.

Let A_m be original canonical-support admission. Induction on the decision DAG
shows `check_admission(x)=A_m(x)`: constants/whole admitted classes pass,
otherwise top atom and both cofactors must pass. A fresh epoch memoizes shared
classes with false short-circuiting. If admission passes but grouping fails,
the same induction establishes original acceptance success. If both pass, every
remaining leaf satisfies A_m and grouped s/c/b classes pass by closure, even
for shared/absorbed syntax. Ignoring resource failures, success is exactly A_m.
On proved components both paths preserve language; general mode needs
`GeneralConverse.lean`, not admission preservation alone.

### Temporal distributions

For every infinite w at n:

```text
w,n ⊨ G(a ∧ b) ⇔ ∀j≥n: (w,j ⊨ a ∧ w,j ⊨ b)
                ⇔ (∀j≥n: w,j ⊨ a) ∧ (∀j≥n: w,j ⊨ b),
w,n ⊨ F(a ∨ b) ⇔ ∃j≥n: (w,j ⊨ a ∨ w,j ⊨ b)
                ⇔ (∃j≥n: w,j ⊨ a) ∨ (∃j≥n: w,j ⊨ b).
```

Thus `G(a∧b)=Ga∧Gb`, `F(a∨b)=Fa∨Fb`; compatible safety/co-safety stays one
monitor. Structural congruence permits replacements in NNF contexts, including
frozen operands. Hash-consing/memoization preserve formulas.
`Impl/Factoring.lean` assigns leaf weight 1, unary twice its operand, binary
operand sum plus 1. Smart construction respects bounds; distribution strictly
decreases weight. Fuel also covers factored/new children; ordinary size need
not decrease. Original admission precedes these identities, with component/
product/parity theorems supplying language correctness.

### Terminal products

On a partial current-letter `joint` path, component leaves fix targets for all
completions. An all-field 0/1 stays `(0,0)`/`(1,0)` forever, never/always marking;
its Inf(i) is that constant independently of prefix/rejecting field/future word.
Substitute only such constants into fixed β, preserving complement polarity;
unresolved decisions/nonterminal all-fields remain variables.

Constant result t accepts every continuation exactly when t. Replace it with
an absorbing reserved-absent-tuple state and true loop priority P if t=1,
P−1 otherwise. Odd P gives exactly t; entering/prefix priorities occur finitely.
Terminal/product/parity rules establish residual equality. Undecided β keeps
its tuple/global tree. No arbitrary nonterminal or local tree is removed/introduced.

### Current-AP unfolding

For consistent current-AP cube C, care traversal returns `U(t)|C` for syntax,
or a class agreeing with U(x) under C. Modal variables remain independent.
Known APs become chosen constants, unknown APs remain; `[Xf]` and all unfolded
continuations stay frozen. Boolean homomorphism/short-circuiting and modal
operand unfoldings use the Stage 1 equations restricted to C.

Simultaneous syntax/BDD induction proves agreement. At AP p, traverse low/high
under `C∧¬p`/`C∧p`, restore assignment, and use ITE(p,high,low); Shannon identity
proves equality. Modal decisions combine operand/cofactor inductions with ITE.
APs precede modal variables, so assigned APs cannot remain in class cofactors.
Finite classes contain only fixed AP/X atoms, so returning them directly is exact.
At root C=true the result equals original U(x). Memo keys include
`(syntax-or-class, owned ID, canonical AP cube)` to distinguish assignments.
Host/cancel budgets apply; no linear bound is claimed. U equality preserves
derivatives/extraction/transitions/languages. Future-X APs are never constrained;
there is zero lookahead.

### Fragment bounds and exact fallback

For original support-tag intersection T(x), cache `L(x)⊆T(x)⊆H(x)`.
Constants have all tags; atoms' sound syntax/refined exact tags give L.
`tags_impl` gives H: F/U/M can only yield `{co-safety,Π₂,Σ₂}`, G/R/W
`{safety,Π₂,Σ₂}`, AP/X unrestricted (X operands need not be finite).
For supported Boolean top v, intersect v/both-cofactor bounds, matching T's
exact intersection. Grammar/operator induction proves syntax lower bounds;
canonicalization can add memberships by removing support without losing old
ones. Later atom refinement preserves cached lower-bound soundness.

Answer `T(x)∩M≠∅` true if `L(x)∩M≠∅`, false if `H(x)∩M=∅`, otherwise use
unchanged exact `dpa_tags`. Every answer matches the original, including mixed
safety/co-safety masks; safety keeps precedence. Reduce/finite-retry in ρ
use the same rule, preserving substitutions/protection/retry and hence exact
transitions for component theorems. Conservative tags alone would not suffice.

No factoring change uses support blocking (#81), suspension/round robin (#82), local
trees/resets/stuttering (#83), `State.inDifferentSccs`, or lookahead. Undecided
products keep the original global tree/update.

## 9. Executable reference and validation

The core-only `proofs/TlsfProofs/Dpa/Impl/` implements class equality/support/tags,
syntactic protection, simultaneous DROP_X, elision/unfold/retry, full progression,
pure factoring, fresh-coordinate assembly, and Zielonka export.
`uncached_construction_language` composes their languages. Positive Buchi rounds
require `positiveb`. `Normalize.lean` covers Boolean simplification below
modalities, including frozen absorption, without C caches/traces/call order.

The canonical [validation guide](../../proofs/README.md#automaton-translation-validation)
documents `Validation/Finite.lean` and `Validation/Equivalence.lean`,
`exportParity_language`, `exportBuchi_language`, `check_language`,
`checkBuchi_sound`, checked alphabet compaction, `Buchi.toParity_language`,
and `validate_parity_sound`/`validate_buchi_sound`. It also gives offline
regeneration, exact hash gates, full results, and the 17-second shared deadline.
Finite-export exhaustion fails validation; no fixed limit is proved sufficient.
Nonpositive round skeletons compare via proved parity embedding; positivity is
sufficient for the selected round construction, not necessary for Buchi language.

Decoding, C memory safety, BDDs, and hashes remain trusted. Validation covers only
enumerated formulas/AP orders/policies/acceptance kinds. Other runtime formulas
rely on the proved reference plus sample, not a C proof; bounded lasso goldens
alone do not prove language equality.
