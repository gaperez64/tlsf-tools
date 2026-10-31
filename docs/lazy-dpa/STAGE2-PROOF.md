# Stage 2: conservative breakpoint proof obligation

**The targeted Stage 2 gate is discharged.** For the exact construction below,
§6 proves both component inclusions for `G(q)`, where q is a positive Boolean
combination of finite windows and `F` of finite windows, and for its `F`/`G`
duals. Together with the Boolean-product/Zielonka theorems, this gives the
admitted grammar at the end. The general Π₂ component theorem was subsequently
proved in `GeneralConverse.lean`; Task T adds executable Π₂/Σ₂ component
simulation. The complete general C constructor/enablement gate remains open;
see §10 and `proofs/README.md`.

This extends [STAGE1-PROOF.md](STAGE1-PROOF.md), using its definitions of `b`, `s`,
`c`, NNF dualization, AP_COMBINED classes, frozen unfolding `U`, simultaneous
stepping `Dᵥ`, and extractor `ρ` (§§1–2). Its derivative, finite-witness,
bad-prefix, and finite-window lemmas (§3) are used below. The authoritative rules
are [DESIGN.md §§1–2](DESIGN.md#conservative-component-exact-rules-and-proof-gate);
the gate is its §5, row 2, and [issue #80](https://github.com/gaperez64/tlsf-tools/issues/80).

## 1. Intended fragment

With `b`, `s`, and `c` respectively the finite, safety, and co-safety grammars of
Stage 1 §1, the extension after canonical NNF and Boolean X distribution is:

```text
π ::= c | π ∧ π | π ∨ π | X π | G π | π R π | π W π
σ ::= s | σ ∧ σ | σ ∨ σ | X σ | F σ | σ U σ | σ M σ
φ ::= π | σ | φ ∧ φ | φ ∨ φ
```

Thus `π=Π₂`, `σ=Σ₂`; negation exchanges them by NNF dualization. Arbitrary Boolean
combinations, including implication and equivalence, are expressed by these
dualities and Boolean truth tables. This is a syntactic fragment, tested on
canonical class support, without Δ₂ normalization or a language-equivalence
oracle. Its grammar is the intended Stage 2 scope, **not an admission theorem**.

## 2. Exact component and complement

For `χ∈π`, `Bχ` is a complete deterministic transition-Büchi automaton over
`2^AP`, with set 0 and states `(A,R)` of unfolded classes. `R=false` denotes
suspension. It never denotes a resource failure. The extractor is exactly Stage 1
§2: replace supported non-co-safety modal atoms by true; repeatedly remove
supported X atoms absent from the X-subformula sets of the current supported
non-X modal atoms; unfold; retry on `U(x)` if the result is finite and `x≠U(x)`.
Protection is recomputed after each removal. The surviving non-X protectors are
F/U/M, and their entire syntactic X subformula sets are protected, including
nested X tails and Xs in operands that would absorb if materialized. This
extractor is also used by the default-fragment Lean theorems; see the
[default-effect audit](DEFAULT-PROTECTION.md).

For canonical input class `x`, initialize `(U(x),false)` if `U(x)` is safety or
co-safety, otherwise `(U(x),ρ(x))`. Constants use `(false,false)` and `(true,false)`.
On letter v compute raw `a=Dᵥ(A)`, `r=Dᵥ(R)`, and `a′=U(a)`; use the first row:

| Condition | Target | Mark 0? |
| --- | --- | --- |
| `a′=false` | `(false,false)` | no |
| `a′=true` | `(true,false)` | yes |
| `a′` safety | `(a′,false)` | yes |
| `a′` co-safety | `(a′,false)` | no |
| `U(r)=false` | `(a′,ρ(a))` | no |
| `U(r)` finite | let `q=U(r)∧ρ(a)`; `(a′,q)` if nonfalse, otherwise `(false,false)` | yes iff `q≠false` |
| otherwise | `(a′,U(r))` | no |

In particular, renewal retains a finite nonconstant remainder and extracts from
raw `a`, with the specified retry, rather than unconditionally from `a′`.
Acceptance is `Inf(0)`. For `ψ∈σ`, construct the complete `Bχ` for `χ=bar(ψ)`
and use `Fin(0)` on the identical run. This recognizes the complement of
`L(Bχ)` unconditionally; equality with `L(ψ)` requires the corresponding
component theorem, proved for the targeted family in §6.

All classes use the finite modal-subformula closure and its X tails, so there
are finitely many classes and pairs. Extractor iterations terminate: substitutions
only remove supported variables, and unfolding is idempotent, permitting at most
one retry. The ordered table gives one transition for every letter. Symbolic
Shannon expansion only represents that same function. There are no transient
tests, support resets, external suspension, state replacement, component pruning,
round robin, local acceptance formulas, tree resets, or stuttering updates.

## 3. Component facts that do hold for general Π₂

Write `⇒ₚ` for implication between propositional classes; it implies LTL
implication, but its converse is not assumed. Put `wₙ=w[n:]`, and let `(Aₙ,Rₙ)`
be the state before letter n. For an unfolded class x, its exact successor is
`Δᵥx=U Dᵥx`, by Stage 1 §3. Unfolding and stepping preserve Π₂ and each of the
finite/safety/co-safety classes.

**Extraction and all/rejecting invariant.** For every x,

```text
U(x) ⇒ₚ ρ(x),                  ρ(x) is unfolded and co-safety.       (1)
```

Indeed classes are positive in modal variables. Every true-substitution weakens
the class, and unfolding is a monotone Boolean substitution. Without retry this
gives (1); with retry apply the same argument to `U(x)` and use `U²=U`.
This covers every iteration of X removal, including changed protection sets.
It proves weakening, not equivalence of the extracted obligation with x.

Initially, and at every subsequent active state,

```text
Aₙ ⇒ₚ Rₙ.                                                       (2)
```

Initialization follows from (1). Stepping (2) gives `a′⇒ₚU(r)`; (1) gives
`a′⇒ₚρ(a)`. Thus both ordinary progression and renewal preserve (2).
If `q=false`, these two implications force `a′=false`, so the first row would
already have applied. The explicit false-renewal branch is consequently
unreachable from an invariant state, and in particular cannot reject a
satisfying word. Likewise an active state cannot take the resume row: `U(r)=false`
would already force the first row. Once a safety/co-safety row suspends R,
derivative closure keeps A in that class forever. Hence **resumption is
unreachable in this baseline**. It becomes a real case with external suspension,
which is outside this variant.

It follows that the all-field is always the exact iterated derivative, including
the false sink:

```text
wₙ ⊨ Aₙ  iff  w ⊨ χ.                                           (3)
```

**Satisfying words accept.** Suppose `w⊨χ`. Equations (2)–(3) exclude the false
sink and make every active R true on the corresponding suffix. A safety suffix
therefore marks forever; a co-safety suffix has a finite witness to true and
then marks forever. Otherwise, suppose there are only finitely many marks. After
all of them the component remains active and progresses R by exact derivatives. The co-safety
finite-witness lemma forces a derivative of this satisfied R to true, which
requires another mark. This contradiction proves

```text
L(χ) ⊆ L(Bχ).                                                  (4)
```

This argument covers arbitrarily many deletions and rounds in this direction;
it does not need a cohort interpretation or a support reset.

**Finite remainders and witnesses across rounds.** During an active interval,
ordinary progression takes the exact derivative of R and renewal conjoins a
new seed to that derivative. Consequently, for any earlier active position t,
until suspension,

```text
Rₙ ⇒ₚ Δ_{w[t:n]}Rₜ.                                            (5)
```

This is an induction on transitions using monotonicity; the renewal step is
precisely where retaining `U(r)` proves it. Also (2), (3), and derivative
monotonicity give `Aₙ⇒ₚΔ_{w[t:n]}Rₜ` at every later position, even after
suspension. These statements hold simultaneously for every earlier round,
without choosing independent witnesses or disjuncts.

Suppose an accepting run stays active and t is any active position. There is
a later renewal at position u. At the first such renewal,
`E=Δ_{w[t:u]}Rₜ` is finite. If `wᵤ⊭E`, its exact derivative becomes false after
at most its maximum X depth plus one letters. By (5) and (2), or the all-field
implication just proved, A then becomes false, contradicting acceptance. Thus E
is true on `wᵤ`, and `wₜ⊨Rₜ`. Moreover that finite E becomes propositionally
true after a finite prefix, giving a genuine finite witness for Rₜ. A mark
therefore need not finish a delayed check immediately, but cannot forgive its
failure. This applies to finite nonconstant E, through any number of intervening
renewals; it does not replace E by true at the marked transition.

If an accepting run instead enters permanent suspension, its safety/co-safety
suffix satisfies A: otherwise the safety bad-prefix lemma, or the co-safety
case of Stage 1 §4, would reject. The all-field implication again implies all
earlier R obligations. Thus accepting runs satisfy every seed they actually
extract, including `ρ(a)` at each renewal. This proves consistency for retained
obligations; it does **not** establish that extraction covers every rejecting
obligation of χ.

## 4. Fixed Boolean product

Let `β(z₀,…,zₘ₋₁)` be the fixed Boolean skeleton, where `zᵢ` names a Π₂ formula
`χᵢ` and a Σ₂ occurrence uses the negation of its dual's variable. Share equal
and complementary occurrences. Advance every complete component on every
letter, keeping sinks in the tuple. The product edge has colour set
`Cₙ={i : component i marks on letter n}` and fixed acceptance

```text
α = β(Inf(0),…,Inf(m−1)),       ¬Inf(i) = Fin(i).
```

Put `S={i : i∈Cₙ infinitely often}`. The unique product run satisfies α exactly
when `β(1_{i∈S})` is true, by the definitions of Inf and Fin and the Boolean
truth tables. **If** each component satisfies `L(Bχᵢ)=L(χᵢ)`, these truth values
are exactly `w⊨χᵢ`, proving the product language equals the supplied formula.
This implication is unconditional for components proved in Stage 1 or §6 below.
A one-sided component inclusion is insufficient for general Boolean skeletons,
especially those using complements.

## 5. Global Zielonka tree and parity

This theorem holds for any fixed Boolean α and any colour stream, independently
of the unresolved component theorem. Keep the full universe `K={0,…,m−1}`.
At node label `C⊆K`, children are **all inclusion-maximal** `M⊊C` with
`α(M)≠α(C)`, in a fixed lexicographic order; apply the same rule recursively.
Strict label decrease makes the tree finite with depth at most m. Share equal
subtrees without identifying distinct occurrences of their paths.

**Generic maximal-model builder.** Restrict colours outside C to false and ask
for a model of `α(X)≠α(C)`. From a model X, repeatedly ask for a strict satisfying
superset within C, retaining every element of X, until none exists. This
terminates at a maximal M. Record it, conjoin `∨_{i∈C\M} i` to block all its
subsets, and repeat until unsatisfiable. Previous blocking clauses are upward
closed, so ascent cannot lose a previous clause, and maximality under these
clauses is maximality for the original opposite-acceptance formula. Every
maximal model remains available until recorded: a distinct maximal model cannot
be a subset of an earlier one. Conversely only such models are recorded.
Finiteness proves termination and completeness, including a possible empty
model; at `C=∅` there is no opposite-acceptance model. Single-bit greedy ascent
is not this algorithm and need not find an inclusion-maximal model.

**Ordinary update.** Start at the leftmost leaf, with an empty path when the
root is a leaf. For edge colour set E, take the deepest node v on the current
path with `E⊆label(v)`. Emit `p=depth(v)+ε`, where `ε=0` if `α(K)` is true and
`ε=1` otherwise. If v is a leaf, retain the path; otherwise advance its current
child index by exactly one modulo the number of children and descend leftmost.
Keep the prefix through v. Process E once, without skipping or recursively
processing siblings. This is the design's zero-lookahead global-tree update.

**Recurrent-set proof.** Let d be the minimum anchor depth occurring infinitely
often. After a finite prefix no shallower anchor occurs; hence the path prefix
through a fixed depth-d node v is permanent. Every later E is contained in
`label(v)`, so `S⊆label(v)`.

If v is a leaf, there is no subset of its label of opposite acceptance: any
such subset would extend, by finiteness, to a maximal one and hence a child.
Therefore `α(S)=α(label(v))`.

Otherwise the infinitely many depth-d anchors cycle through every child. No
child label can contain S. For suppose a child D contained S. After the last
occurrence of any colour outside S (there are finitely many colours), every
edge E is contained in D. On the next visit to D the path could never anchor
at v again: updates inside D retain it. This contradicts infinitely many
depth-d anchors. If `α(S)≠α(label(v))`, however, a maximal opposite-acceptance
subset containing S would be a child. Thus again `α(S)=α(label(v))`.

Acceptance alternates at each tree edge, so the depth plus root offset is
even exactly at accepting nodes. The minimum recurring priority is `d+ε`,
which is even exactly when `α(S)` holds. This proves the min-even parity
condition equivalent to the fixed Emerson–Lei condition. Empty edge marks cause
no exception: the empty set is contained in every path label, so anchors at
the current leaf. Constant α gives a root leaf and an empty path, with the
correct constant priority, also when `m=0`.

Finally choose P as the smallest odd integer greater than `m+1` and export
`P−p`, as in DESIGN.md §2. Since `p≤m+1`, every ordinary exported priority is
positive, and

```text
max Inf(P−p) = P − min Inf(p)
```

is odd exactly when that minimum is even. Hence the exported max-odd condition
is equivalent too. Every product transition has a priority; this proof uses
no changing trees, uncoloured reset edges, SCC lookahead, or stuttering.

## 6. Targeted converse: flat eventualities under G

Let `q ::= b | F b | q ∧ q | q ∨ q`, with b a finite window as in Stage 1.
Fix `χ=G(q)`. There is a finite maximum X depth h among its finite bodies;
there is no common bound across inputs. We prove `L(Bχ)⊆L(χ)` without changing
the extractor, retry, renewal, or suspension rules. Components already reduced
to safety/co-safety use Stage 1. Any outer Boolean splitting already performed
by canonicalization uses §4; the argument below treats one remaining G atom.

### 6.1. A failed clause and its exact residual

Write `K=[G(q)]`, and let `Hᵢ=[F bᵢ]` range over the distinct eventuality
atoms of q. Every raw all-field class, before a false sink, has the form

```text
x₀ = K,     xₙ = D_{w[n−1]}Aₙ₋₁ = K ∧ Pₙ,     Aₙ = U(xₙ),
```

where Pₙ contains only H atoms and finite atoms/APs. This follows inductively
from `U(K)=K∧U(q)`: stepping retains K and H, and unwraps only finite X atoms.
In particular `Aₙ⇒ₚU(q)`. K is the only non-co-safety atom, and is independent
of all variables in Pₙ.

Suppose `w⊭G(q)`, and choose t with `wₜ⊭q`. There is a propositional consequence

```text
q ⇒ₚ C = B ∨ ⋁_{i∈I} Hᵢ,
```

where B is a finite disjunction of finite leaves of q, and **every** disjunct
is false on `wₜ`. To obtain it, at a false conjunction select a false operand;
at a false disjunction combine the clauses obtained from both operands. At a
leaf select that leaf. This is one false clause, without performing a CNF
rewrite in the construction. Empty disjunctions mean false. In particular,
for each selected i, `F bᵢ` and bᵢ are false on every suffix at or after t.

Since `Aₜ⇒ₚU(C)`, from position t+1 onward the raw all-field implies the
corresponding raw residual of C. More generally maintain, at a raw position n,

```text
xₙ ⇒ₚ Cₙ = (⋁_{i∈I} Hᵢ) ∨ Eₙ,       wₙ ⊭ Cₙ,                  (6)
```

with Eₙ finite. With I fixed, exact progression is

```text
Cₙ₊₁ = D_{w[n]}U(Cₙ)
      = (⋁_{i∈I} Hᵢ) ∨ D_{w[n]}(Eₙ ∨ ⋁_{i∈I} bᵢ).             (7)
```

Both the implication and falsity persist by monotonicity and the derivative
lemma. Every finite candidate in Eₙ is false on its actual suffix: an initial
candidate comes from the false B, and a later one from a bᵢ that never holds.

### 6.2. Finite depth flushes abandoned candidates

We will occasionally remove an index from I in this **proof constraint**;
the automaton is untouched. When Hᵢ is removed from Cₙ, its already pending
finite candidates remain in Eₙ, but (7) creates no further candidates from bᵢ.
After h+1 further letters those old, false finite candidates are propositionally
false, by the finite-window lemma. The same holds for the initial B.

Consequently, after h+1 letters following initialization or the latest removal,
every supported X atom in Cₙ is an X subformula of a bᵢ with `i∈I`. Indeed (7)
only introduces finite derivatives of these bodies; unwrapping X exposes their
existing X tails. This statement uses exact propositional classes: a consumed
false finite candidate has become false, rather than merely being semantically
false. A finite disjunction cannot introduce a new supported variable.

### 6.3. Losing a protector gives a smaller failed clause

Inspect the first extraction pass on raw xₙ at such a position, whether or not
the transition renews. Substituting true for K gives Pₙ. Since Cₙ contains no K,
(6) implies `Pₙ⇒ₚCₙ` by the same
substitution. Let y be an intermediate class in the actual X-removal loop.
As long as every selected Hᵢ is supported in y, **all X atoms of Cₙ are
protected**. Therefore deleting unprotected X atoms leaves Cₙ unchanged and
preserves `y⇒ₚCₙ`. This applies to each simultaneous deletion, with protection
recomputed exactly as specified in §2.

If a selected Hⱼ is absent from support initially or after a deletion, stop
this inspection at the first such point. Then

```text
y ⇒ₚ Cₙ,     y does not depend on Hⱼ
    imply y ⇒ₚ Cₙ[Hⱼ:=false],
    hence xₙ ⇒ₚ Cₙ[Hⱼ:=false].                                (8)
```

The last implication holds because every extraction substitution so far has
weakened xₙ. Substitution by false in (8) is a proof step justified by support
independence, **not an extractor operation**. Remove j from I and propagate this
new constraint by (7). It is still false on the actual suffix, since Hⱼ was
already false there. Wait h+1 letters before inspecting another extraction, to
flush its remaining finite candidates as in §6.2.

This is the reason repeated elision is tractable here. An H atom may reappear
in the all-field later, but an index removed from this constraint never returns
to I. A loss of protection therefore consumes one of finitely many selected
eventuality loops; it cannot start an unbounded succession of new loops.

### 6.4. Eventually every extracted seed is false

Assume the all-field never reaches false. No xₙ can imply a finite class false
on `wₙ`: unfolding and exact progression would force A to false after that
class's finite horizon. This handles an initially empty I, and shows that (8)
cannot leave I empty.

Starting with (6), inspect positions after the required finite wait. At each
position either (8) strictly decreases I, followed by another finite wait, or
the whole X-removal pass preserves the false constraint Cₙ. There are at most
the original `|I|` decreases, including losses during intermediate iterations.
Thus there is N after the last decrease and its wait such that every extraction
at `n≥N` preserves Cₙ through the entire removal loop.

Let y be the final remainder of that first pass. Then `y⇒ₚCₙ`, so `U(y)` is
false on `wₙ`. Also `Aₙ⇒ₚU(y)`, because extraction only weakened xₙ. If U(y)
were finite, the preceding finite-horizon observation would force a false
all-field later. Thus U(y) is not finite. **The retry condition is false**, and
the actual result, extracted from raw xₙ, is precisely this U(y). We have proved
the previously missing sufficient lemma for this family:

```text
w ⊭ G(q), A never false  ⇒  ∃N ∀n≥N: wₙ ⊭ ρ(xₙ).               (9)
```

No bound on the time of the last decrease is claimed; only the number of
decreases and the h+1 flush time are bounded. Nor is (9) claimed for the
general Π₂ grammar of §1. Arbitrary nested temporal bodies would invalidate
the finite flush used here.

### 6.5. Converse, finite remainders, and duals

Suppose Bχ accepts a word violating χ. It never reaches the false sink. If it
enters safety/co-safety suspension, §3 already proves that an accepting suffix
satisfies A, contradicting the all-field invariant. Otherwise it remains
active. Infinitely many marks then mean infinitely many renewals, and §3
proves that **every** renewed seed `ρ(xₙ)` is satisfied on `wₙ`. Choose a
renewal after N in (9), a contradiction.

This uses §3's preservation of the finite nonconstant remainder in
`q=U(r)∧ρ(xₙ)`: a mark may precede the end of a finite check, but an accepting
run cannot forgive its failure. The failed-clause argument selects no witnesses
or independent disjuncts across rounds. It supplies an eventual false seed on
every sufficiently late renewal, regardless of overlap or support changes.

Together with (4), this proves `L(BG(q))=L(G(q))`. If
`r ::= b | G b | r∧r | r∨r`, its NNF dual is a q of exactly the preceding
grammar, since finite-window duals have the same depth. The complete component
for `G(bar(r))`, with the identical run and acceptance Fin(0), therefore
recognizes `F(r)`. This proves both inclusions for the requested Σ₂ duals too.

## 7. Covered shapes and remaining scope

The theorem covers Boolean combinations of Stage 1 safety/co-safety components,
`G(q)` over finite windows and their flat eventualities, and the dual `F(r)`.

## 8. Admitted grammar

After canonical NNF and Boolean X distribution, with `p∈AP`, the proved grammar
is exactly

```text
lit ::= p | ¬p
b   ::= true | false | lit | b ∧ b | b ∨ b | X b
s   ::= b | s ∧ s | s ∨ s | X s | G s | s R s | s W s
c   ::= b | c ∧ c | c ∨ c | X c | F c | c U c | c M c
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
temporal distribution or a language-equivalence oracle. **Decline any component
outside this guard**, unless canonicalization already places it inside. A
Π₂/Σ₂ tag or finite tests do not prove the general theorem. Proof review and
implementation/bridge validation remain separate gates.

## 9. Exact factoring and current-letter care

These transformations change the representation of the construction, within
the admission decision of §8. `check_admission` first applies the original
canonical-support guard to the original formula: at a nonconstant class x,
accept it if `dpa_admitted(x)`; otherwise require its supported top atom to
be admitted and check both Boolean cofactors. This is exactly the recursion
of the original `dpa_acceptance`, without allocating colours. In particular,
distribution cannot newly admit `G(G a ∧ F b)` or `F(F a ∨ G b)` by exposing
a proved Boolean product. `allow_unproved` uses its original Π₂/Σ₂ guard in
this same check; none of the transformations supplies the missing general
component theorem. Resource exhaustion still declines, without publishing a
partial row. The claims below concern successful construction.

### 9.1. Grouping compatible obligations

At an outer ∧ or ∨, flatten only siblings with that same operator ⋄.
Partition the operands with sound syntax tags into safety S, co-safety C,
finite B, and remaining operands T. Finite operands are collected separately
because they belong to both grammars. Fold C to its canonical Boolean class c,
using ⋄'s identity e (true for ∧, false for ∨) for an empty group. If c ≠ e,
join B to C; otherwise join B to S. This is a class comparison, not a test
that C's operand list is nonempty: a nonempty C can fold to e by Boolean
absorption or a tautology/contradiction. Each grouped
operand has exactly the conjunction/disjunction of its former siblings as
its language: associativity, commutativity, and the identity law prove the
formula equality. Both `s` and `c` are closed under both Boolean operators,
and `b⊆s∩c`, by Stage 1 §1. Thus the new components satisfy the **Stage 1 §4
safety/co-safety theorem**, including both language inclusions. Remaining
components retain their previous proof obligation (Stage 1 §4 or §6 here).
Applying the **fixed Boolean-product theorem (§4)** to these exact component
languages and then **§5's global Zielonka theorem** proves the same language
for the regrouped DPA. Choosing C rather than S for the finite operands is
only a representation choice justified by these closure properties.

Canonical absorption can remove an unsupported syntax operand. The original
guard alone does not justify visiting that operand again. Before constructing
any components, `groupable` therefore descends through **every** ∧/∨ node of
the factored outer syntax, including canonically absorbed branches. At each
non-Boolean leaf it applies `check_admission` to that leaf's canonical class.
This check returns false for unsupported support without changing the context
status or creating colours. If any leaf fails, construction uses the original
`dpa_acceptance(c, original_class)`; no decline is cleared or context retried.
Resource failures retain their original status and do not trigger a retry.

Write A_m for the original canonical-support admission predicate in mode m.
Induction on the canonical Boolean decision DAG shows `check_admission(x)`
computes A_m(x): constants pass, admitted whole classes pass, and otherwise
the supported top atom and both cofactors must pass. A fresh epoch memoizes
shared classes; a false result short-circuits the traversal. Thus the initial
check rejects exactly the original unsupported domain. If it passes but
`groupable` fails, the original acceptance recursion succeeds by that same
induction. If both pass, all canonical acceptance calls on remaining syntax
leaves satisfy A_m; grouped safety/co-safety/finite classes are admitted by
the closure argument above. Every syntax acceptance call is consequently
supported, even when a shared or absorbed subtree is visited by flattening.
Ignoring resource failures, the new constructor therefore succeeds exactly
on A_m. On the proved domain, the component and product theorems cited above
give the original infinite-word language in both paths. In `allow_unproved`
mode this language claim remains conditional on the general component theorem
of §6; preserving admission does not discharge that theorem.

### 9.2. The two temporal distributions

For every infinite word w and position n,

```text
w,n ⊨ G(a ∧ b) ⇔ ∀j≥n: (w,j ⊨ a ∧ w,j ⊨ b)
                ⇔ (∀j≥n: w,j ⊨ a) ∧ (∀j≥n: w,j ⊨ b),
w,n ⊨ F(a ∨ b) ⇔ ∃j≥n: (w,j ⊨ a ∨ w,j ⊨ b)
                ⇔ (∃j≥n: w,j ⊨ a) ∨ (∃j≥n: w,j ⊨ b).
```

Therefore `G(a∧b)=Ga∧Gb` and `F(a∨b)=Fa∨Fb`. Already compatible safety/co-safety
syntax is retained as one monitor; distributing inside it is unnecessary.
Structural congruence permits
replacement inside any NNF syntax context, including frozen modal operands.
Hash-consing/memoization changes no formula. The recursion terminates because
each distribution moves G/F onto strict Boolean subterms; ordinary recursive
calls descend the syntax DAG. These are the **infinite-word semantic identities
used for canonicalization in Stage 1 §1**, with component correctness and the
final parity language supplied by **Stage 1 §4, §6 here, and §§4–5 here**.
The original admission guard is evaluated first, as above.

### 9.3. Terminally decided products

Consider a partial current-letter path through `joint`. A component DAG leaf
fixes its target pair for every completion of that path. If that pair's
all-field is 0 or 1, §2's transition table keeps it forever in `(0,0)` or
`(1,0)`, with respectively no marks or a mark on every edge. Consequently its
`Inf(i)` truth is exactly that constant, independently of the remaining word,
the rejecting field, and the finite prefix of marks. Substitute only these
constants in the fixed acceptance Boolean β of §4. Components whose target
is still a decision, or whose all-field is nonterminal, remain variables.
Complemented occurrences in β keep their Boolean polarity during substitution.

If the result is the Boolean constant t, every infinite continuation has
acceptance truth t. Replace this branch by an absorbing state identified
by the reserved absent tuple and t. Its universal self-loop has priority P
for t=1 and P−1 for t=0, where P is the odd export constant of §5. The
recurring maximum is therefore odd exactly for t=1. The entering priority
and all earlier priorities occur only finitely before this constant suffix
and cannot change acceptance. This proves equality of the residual languages,
using the **fixed Boolean-product theorem (§4)**, the **terminal rows of §2**,
and **§5's max-odd parity characterization**. For an undecided β use the
unchanged tuple and global-tree update. No arbitrary nonterminal component
is dropped and no conditional/local acceptance tree is introduced.

### 9.4. Unfolding under current-AP choices

Let C be a consistent cube of assignments to current AP variables only.
For syntax t the care traversal returns `U(t)|C`; a class traversal returns
a class agreeing with `U(x)` on all valuations satisfying C. Modal variables
retain the independent interpretation of Stage 1 §2. A known current AP is
replaced by its chosen Boolean value; an unknown AP is retained. `[Xf]` and
every displayed continuation in the unfolding equations remain frozen and
are never evaluated under C. Boolean syntax uses the usual homomorphism,
including constant short-circuiting; the modal clauses are exactly Stage 1
§2's equations with their operand unfoldings restricted to C.

Prove the invariant simultaneously by induction on syntax and the class BDD.
At a current AP decision p, traverse the low/high cofactors under `C∧¬p`
and `C∧p`, restore the previous assignment, and recombine with ITE(p,high,low).
Shannon's identity proves agreement with `U(x)` under C. At a modal decision,
the operand induction gives its unfolded decision expression under C, and
the cofactor induction plus ITE proves the same claim. APs precede every
modal variable in the existing order; hence assigned APs cannot occur in a
remaining class cofactor. For a provably finite class U fixes every supported
AP/X atom, so returning that class directly also satisfies the invariant.
At the root C=true, the result is propositionally equal to the original U(x).
The memo key is `(syntax-or-class, owned ID, canonical AP cube)`; different
partial assignments cannot share a result accidentally. Storage and recursion
use the existing host/cancellation budgets; no linear bound is claimed.

This relies on **Stage 1 §2's frozen unfolding definition** and Shannon
expansion. Equality of U leaves the **Stage 1 §3 derivative lemma**, extractor
ρ, §2's ordered transition table, and the **component/product/parity theorems**
unchanged. In particular current care never constrains APs exposed by a future
X step, and introduces zero lookahead.

### 9.5. Fragment bounds with exact fallback

Write T(x) for the original exact support-tag intersection used during
expansion. Maintain cached bit sets `L(x)⊆T(x)⊆H(x)`. Constants have all tags.
For an atom, the sound syntax tags (or already refined exact tags) give L.
The operator's actual tag transfer in `tags_impl` gives H: F/U/M can only
produce `{co-safety,Π₂,Σ₂}`, G/R/W only `{safety,Π₂,Σ₂}`, and AP/X use the
unrestricted set of tags. X's operand is not assumed finite. For a Boolean
class with supported top atom v, intersect the respective bounds of v and
both cofactors. This preserves both inclusions because T uses exactly that
intersection. Soundness of the initial syntax bounds follows by structural
induction on the **grammars of Stage 1 §1 and §1 here** and their operator
transfer rules; Boolean canonicalization can add memberships by removing
support but cannot invalidate those syntax memberships. Cached lower bounds
remain sound if an atom is subsequently refined.

For the original predicate `T(x)∩M≠∅`, return true if `L(x)∩M≠∅`, false if
`H(x)∩M=∅`, and otherwise call the unchanged `dpa_tags` exact computation.
Thus every answer equals the original predicate, including masks containing
both safety and co-safety. The safety test still precedes the co-safety test
in §2. The reduce and finite-retry tests in ρ use the same rule, preserving
every substitution, protected-X computation, and retry. This establishes
identity of the transition rules needed by the **Stage 1 §4 and §6 component
theorems**; conservative tags alone would not establish that identity.

None of §9 uses support blocking (#81), external suspension/round robin (#82),
local-tree/reset/stuttering reductions (#83), `State.inDifferentSccs`, or
lookahead. Undecided products retain §5's original global tree and update.

## 10. Task T executable refinement status

`proofs/TlsfProofs/Dpa/Impl/` now contains core-only executable class equality,
exact support, all five structural tags, syntactic protection, simultaneous
DROP_X, bounded elision, unfolding, retry and the ordered component table.
Simulation theorems reduce its infinite runs to `general_pi2_language`.
NNF dualization respects canonical class equality and maps Σ₂ support to Π₂
support, so the dual run also has the exact Σ₂ language. The fresh oriented
component has both one-set numeric parity languages. Canonical research
admission has the support-union domain and Shannon recursion; the grouping
test uses the folded class's equality with the Boolean identity.

The executable checks include the review-k/l protected remainders and
review-i's identity group, Büchi round/state split, and store/cache branches:
68 checks pass both by kernel reduction and in
`lake exe dpaImplChecks`. The offline dependency audit is
`tools/golden/dpa_impl_audit.lean`; its dependencies are restricted to
`propext`, `Classical.choice`, and `Quot.sound`.

`Impl/Store.lean` also proves the executable component-store invariant:
insertion-order equal-class and cached-dual hits, fresh Π₂/Σ₂ orientation,
and preservation of existing indices, complete streams, and literals. The
stored coordinates agree with the abstract fixed product. Büchi Π₂ calls
return positive literals and do not share cached duals.

`Impl/Assembly.lean` now compiles explicit valid Boolean/Shannon construction
plans, preserving intermediate index bounds and acceptance truth across
store extensions. `assemble_presentation` and its Shannon and grouped
instances give `ProductPresentation` for the returned store and indexed
acceptance. Grouping uses the canonical folded-class identity guard, including
the nonempty identity case. The reference fixes an explicit recursive call
order; selecting the exact plan/order from C's materialized classes and
frozen syntax is still open.

This does not yet provide that C constructor selection, the C
transport and recursive default-tag refinements, a C-ordered tree/export, or
the C↔Lean BFS goldens. Task T2 proves the state-based positive-Boolean Büchi
round encoding in `Impl/Buchi.lean`: the executable Shannon residual/reset
monitor has infinitely many completed rounds iff its positive acceptance
holds on recurrent colours. The incoming-mark state split, one-step delay,
initial mark, and C's 0/1 max-odd priorities preserve that language, including
constant acceptance. This proof does not require colours of a conjunction
to occur simultaneously. Concrete constructor selection and the syntax
bridge remain separate obligations. General admission stays research-only.
The smallest remaining selection/transport lemma and why arbitrary valid
plans and Boolean class equality do not imply it are recorded in
`proofs/README.md`.

VERDICT: done (targeted Stage 2 grammar); Task T enablement remains open
