# Stage 1: restricted language-correctness proof

This discharges the restricted component proof gate in [DESIGN.md §1](DESIGN.md#conservative-component-exact-rules-and-proof-gate).
It proves the construction below, including its complement, on every infinite word.
It does not discharge the general Π₂ claim in [#80](https://github.com/gaperez64/tlsf-tools/issues/80)
or certify the implementation, bridge, or Stage 0; their separate release gates remain.

## 1. Exact fragment

Let AP be a finite set, `lit ::= p | ¬p` for `p ∈ AP`. After NNF and distribution
of X through Boolean operators, the admitted fragment is:

```text
b ::= true | false | lit | b ∧ b | b ∨ b | X b
s ::= b | s ∧ s | s ∨ s | X s | G s | s R s | s W s
c ::= b | c ∧ c | c ∨ c | X c | F c | c U c | c M c
φ ::= s | c | G F b | F G b
```

Here `s`, `c`, and `b` are syntactic safety, co-safety, and finite-window
formulas. Each `b` has a finite maximum X depth `h`; its truth at position n
depends only on positions n through n+h. There is no bound common to all inputs.
The dual `bar(b)` swaps constants, literal polarities, and ∧/∨, and commutes with X.
Thus `FG b = ¬GF bar(b)`. General duality also exchanges F/G, U/R, and M/W.
U is strong until, W weak until, R weak release, and M strong release:
`f M g = g U (f ∧ g)` and `f R g = g W (f ∧ g)`.

NNF uses these dualities and the Boolean truth tables, including expansion of
implication and equivalence; X distribution uses `X(f ⋄ g) = Xf ⋄ Xg`.
These identities follow directly from infinite-word semantics. Fold temporal
constants (`X true = F true = G true = true`, and likewise false).
Membership is checked on the resulting canonical classes: Boolean identities
may remove unsupported operands. No other semantic membership oracle is assumed.
In particular, this grammar admits no general Boolean product containing GF/FG
components and no unbounded temporal operator inside `b`.

## 2. Exact automaton

**Classes and derivatives.** Abstract each distinct modal formula as an independent
Boolean variable, with APs and their Boolean negations sharing AP variables.
Equality is propositional equality in this abstraction. A modal formula and its
NNF dual are separate variables; class negation must use NNF dualization, not
Boolean complementation of modal variables. Supported atoms below mean the
variables on which the class actually depends, without descending into them.
All represented NNF functions are positive in modal variables.

Write `[t]` for a frozen modal atom. Unfolding U is Boolean-homomorphic, fixes
APs/constants and `[Xf]`, and uses:

```text
U(Ff)     = U(f) ∨ [Ff]          U(Gf)     = U(f) ∧ [Gf]
U(f U g)  = U(g) ∨ (U(f) ∧ [f U g])       (same equation for W)
U(f R g)  = U(g) ∧ (U(f) ∨ [f R g])       (same equation for M)
```

The displayed continuations are frozen during that substitution. U is idempotent
as a propositional class: substituting these equations twice gives the same
class by absorption. Dᵥ evaluates current APs under letter `v ⊆ AP`, substitutes
`f` for `[Xf]`, and retains every other frozen modal atom; substitution is
simultaneous, so newly exposed APs are not evaluated. Set `Δᵥ = U Dᵥ U`.
In particular, X does not expose its operand to the current letter.

A class is finite/safety/co-safety iff every supported atom belongs respectively
to `b`/`s`/`c` above. Constants satisfy all three tests. This is the direct
syntactic test, without graph or support-change heuristics.

**Extractor ρ.** On class x, replace each supported non-co-safety modal atom by
true. On the resulting class y, repeatedly collect all X subformulas inside
supported non-X modal atoms, using their frozen syntax even inside operands
that would be propositionally absorbed if materialized. Replace supported X
atoms outside that protected set by true, until unchanged. Compute `z = U(y)`.
If z is finite and `x ≠ U(x)`,
retry the entire extraction on `U(x)`; otherwise return z. Idempotence of U
makes a second retry impossible. Protection is recomputed from the reduced
support on every iteration. Each changing iteration removes a supported X
variable, so the loop also terminates.

**Breakpoint component Bχ.** Its alphabet is `2^AP`, its reachable states are
pairs `(A,R)` of unfolded classes, and `R=false` is the suspension sentinel.
For χ in `s`, `c`, or `GF b`, initialize

```text
(U(χ), false)    if U(χ) is safety or co-safety;
(U(χ), ρ(χ))    otherwise.
```

Constants use `(false,false)` and `(true,false)`. For each letter v, compute
`a=Dᵥ(A)`, `r=Dᵥ(R)`, `a′=U(a)`, and apply the first applicable row:

| Condition | Target | Mark 0? |
| --- | --- | --- |
| `a′=false` | `(false,false)` | no |
| `a′=true` | `(true,false)` | yes |
| `a′` safety | `(a′,false)` | yes |
| `a′` co-safety | `(a′,false)` | no |
| `U(r)=false` | `(a′,ρ(a))` | no |
| `U(r)` finite | set `q=U(r) ∧ ρ(a)`; target `(a′,q)` if `q≠false`, else `(false,false)` | yes iff `q≠false` |
| otherwise | `(a′,U(r))` | no |

Acceptance is `Inf(0)`: infinitely many marked transitions. For input `FG b`,
construct Bχ for `χ=GF bar(b)` and use `Fin(0)` on the same complete run.
Handle inputs already classified as safety/co-safety directly, including constants.
No transient blocking, support reset, external suspension, pruning, round robin,
or changing acceptance formula/tree is used.

This is a finite deterministic complete automaton: all classes use the finite
closure of input modal subformulas and their X tails; there are finitely many
Boolean functions over that closure. The ordered table defines one successor
and mark for every letter. A symbolic implementation Shannon-splits current APs
and merges equal `(target,mark)` leaves; the disjoint guards cover all letters
and implement exactly this function. No alphabet enumeration is needed.

## 3. Derivative and finite-witness lemmas

Give classes their LTL interpretation by replacing each modal variable with its
formula. Propositional equality implies equal LTL languages. The usual semantic
equations, with an explicit next on the continuation, are for example
`Ff = f ∨ X Ff`, `Gf = f ∧ X Gf`, and
`f U g = g ∨ (f ∧ X(f U g))`; W uses the same equation and R/M its conjunctive dual.
Together with the Boolean and X clauses, these equations prove by structural
induction, for every suffix z,

```text
v z ⊨ x  iff  z ⊨ Δᵥ(x).                         (1)
```

Indeed DᵥU performs precisely those one-step equations; the final U preserves
their LTL interpretation. Thus for an unfolded x its next residual is `U Dᵥ x`.
Induction on prefix length gives the corresponding iterated derivative identity.
The displayed clauses also show that unfolding and derivatives preserve each
of the three syntactic classes.

If `z ⊨ c`, some finite prefix derivative of c is propositionally true.
Here is a structural proof, including why the conclusion is propositional:
true needs zero letters, false has no satisfying word, and literals need one
letter. Boolean conjunction takes the maximum of its two
witness lengths, disjunction a satisfied operand's length, and X adds one.
For F choose a satisfying position of its operand. For `f U g` choose its finite
witness position j, finite witnesses for g at j, and for f at every earlier
position. For `f M g` choose j with f true there and g true through j inclusive,
and take those finitely many operand witnesses. Take the maximum of their end
positions. Repeated unfolding contains the corresponding sufficient Boolean
branch; every factor in it has become true by the operand induction, so the
whole derivative is propositionally true. True remains true, justifying each
maximum. This proves the claim for every grammar clause.

Dually, if `z ⊭ s`, a finite prefix derivative of s is propositionally false.
Apply the preceding proof to its NNF dual. Dualization commutes with unfolding
and stepping and exchanges true/false; on modal classes it also renames each
modal variable to its dual, as specified above. This follows clause by clause
from the displayed equations, so does not assume modal variables are Boolean
complements. Finally, a finite class becomes its actual truth constant after at
most `h+1` letters: each step decreases all remaining X depths and then evaluates
all exposed APs. These arguments also apply to classes passing the support tests:
a positive Boolean function of atoms from a grammar has a representative in it.

## 4. Component correctness, both directions

**Safety.** Every residual stays safety and R stays suspended. By (1), a
satisfying word never reaches false, so every edge marks. A violating word
reaches false by the bad-prefix lemma and then never marks. Hence
`L(Bs)=L(s)`.

**Co-safety.** A satisfying word reaches true by the finite-witness lemma and
then marks forever. On a violating word true is unreachable. Before a safety
residual is reached there are no marks. If one is reached, it is both safety
and co-safety, hence finite: every supported modal atom belongs to both grammars,
whose intersection is the finite grammar. It therefore reaches false after
finitely many further letters. Thus a violating word has only finitely many
marks, and `L(Bc)=L(c)`. This also handles the precedence of the safety row for
finite co-safety residuals.

**GF finite-window.** Fix a finite class `b ∉ {false,true}` and write

```text
H = [F b],   K = [G F b],   S = H ∨ b,   A* = K ∧ S.
```

Constant b was already folded and handled above. H and K are independent modal
variables, distinct from every atom in b. `U(K)=A*`. On letter v put `e=Dᵥ(b)`;
it is a finite class. Direct calculation gives

```text
a = Dᵥ(A*) = K ∧ (H ∨ e),
U(a) = K ∧ (H ∨ b) ∧ (H ∨ b ∨ e) = A*.          (2)
```

Consequently A never changes and is neither safety nor co-safety. Extracting
from K first gives true and retries on A*, giving `ρ(K)=S`. Extracting from raw
a deletes K and gives `H ∨ e`, unless e already makes it true. Every X atom
remaining in e is an X subformula of b, since a finite temporal step only exposes
children of existing X atoms. H therefore protects all those X atoms. No
unprotected X obligation is deleted. Unfolding gives `S ∨ e`. If this is finite
it must be true (otherwise it still depends on H); the retry returns S. More
explicitly,

```text
ρ(a) = S                 if b ∨ e = true,
       S ∨ e             otherwise.             (3)
```

In the first case a differs from A*: equality would imply `e=b` by assigning
independently to H and K, contradicting `b ∨ e=true` and nonconstant b.
Thus the required retry really occurs. These calculations also cover finite
classes that are semantically constant without being propositionally constant.

Every active R has the form `H ∨ E` for a finite class E. This holds initially
and after renewal by (3); on an unmarked step its unfolded derivative is
`H ∨ b ∨ Dᵥ(E)`. Therefore it can never be false, and when finite it is exactly
true. The suspension/resumption row and the false-renewal target are unreachable.
The renewal is exactly `(A*,ρ(a))`, with a mark. In particular, **a finite
nonconstant remainder is unreachable in this restricted GF construction**;
this does not justify dropping that remainder in the general table. Also
`A* ⇒ S ⇒ R` propositionally throughout the run. Thus the all-field derivative
invariant (1) is never interrupted by a breakpoint-induced false sink.

Call initialization and the state immediately after each marked edge round
starts, at positions t. The initial seed is S. By (3), every later seed is
either S or `S ∨ D_{w[t−1]}(b)`. Between round starts, every unmarked transition
updates R by its exact derivative. These statements specify all round behavior;
in particular a renewal forgets all witness starts before t−1.

Suppose `w ⊨ GF b`. At every round start t, its suffix satisfies H, hence the
seed R. If that round never ended, R would evolve only by exact derivatives.
R is co-safety, so its finite-witness lemma would force a derivative to true,
which the transition table marks, a contradiction. Every round therefore ends,
and induction gives infinitely many marks. Hence `L(GF b) ⊆ L(BGFb)`.

Conversely suppose there are infinitely many marks. Each completed round starting
at t reaches `U(r)=true`. Exact derivatives within the round and (1) imply
`w[t:] ⊨ R_t`. For the initial seed this implies a b occurrence starting at
some `j≥t`. For a later seed, either H holds, again giving such j, or
`w[t:] ⊨ D_{w[t−1]}(b)`, which by (1), since b is already unfolded, gives
`w[t−1:] ⊨ b`. Thus **each completed round guarantees a b occurrence with
start `j≥t−1`**. The infinitely many round starts are strictly increasing.
Their lower bounds are unbounded, so the occurrence starts are unbounded:
`w ⊨ GF b`. This proves `L(BGFb) ⊆ L(GF b)`.

No separation of witnesses is assumed. A retained derivative in (3) carries
the possible witness starting on the preceding letter, including its entire
remaining X delay. A new H searches all later starts. The unbounded-start
argument prevents infinitely many renewals from reusing finitely many witnesses;
the finite-witness argument prevents overlap or delay from stopping a satisfying
run. This proves the required repeated-renewal property without a cohort or SCC
assumption.

We have proved `L(Bχ)=L(χ)` for every admitted positive component. Since its run
is unique and complete, exactly one of Inf(0) and Fin(0) holds. Complementing
acceptance therefore gives `L(Bχ,Fin(0)) = L(¬χ)`, in particular the specified
FG fragment, on every word.

## 5. The one-set Zielonka path and priorities

Keep the global colour universe `{0}`. For Inf(0) its Zielonka tree has accepting
root `{0}` and rejecting child `∅`; for Fin(0) the same two labels have opposite
acceptance. In both cases the only leaf path is `[0]`, initially and forever.
Use the ordinary update: find the deepest node on the path containing the edge's
colour set, emit its depth plus 0 for an accepting root or 1 for a rejecting root,
then advance one child cyclically and descend leftmost. There is only one child.
Thus marked edges anchor at depth 0 and unmarked edges at depth 1, including
empty colour sets. The DPA state is `(A,R,[0])`.

The design exports max-odd priorities using `P−p`, with `P=3` for one colour:

| Component acceptance | Marked: min-even p / max-odd export | Unmarked: p / export |
| --- | --- | --- |
| Inf(0) | 0 / 3 | 1 / 2 |
| Fin(0) | 1 / 2 | 2 / 1 |

For Inf(0), infinitely many marks make the recurring maximum 3 (odd);
finitely many make it 2 (even). For Fin(0), infinitely many marks make it 2
(even); finitely many make it 1 (odd). This proves both parity orientations
directly, including true/false sinks and streams with no marks. Equivalently,
`max Inf(3−p) = 3−min Inf(p)`, whose parity is odd exactly when the minimum is
even. Every edge has a priority; there are no tree-reset edges or missing letters.

## 6. Discharged restriction and remaining obligations

The general [#80](https://github.com/gaperez64/tlsf-tools/issues/80) obligations
are replaced here by explicit facts: safety/co-safety have finite bad/good
certificates; (2) fixes the GF all-field; H protects every relevant X tail;
(3) proves the retry and seed behavior; finite remainders are only true;
and round starts give the two language inclusions. Suspension is permanent in
safety/co-safety and absent in nontrivial GF. None of these facts establishes
the general Π₂ cohort correspondence, repeated unprotected-X deletion, finite
nonconstant renewal, or general suspension/resumption lemma.

Those general lemmas remain unproved here. **Stage 1 must decline formulas
outside §1**, including a non-finite body such as `G(a → F(Xb ∧ XXc))` and
general Boolean products of recurrence components, unless canonicalization
puts the entire formula in the proved fragment. It must not infer admission
from a Π₂ tag, tests, or support changes. Support blocking/resets
([#81](https://github.com/gaperez64/tlsf-tools/issues/81)), DELA suspension/round
robin/padding ([#82](https://github.com/gaperez64/tlsf-tools/issues/82)), and
stuttering/local-tree resets ([#83](https://github.com/gaperez64/tlsf-tools/issues/83))
are unused and remain outside this theorem.

All semantic lemmas used here were proved above; no external automata theorem is
assumed. For the exact reference algorithms, see the inspected Owl checkout,
`src/main/java/owl/ltl/SyntacticFragments.java:42–95` (support tests) and
`src/main/java/owl/translations/canonical/DeterministicConstructions.java:682–779`
(breakpoint/extractor). The authoritative transition variant and ordinary
Zielonka update are [DESIGN.md §§1–2](DESIGN.md), rather than Owl's additional
optimizations. There is no unproved mathematical case within the stated grammar;
proof review and the implementation/bridge checks remain Stage 1 closing gates.

VERDICT: done
