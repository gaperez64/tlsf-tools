# Restricted component language proof

The construction below recognizes its input and complement on every infinite
word. It discharges the restricted component gate in [the design](DESIGN.md#conservative-component-exact-rules-and-proof-gate),
not implementation, bridge, or objective-assembly validation. The general Π₂
proof is separate; see [the proof overview](../../proofs/README.md#automaton-translation-validation).

## Fragment and classes

For finite AP, after NNF and Boolean X distribution:

```text
lit ::= p | ¬p, p ∈ AP
b ::= true | false | lit | b ∧ b | b ∨ b | X b
s ::= b | s ∧ s | s ∨ s | X s | G s | s R s | s W s
c ::= b | c ∧ c | c ∨ c | X c | F c | c U c | c M c
φ ::= s | c | G F b | F G b
```

Finite-window b has some maximum X depth h and reads n through n+h; no bound
is common to inputs. NNF dualization swaps constants, literals, ∧/∨, F/G,
U/R, and M/W, commuting with X; `FG b = ¬GF bar(b)`.
U/M are strong until/release, W/R weak: `f M g = g U (f ∧ g)` and
`f R g = g W (f ∧ g)`. Boolean truth tables expand implication/equivalence;
`X(f ⋄ g) = Xf ⋄ Xg` distributes X, and temporal constants fold
(`X true = F true = G true = true`, likewise false). Infinite semantics
justify these identities. Membership uses canonical class support, where
Boolean identities can remove unsupported operands, without a semantic oracle.
No general GF/FG Boolean product or unbounded operator inside b is admitted here.

Classes abstract each modal formula, including its NNF dual, as an independent
Boolean variable. AP negation shares its AP variable; modal negation uses NNF
dualization, never Boolean complementation. Equality is propositional; support
does not descend inside atoms. NNF functions are positive in modal variables.
For frozen `[t]`, Boolean-homomorphic unfolding fixes AP/constants/X and uses:

```text
U(Ff)     = U(f) ∨ [Ff]          U(Gf)     = U(f) ∧ [Gf]
U(f U g)  = U(g) ∨ (U(f) ∧ [f U g])       (same for W)
U(f R g)  = U(g) ∧ (U(f) ∨ [f R g])       (same for M)
```

Continuations stay frozen during substitution; absorption proves `U²=U`.
Simultaneous `Dᵥ` evaluates current APs, replaces `[Xf]` by f, and retains other
modal atoms; newly exposed APs are not evaluated. Write `Δᵥ = U Dᵥ U`.
Finite/safety/co-safety tests require every supported atom to belong to b/s/c;
constants pass all. There are no graph/support-change heuristics.

Use exactly [the canonical extractor and ordered component table](DESIGN.md#conservative-component-exact-rules-and-proof-gate).
Call the extractor ρ and component Bχ. The alphabet is `2^AP`; states `(A,R)`
are unfolded classes with false R as suspension. Acceptance is Inf(0) for
safety, co-safety, and GF b; FG b uses the identical complete run for GF bar(b)
with Fin(0). Safety/co-safety/constants take their direct classification.
No transient/support reset, external suspension, pruning, round robin, or
changing tree/acceptance is used. Finite modal closure plus X tails gives
finitely many Boolean classes/pairs. The ordered table is total/deterministic;
Shannon splitting and equal `(target,mark)` merging represent it with complete,
disjoint guards, without enumerating the alphabet.

## Derivatives and finite witnesses

Interpret modal variables by their LTL formulas; propositional equality then
preserves language. Structural induction using `Ff = f ∨ X Ff`,
`Gf = f ∧ X Gf`, `f U g = g ∨ (f ∧ X(f U g))`, the W equation, and R/M duals gives:

```text
v z ⊨ x  iff  z ⊨ Δᵥ(x).                         (1)
```

`DᵥU` implements these equations, and final U preserves interpretation.
Unfolded x therefore steps to `U Dᵥ x`; induction extends (1) over prefixes.
Unfolding/stepping preserve all three syntactic classes.

If `z ⊨ c`, some finite derivative is propositionally true. Structural witness
lengths are zero for true, absent for false, one for literals, maximum for
conjunction, a satisfied operand for disjunction, and one extra for X. F chooses
a satisfying operand position. U chooses g at finite j and f before j; M
chooses f at j and g through j. Take the maximum end of these finitely many
operand witnesses. Unfolding contains that sufficient Boolean branch, whose
factors become true by induction; true persists, justifying maxima.

Dually, violated s has a propositionally false finite derivative. Its NNF
dualization commutes clausewise with unfolding/stepping and swaps true/false,
renaming modal variables to duals without assuming Boolean complements.
Finite b becomes its actual truth constant within h+1 letters: each step
reduces X depth and evaluates exposed APs. Support-tested classes inherit these
lemmas because positive Boolean functions of grammar atoms have representatives
in that grammar.

## Component correctness

For safety, R stays suspended and every residual is safety. By (1), satisfying
words never reach false and mark forever; violations reach false by a finite
bad prefix and never mark again. Thus `L(Bs)=L(s)`.

For co-safety, satisfying words reach true and mark forever. Violations cannot
reach true and mark only on reaching safety. A residual in both grammars is
finite, since their supported-atom intersection is b, so a violating one soon
reaches false. There are only finitely many marks: `L(Bc)=L(c)`, including the
safety-row precedence on finite co-safety.

For nonconstant finite b, define independent modal variables H,K:

```text
H = [F b],   K = [G F b],   S = H ∨ b,   A* = K ∧ S.
```

Constants were folded above. `U(K)=A*`; with finite `e=Dᵥ(b)`:

```text
a = Dᵥ(A*) = K ∧ (H ∨ e),
U(a) = K ∧ (H ∨ b) ∧ (H ∨ b ∨ e) = A*.          (2)
```

A is fixed, neither safety nor co-safety. Extracting K first yields true,
then retries A*, so `ρ(K)=S`. Extracting raw a deletes K, leaving `H ∨ e`
unless already true. Every X in e is a tail of b and syntactically protected
by H, so none is elided. Unfolding yields `S ∨ e`; if finite it must be true
(otherwise it depends on H), and retry returns S:

```text
ρ(a) = S                 if b ∨ e = true,
       S ∨ e             otherwise.             (3)
```

The first case requires `a≠A*`: equality would imply `e=b` by independent H/K
assignments, contradicting nonconstant b and `b∨e=true`. This also covers
semantically constant b that is not propositionally constant.

Every active R is `H ∨ E` for finite E, initially/after renewal by (3), with
unmarked successor `H ∨ b ∨ Dᵥ(E)`. It cannot be false; finite means true.
Resume/false-renewal are unreachable, and renewal marks exactly `(A*,ρ(a))`.
Finite nonconstant remainders are unreachable here; the general table must
still retain them. `A* ⇒ S ⇒ R` holds propositionally, so breakpoint failure
never interrupts derivative invariant (1).

Round starts are initialization and states after marked edges, at positions t.
Initial seed is S; later seeds are S or `S ∨ D_{w[t−1]}(b)`. Unmarked steps
are exact derivatives; renewal forgets witness starts before t−1.

If `w ⊨ GF b`, every round-start suffix satisfies H and its seed. A round that
never ends would evolve this satisfied co-safety seed by exact derivatives;
its finite witness forces true and a mark. Every round ends, giving infinitely
many marks: `L(GF b) ⊆ L(BGFb)`.

Conversely, every completed round reaches `U(r)=true`, so (1) gives
`w[t:] ⊨ R_t`. Initial S gives b at some `j≥t`. Later seeds give either H
(and such j) or `w[t:] ⊨ D_{w[t−1]}(b)`, hence b at t−1 by (1).
Each completed round therefore gives a b occurrence starting at `j≥t−1`.
Infinitely many strictly increasing starts give unbounded occurrence positions,
so `L(BGFb) ⊆ L(GF b)`.

Witnesses need not be separated: retained derivatives carry all preceding-letter
X delay, and H searches later starts. Unbounded starts prevent reuse of finitely
many witnesses; finite witnesses prevent overlap/delay from blocking renewal.
No cohort/SCC assumption is needed. Completeness/unique runs make Inf(0) and
Fin(0) complements, proving `L(Bχ,Fin(0))=L(¬χ)`, including FG.

## One-set Zielonka parity

The universe is `{0}`. Inf(0) has accepting root `{0}` and rejecting child ∅;
Fin(0) reverses acceptance. The sole leaf path `[0]` persists; state is
`(A,R,[0])`. The ordinary deepest-containing-node update advances one sibling
and descends leftmost. Marked edges anchor at depth 0, unmarked at depth 1,
including empty marks. Root offset is 0 when accepting, otherwise 1.
For max-odd export `P−p`, `P=3`:

| Component acceptance | Marked: min-even p / max-odd export | Unmarked: p / export |
| --- | --- | --- |
| Inf(0) | 0 / 3 | 1 / 2 |
| Fin(0) | 1 / 2 | 2 / 1 |

Infinitely many marks give recurring maximum 3/2 respectively; finitely many
give 2/1. Thus both orientations accept correctly, including sinks/no marks:
`max Inf(3−p) = 3−min Inf(p)` is odd iff the minimum is even.
Every edge has priority; there are no resets or missing letters.

## Scope

This proof replaces the restricted [#80](https://github.com/gaperez64/tlsf-tools/issues/80)
obligations with finite witnesses, fixed GF all-field, protected X tails,
retry/seed calculations, and both round inclusions. Suspension is permanent
for safety/co-safety and absent for nontrivial GF. It proves no general Π₂
cohort, repeated unprotected-X elision, nonconstant renewal, or resumption lemma.
The restricted constructor must decline outside its grammar unless canonicalization
puts the whole formula inside. This includes `G(a → F(Xb ∧ XXc))` and general
recurrence products; a Π₂ tag, tests, or support changes cannot justify them.
The [extended proof](STAGE2-PROOF.md) covers a broader grammar.

Support blocking/resets [#81](https://github.com/gaperez64/tlsf-tools/issues/81),
DELA suspension/round robin/padding [#82](https://github.com/gaperez64/tlsf-tools/issues/82),
and stuttering/local resets [#83](https://github.com/gaperez64/tlsf-tools/issues/83)
remain outside this theorem. No external automata theorem was assumed.
Inspected Owl references are `src/main/java/owl/ltl/SyntacticFragments.java:42–95`
and `src/main/java/owl/translations/canonical/DeterministicConstructions.java:682–779`;
[the design](DESIGN.md) fixes the variant, without Owl's extra optimizations.
Proof review and implementation/bridge checks remain separate closing gates.
