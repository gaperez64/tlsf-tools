import TlsfProofs.Dpa.Impl.Classes
import TlsfProofs.Rewrites

/-!
# Frozen syntax transport with pending next operators

This is the decoded-syntax traversal of `src/lib/dpa_formula.c:394`.
`neg` has C's polarity (true means negate), and `pending` is C's `next`.
Boolean children inherit both parameters; modal operands restart at zero.
Strong-next is rejected, including in a subsequently absorbed branch.

`termBoolean` models `src/lib/dpa_formula.c:254`: sort by permanent term ID,
then eliminate duplicates and constants. Its `rank` parameter is the ID of
decoded syntax in the final, append-only C arena. All soundness results hold
for every rank, so they do not assume any allocation order. In the C instance
false/true have ranks 0/1. `termUnary` models the unary branch of `term`;
`wrapNext` models `src/lib/dpa_formula.c:388`.
Hash-consing, traversal memoization, resource failure and the representation
of IDs remain implementation boundaries. No Boolean absorption is performed
inside frozen syntax. In particular, the conclusion is language equality,
not equality of independent modal-atom classes.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

def orderedBoolean (op : Bool) (a b : Formula (Fin ap)) : Formula (Fin ap) :=
  if a = b then a else
  match a with
  | .ff => if op then .ff else b
  | .tt => if op then b else .tt
  | _ => if op then .conj a b else .disj a b

def termBoolean (rank : Formula (Fin ap) → Nat) (op : Bool)
    (f g : Formula (Fin ap)) : Formula (Fin ap) :=
  if rank f > rank g then orderedBoolean op g f else orderedBoolean op f g

private theorem orderedBoolean_language (op : Bool) (a b : Formula (Fin ap))
    (w : Word (Fin ap)) (j : Nat) :
    Sat none w (orderedBoolean op a b) j ↔
    (if op then Sat none w a j ∧ Sat none w b j
     else Sat none w a j ∨ Sat none w b j) := by
  unfold orderedBoolean
  by_cases he : a = b
  · subst b; cases op <;> simp
  · cases a <;> cases op <;> simp [he, Sat, InRange]

theorem termBoolean_language (rank : Formula (Fin ap) → Nat) (op : Bool)
    (f g : Formula (Fin ap)) (w : Word (Fin ap)) (j : Nat) :
    Sat none w (termBoolean rank op f g) j ↔
      (if op then Sat none w f j ∧ Sat none w g j
       else Sat none w f j ∨ Sat none w g j) := by
  unfold termBoolean
  split
  · simpa only [and_comm, or_comm] using orderedBoolean_language op g f w j
  · exact orderedBoolean_language op f g w j

private theorem orderedBoolean_nnf (op : Bool) (a b : Formula (Fin ap))
    (ha : NNF a) (hb : NNF b) : NNF (orderedBoolean op a b) := by
  unfold orderedBoolean
  split
  · exact ha
  · cases a <;> cases op <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact ha | exact hb | exact True.intro | exact ⟨ha, hb⟩

theorem termBoolean_nnf (rank : Formula (Fin ap) → Nat) (op : Bool)
    (f g : Formula (Fin ap)) (hf : NNF f) (hg : NNF g) :
    NNF (termBoolean rank op f g) := by
  unfold termBoolean
  split
  · exact orderedBoolean_nnf op g f hg hf
  · exact orderedBoolean_nnf op f g hf hg

inductive UnaryTerm where
  | next | eventual | global
  deriving DecidableEq

def UnaryTerm.apply : UnaryTerm → Formula α → Formula α
  | .next, f => .next f
  | .eventual, f => .eventually f
  | .global, f => .globally f

def termUnary (op : UnaryTerm) (f : Formula α) : Formula α :=
  match f with
  | .tt => .tt
  | .ff => .ff
  | _ => op.apply f

theorem termUnary_language (op : UnaryTerm) (f : Formula α) (w : Word α) (j : Nat) :
    Sat none w (termUnary op f) j ↔ Sat none w (op.apply f) j := by
  cases f <;> cases op <;>
    simp [termUnary, UnaryTerm.apply, Sat, InRange, AllFuture]
  all_goals exact ⟨j, Nat.le_refl j⟩

theorem termUnary_nnf (op : UnaryTerm) (f : Formula α) (h : NNF f) :
    NNF (termUnary op f) := by
  cases f <;> cases op <;> simp_all [termUnary, UnaryTerm.apply, NNF]

def wrapNext (f : Formula α) : Nat → Formula α
  | 0 => f
  | n + 1 => termUnary .next (wrapNext f n)

theorem wrapNext_language (f : Formula α) (pending : Nat) (w : Word α) (j : Nat) :
    Sat none w (wrapNext f pending) j ↔ Sat none w f (j + pending) := by
  induction pending generalizing j with
  | zero => simp [wrapNext]
  | succ n ih =>
    rw [wrapNext, termUnary_language]
    simpa [UnaryTerm.apply, Sat, InRange, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih (j + 1)

theorem wrapNext_nnf (f : Formula α) (h : NNF f) (pending : Nat) :
    NNF (wrapNext f pending) := by
  induction pending with
  | zero => exact h
  | succ _ ih => exact termUnary_nnf .next _ ih

/-- Successful syntax transport, before the Boolean class is materialized.
Input APs have already been resolved to `Fin ap`. Resource limits and invalid
AST pointers can only remove successful executions from this reference. -/
def transport (rank : Formula (Fin ap) → Nat) :
    Formula (Fin ap) → Bool → Nat → Option (Formula (Fin ap))
  | .tt, negate, _ => some (if negate then .ff else .tt)
  | .ff, negate, _ => some (if negate then .tt else .ff)
  | .ap a, negate, pending =>
      some (wrapNext (if negate then .neg (.ap a) else .ap a) pending)
  | .neg f, negate, pending => transport rank f (!negate) pending
  | .next f, negate, pending => transport rank f negate (pending + 1)
  | .strongNext _, _, _ => none
  | .conj f g, negate, pending => do
      let a ← transport rank f negate pending
      let b ← transport rank g negate pending
      pure (termBoolean rank (!negate) a b)
  | .disj f g, negate, pending => do
      let a ← transport rank f negate pending
      let b ← transport rank g negate pending
      pure (termBoolean rank negate a b)
  | .impl f g, negate, pending => do
      let a ← transport rank f (!negate) pending
      let b ← transport rank g negate pending
      pure (termBoolean rank negate a b)
  | .equiv f g, negate, pending => do
      let a ← transport rank f (!negate) pending
      let b ← transport rank g negate pending
      let first := termBoolean rank negate a b
      let a' ← transport rank f negate pending
      let b' ← transport rank g (!negate) pending
      pure (termBoolean rank (!negate) first (termBoolean rank negate a' b'))
  | .eventually f, negate, pending => do
      let a ← transport rank f negate 0
      pure (wrapNext (termUnary (if negate then .global else .eventual) a) pending)
  | .globally f, negate, pending => do
      let a ← transport rank f negate 0
      pure (wrapNext (termUnary (if negate then .eventual else .global) a) pending)
  | .until f g, negate, pending => do
      let a ← transport rank f negate 0
      let b ← transport rank g negate 0
      pure (wrapNext (if negate then .release a b else .until a b) pending)
  | .release f g, negate, pending => do
      let a ← transport rank f negate 0
      let b ← transport rank g negate 0
      pure (wrapNext (if negate then .until a b else .release a b) pending)
  | .weakUntil f g, negate, pending => do
      let a ← transport rank f negate 0
      let b ← transport rank g negate 0
      pure (wrapNext (if negate then .strongRelease a b else .weakUntil a b) pending)
  | .strongRelease f g, negate, pending => do
      let a ← transport rank f negate 0
      let b ← transport rank g negate 0
      pure (wrapNext (if negate then .weakUntil a b else .strongRelease a b) pending)

def transportableb : Formula α → Bool
  | .tt | .ff | .ap _ => true
  | .neg f | .next f | .eventually f | .globally f => transportableb f
  | .conj f g | .disj f g | .impl f g | .equiv f g
  | .until f g | .release f g | .weakUntil f g | .strongRelease f g =>
      transportableb f && transportableb g
  | .strongNext _ => false

private theorem optionAny_const (x : Option α) (b : Bool) :
    x.any (fun _ => b) = (x.isSome && b) := by
  cases x <;> simp

/-- Ignoring resource/invalid-input failures, strong-next is the only rejected
constructor. Even a strong-next in a constant-folded Boolean branch rejects. -/
theorem transport_domain (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (negate : Bool) (pending : Nat) :
    (transport rank f negate pending).isSome = transportableb f := by
  induction f generalizing negate pending with
  | equiv f g ihf ihg =>
    simp only [transport, bind, pure, Option.isSome_bind, Option.isSome_some,
      optionAny_const, ihf, ihg, transportableb]
    cases transportableb f <;> cases transportableb g <;> decide
  | _ => simp only [transport, bind, pure, Option.isSome_bind, Option.isSome_some,
      Option.isSome_none, optionAny_const, Bool.and_true, transportableb, *]

/-- The accumulated-next invariant, proved against the traversal itself.
The modal cases use operands transported at zero and then wrap the result;
the Boolean cases use children transported at the unchanged pending count. -/
theorem transport_language (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (negate : Bool) (pending : Nat) (t : Formula (Fin ap))
    (ht : transport rank f negate pending = some t) (w : Word (Fin ap)) (j : Nat) :
    Sat none w t j ↔
      (if negate then ¬Sat none w f (j + pending) else Sat none w f (j + pending)) := by
  classical
  induction f generalizing negate pending t j with
  | tt | ff =>
    simp only [transport, Option.some.injEq] at ht
    subst t
    cases negate <;> simp [Sat, InRange]
  | ap a =>
    simp only [transport, Option.some.injEq] at ht
    subst t
    rw [wrapNext_language]
    cases negate <;> simp [Sat, InRange]
  | neg f ih =>
    have h := ih (!negate) pending t ht j
    cases negate <;> simpa [Sat, InRange] using h
  | next f ih =>
    have h := ih negate (pending + 1) t ht j
    cases negate <;> simpa [Sat, InRange, Nat.add_assoc] using h
  | strongNext _ _ => simp [transport] at ht
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    rw [termBoolean_language]
    cases negate <;> simp [Sat, InRange, ihf _ _ _ ha, ihg _ _ _ hb]
    all_goals grind
  | equiv f g ihf ihg =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, b, hb, a', ha', b', hb', rfl⟩ := ht
    simp only [termBoolean_language]
    cases negate <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Sat, InRange, true_and, ihf _ _ _ ha, ihg _ _ _ hb,
      ihf _ _ _ ha', ihg _ _ _ hb']
    all_goals grind
  | eventually f ih | globally f ih =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    rw [wrapNext_language, termUnary_language]
    have he : Sat none w a = (fun k =>
        if negate then ¬Sat none w f k else Sat none w f k) := by
      funext k
      exact propext (by simpa only [Nat.add_zero] using ih negate 0 a ha k)
    cases negate <;> simp only [Bool.false_eq_true, ↓reduceIte, UnaryTerm.apply,
      Sat, InRange, true_and]
    all_goals simp [he, AllFuture, InRange]
  | «until» f g ihf ihg | release f g ihf ihg | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    rw [wrapNext_language]
    have hu := until_congr (len := none) (j := j + pending)
      (fun k _ _ => ihf negate 0 a ha k) (fun k _ _ => ihg negate 0 b hb k)
    have hn := until_congr (len := none) (j := j + pending)
      (fun k _ _ => not_congr (ihf negate 0 a ha k))
      (fun k _ _ => not_congr (ihg negate 0 b hb k))
    have hg := future_congr (len := none) (j := j + pending)
      (fun k _ _ => ihf negate 0 a ha k)
    have hgn := future_congr (len := none) (j := j + pending)
      (fun k _ _ => not_congr (ihf negate 0 a ha k))
    cases negate <;> simp [Sat, InRange, hu, hn, hg, hgn]
    all_goals grind

theorem transport_nnf (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (negate : Bool) (pending : Nat) (t : Formula (Fin ap))
    (ht : transport rank f negate pending = some t) : NNF t := by
  induction f generalizing negate pending t with
  | tt | ff =>
    simp only [transport, Option.some.injEq] at ht
    subst t
    cases negate <;> trivial
  | ap a =>
    simp only [transport, Option.some.injEq] at ht
    subst t
    apply wrapNext_nnf
    cases negate <;> trivial
  | neg f ih => exact ih (!negate) pending t ht
  | next f ih => exact ih negate (pending + 1) t ht
  | strongNext _ _ => simp [transport] at ht
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    exact termBoolean_nnf rank _ a b (ihf _ _ _ ha) (ihg _ _ _ hb)
  | equiv f g ihf ihg =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, b, hb, a', ha', b', hb', rfl⟩ := ht
    exact termBoolean_nnf rank _ _ _
      (termBoolean_nnf rank _ _ _ (ihf _ _ _ ha) (ihg _ _ _ hb))
      (termBoolean_nnf rank _ _ _ (ihf _ _ _ ha') (ihg _ _ _ hb'))
  | eventually f ih | globally f ih =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    exact wrapNext_nnf _ (termUnary_nnf _ a (ih _ _ _ ha)) pending
  | «until» f g ihf ihg | release f g ihf ihg | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    simp only [transport, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    apply wrapNext_nnf
    cases negate <;> exact ⟨ihf _ _ _ ha, ihg _ _ _ hb⟩

/-- The materialized transported class has an NNF representative and the
original language. `Class.ofFormula` freezes modal operands, just as
`src/lib/dpa_formula.c:366` stops materialization at a modal term. -/
theorem transport_class_language (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (t : Formula (Fin ap)) (ht : transport rank f false 0 = some t) :
    NNFClass (Class.ofFormula t) ∧
      ∀ w j, Holds w j (Class.ofFormula t) ↔ Sat none w f j := by
  refine ⟨⟨t, transport_nnf rank f false 0 t ht, rfl⟩, ?_⟩
  intro w j
  rw [ofFormula_holds]
  simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
    transport_language rank f false 0 t ht w j

end Tlsf.Dpa.Impl
