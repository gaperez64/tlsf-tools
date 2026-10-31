import TlsfProofs.Dpa.Impl.Transport
import TlsfProofs.Dpa.Impl.Grouping

/-!
# Recursive factoring of frozen syntax

The decoded traversal of `src/lib/dpa_formula.c:524` retains safety/co-safety
terms, recursively factors children, and repeats on the smart-constructed
distribution of G over conjunction or F over disjunction. In particular it
inspects the *returned* child, which can expose a new Boolean node.

`factorWeight` charges twice the operand weight for unary nodes and the sum
plus one for binary nodes. Distribution strictly decreases this measure,
even though it can increase ordinary syntax size. Fuel models a recursion
limit; the proved sufficient bound is used by `factor` and `factorCached`.
The latter threads the actual recursive memo writes and hits. C's term IDs,
hash-consing and faithful memo-table decoding remain representation boundaries.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

def factorWeight : Formula α → Nat
  | .tt | .ff | .ap _ => 1
  | .neg f | .next f | .strongNext f | .eventually f | .globally f => 2 * factorWeight f
  | .conj f g | .disj f g | .impl f g | .equiv f g
  | .until f g | .release f g | .weakUntil f g | .strongRelease f g =>
      factorWeight f + factorWeight g + 1

theorem factorWeight_pos (f : Formula α) : 0 < factorWeight f := by
  induction f <;> simp only [factorWeight] <;> omega

private theorem orderedBoolean_factorWeight (op : Bool) (f g : Formula (Fin ap)) :
    factorWeight (orderedBoolean op f g) ≤ factorWeight f + factorWeight g + 1 := by
  unfold orderedBoolean
  split
  · omega
  · cases f <;> cases op <;> simp [factorWeight] <;> omega

theorem termBoolean_factorWeight (rank : Formula (Fin ap) → Nat) (op : Bool)
    (f g : Formula (Fin ap)) :
    factorWeight (termBoolean rank op f g) ≤ factorWeight f + factorWeight g + 1 := by
  unfold termBoolean
  split
  · simpa only [Nat.add_comm (factorWeight f) (factorWeight g)] using
      orderedBoolean_factorWeight op g f
  · exact orderedBoolean_factorWeight op f g

theorem termUnary_factorWeight (op : UnaryTerm) (f : Formula α) :
    factorWeight (termUnary op f) ≤ 2 * factorWeight f := by
  cases f <;> cases op <;> simp [termUnary, UnaryTerm.apply, factorWeight]

def FactorSpec (f g : Formula (Fin ap)) : Prop :=
  NNF g ∧ factorWeight g ≤ factorWeight f ∧
    ∀ w n, Sat none w g n ↔ Sat none w f n

theorem FactorSpec.refl (hf : NNF f) : FactorSpec f f :=
  ⟨hf, Nat.le_refl _, fun _ _ => Iff.rfl⟩

theorem FactorSpec.trans (h : FactorSpec f g) (h' : FactorSpec g k) : FactorSpec f k :=
  ⟨h'.1, Nat.le_trans h'.2.1 h.2.1, fun w n => (h'.2.2 w n).trans (h.2.2 w n)⟩

private theorem unary_congr (op : UnaryTerm) (f g : Formula (Fin ap))
    (h : ∀ w n, Sat none w f n ↔ Sat none w g n) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (op.apply f) n ↔ Sat none w (op.apply g) n := by
  cases op <;> simp [UnaryTerm.apply, Sat, InRange, AllFuture, h]

private theorem unary_spec (op : UnaryTerm) (h : FactorSpec f g) :
    FactorSpec (op.apply f) (termUnary op g) := by
  refine ⟨termUnary_nnf op g h.1, ?_, fun w n => ?_⟩
  · have hw := termUnary_factorWeight op g
    have hg := h.2.1
    cases op <;> simp only [UnaryTerm.apply, factorWeight] <;> omega
  · exact (termUnary_language op g w n).trans (unary_congr op g f h.2.2 w n)

inductive FactorBinary where
  | boolean (op : Bool) | «until» | release | weakUntil | strongRelease

def FactorBinary.apply (rank : Formula (Fin ap) → Nat) :
    FactorBinary → Formula (Fin ap) → Formula (Fin ap) → Formula (Fin ap)
  | .boolean op, f, g => termBoolean rank op f g
  | .until, f, g => .until f g
  | .release, f, g => .release f g
  | .weakUntil, f, g => .weakUntil f g
  | .strongRelease, f, g => .strongRelease f g

def FactorBinary.raw : FactorBinary → Formula α → Formula α → Formula α
  | .boolean true, f, g => .conj f g
  | .boolean false, f, g => .disj f g
  | .until, f, g => .until f g
  | .release, f, g => .release f g
  | .weakUntil, f, g => .weakUntil f g
  | .strongRelease, f, g => .strongRelease f g

private theorem binary_spec (rank : Formula (Fin ap) → Nat) (op : FactorBinary)
    (hf : FactorSpec f f') (hg : FactorSpec g g') :
    FactorSpec (op.raw f g) (op.apply rank f' g') := by
  refine ⟨?_, ?_, fun w n => ?_⟩
  · cases op with
    | boolean op => exact termBoolean_nnf rank op f' g' hf.1 hg.1
    | _ => exact ⟨hf.1, hg.1⟩
  · have hfw := hf.2.1
    have hgw := hg.2.1
    cases op with
    | boolean op =>
      have hw := termBoolean_factorWeight rank op f' g'
      cases op <;> simp only [FactorBinary.raw, FactorBinary.apply, factorWeight] <;> omega
    | _ => simp only [FactorBinary.raw, FactorBinary.apply, factorWeight]; omega
  · cases op with
    | boolean op =>
      rw [FactorBinary.apply, termBoolean_language]
      cases op <;> simp [FactorBinary.raw, Sat, InRange, hf.2.2, hg.2.2]
    | _ => simp [FactorBinary.raw, FactorBinary.apply, Sat, InRange, UntilAt,
        AllFuture, hf.2.2, hg.2.2]

/-- Smart construction in the distribution branch. C uses the factored
operand's root operator, rather than the original operand's operator. -/
def factorDistribution (rank : Formula (Fin ap) → Nat) :
    UnaryTerm → Formula (Fin ap) → Option (Formula (Fin ap))
  | .global, .conj f g =>
      some (termBoolean rank true (termUnary .global f) (termUnary .global g))
  | .eventual, .disj f g =>
      some (termBoolean rank false (termUnary .eventual f) (termUnary .eventual g))
  | _, _ => none

theorem factorDistribution_spec (rank : Formula (Fin ap) → Nat) (op : UnaryTerm)
    (f d : Formula (Fin ap)) (hf : NNF f) (hd : factorDistribution rank op f = some d) :
    NNF d ∧ factorWeight d < 2 * factorWeight f ∧
      ∀ w n, Sat none w d n ↔ Sat none w (op.apply f) n := by
  cases op <;> cases f <;> simp [factorDistribution] at hd
  all_goals subst d
  all_goals refine ⟨termBoolean_nnf rank _ _ _
      (termUnary_nnf _ _ hf.1) (termUnary_nnf _ _ hf.2), ?_, fun w n => ?_⟩
  · rename_i a b
    have hb := termBoolean_factorWeight rank false (termUnary .eventual a) (termUnary .eventual b)
    have ha := termUnary_factorWeight .eventual a
    have hc := termUnary_factorWeight .eventual b
    simp only [factorWeight]
    omega
  · simp only [termBoolean_language, termUnary_language, UnaryTerm.apply]
    simpa only [Sat, InRange, true_and, Bool.false_eq_true, ↓reduceIte] using
      (distribute_F_disj _ _ w n).symm
  · rename_i a b
    have hb := termBoolean_factorWeight rank true (termUnary .global a) (termUnary .global b)
    have ha := termUnary_factorWeight .global a
    have hc := termUnary_factorWeight .global b
    simp only [factorWeight]
    omega
  · simp only [termBoolean_language, termUnary_language, UnaryTerm.apply]
    simpa only [Sat, InRange, true_and, ↓reduceIte] using
      (distribute_G_conj _ _ w n).symm

/-- One unary reconstruction, including the recursive call on newly
distributed syntax at `src/lib/dpa_formula.c:524`. -/
def factorUnary (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap)))
    (op : UnaryTerm) (f : Formula (Fin ap)) : Option (Formula (Fin ap)) := do
  let body ← recur f
  match factorDistribution rank op body with
  | some d => recur d
  | none => pure (termUnary op body)

def factorBinary (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap)))
    (op : FactorBinary) (f g : Formula (Fin ap)) : Option (Formula (Fin ap)) := do
  let a ← recur f
  let b ← recur g
  pure (op.apply rank a b)

def factorStep (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap)))
    (f : Formula (Fin ap)) : Option (Formula (Fin ap)) :=
  if safetyb f || cosafetyb f then some f else
  match f with
  | .conj f g => factorBinary rank recur (.boolean true) f g
  | .disj f g => factorBinary rank recur (.boolean false) f g
  | .next f => factorUnary rank recur .next f
  | .eventually f => factorUnary rank recur .eventual f
  | .globally f => factorUnary rank recur .global f
  | .until f g => factorBinary rank recur .until f g
  | .release f g => factorBinary rank recur .release f g
  | .weakUntil f g => factorBinary rank recur .weakUntil f g
  | .strongRelease f g => factorBinary rank recur .strongRelease f g
  | _ => some f

def factorTerm (rank : Formula (Fin ap) → Nat) :
    Nat → Formula (Fin ap) → Option (Formula (Fin ap))
  | 0, _ => none
  | fuel + 1, f => factorStep rank (factorTerm rank fuel) f

private theorem distributed_body_spec (rank : Formula (Fin ap) → Nat) (op : UnaryTerm)
    (h : FactorSpec f body) (hd : factorDistribution rank op body = some d) :
    FactorSpec (op.apply f) d := by
  have ds := factorDistribution_spec rank op body d h.1 hd
  refine ⟨ds.1, ?_, fun w n => (ds.2.2 w n).trans (unary_congr op body f h.2.2 w n)⟩
  have hw := h.2.1
  cases op <;> simp only [UnaryTerm.apply, factorWeight] <;> omega

private theorem factorUnary_spec (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap)))
    (hr : ∀ a b, NNF a → recur a = some b → FactorSpec a b)
    (op : UnaryTerm) (hf : NNF f) (ht : factorUnary rank recur op f = some t) :
    FactorSpec (op.apply f) t := by
  simp only [factorUnary, bind, Option.bind_eq_some_iff] at ht
  obtain ⟨body, hb, ht⟩ := ht
  have bs := hr f body hf hb
  cases hd : factorDistribution rank op body with
  | none =>
    simp only [hd, pure, Option.some.injEq] at ht
    subst t
    exact unary_spec op bs
  | some d =>
    simp only [hd] at ht
    have ds := distributed_body_spec rank op bs hd
    exact ds.trans (hr d t ds.1 ht)

private theorem factorBinary_spec (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap)))
    (hr : ∀ a b, NNF a → recur a = some b → FactorSpec a b)
    (op : FactorBinary) (hf : NNF f) (hg : NNF g)
    (ht : factorBinary rank recur op f g = some t) :
    FactorSpec (op.raw f g) t := by
  simp only [factorBinary, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  exact binary_spec rank op (hr f a hf ha) (hr g b hg hb)

theorem factorStep_spec (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap)))
    (hr : ∀ a b, NNF a → recur a = some b → FactorSpec a b)
    (f t : Formula (Fin ap)) (hf : NNF f) (ht : factorStep rank recur f = some t) :
    FactorSpec f t := by
  unfold factorStep at ht
  split at ht
  · cases Option.some.inj ht; exact FactorSpec.refl hf
  · cases f with
    | conj f g => exact factorBinary_spec rank recur hr (.boolean true) hf.1 hf.2 ht
    | disj f g => exact factorBinary_spec rank recur hr (.boolean false) hf.1 hf.2 ht
    | next f => exact factorUnary_spec rank recur hr .next hf ht
    | eventually f => exact factorUnary_spec rank recur hr .eventual hf ht
    | globally f => exact factorUnary_spec rank recur hr .global hf ht
    | «until» f g => exact factorBinary_spec rank recur hr .until hf.1 hf.2 ht
    | release f g => exact factorBinary_spec rank recur hr .release hf.1 hf.2 ht
    | weakUntil f g => exact factorBinary_spec rank recur hr .weakUntil hf.1 hf.2 ht
    | strongRelease f g => exact factorBinary_spec rank recur hr .strongRelease hf.1 hf.2 ht
    | _ => cases Option.some.inj ht; exact FactorSpec.refl hf

/-- Every successful bounded traversal preserves NNF, language, and weight.
This does not assume that distribution preserves independent modal classes. -/
theorem factorTerm_spec (rank : Formula (Fin ap) → Nat) (fuel : Nat)
    (f t : Formula (Fin ap)) (hf : NNF f) (ht : factorTerm rank fuel f = some t) :
    FactorSpec f t := by
  induction fuel generalizing f t with
  | zero => simp [factorTerm] at ht
  | succ fuel ih => exact factorStep_spec rank _ ih f t hf ht

private theorem factorUnary_success (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap))) (op : UnaryTerm)
    (f : Formula (Fin ap)) (hf : NNF f)
    (hr : ∀ g, NNF g → factorWeight g < 2 * factorWeight f →
      ∃ t, recur g = some t ∧ FactorSpec g t) :
    ∃ t, factorUnary rank recur op f = some t ∧ FactorSpec (op.apply f) t := by
  obtain ⟨body, hb, bs⟩ := hr f hf (by have hp := factorWeight_pos f; omega)
  cases hd : factorDistribution rank op body with
  | none => exact ⟨_, by simp [factorUnary, hb, hd], unary_spec op bs⟩
  | some d =>
    have ds := factorDistribution_spec rank op body d bs.1 hd
    have bw := bs.2.1
    obtain ⟨t, ht, ts⟩ := hr d ds.1 (by omega)
    exact ⟨t, by simp [factorUnary, hb, hd, ht],
      (distributed_body_spec rank op bs hd).trans ts⟩

private theorem factorBinary_success (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap))) (op : FactorBinary)
    (f g : Formula (Fin ap)) (hf : NNF f) (hg : NNF g)
    (hr : ∀ a, NNF a → factorWeight a < factorWeight f + factorWeight g + 1 →
      ∃ t, recur a = some t ∧ FactorSpec a t) :
    ∃ t, factorBinary rank recur op f g = some t ∧ FactorSpec (op.raw f g) t := by
  obtain ⟨a, ha, aspec⟩ := hr f hf (by omega)
  obtain ⟨b, hb, bspec⟩ := hr g hg (by omega)
  exact ⟨_, by simp [factorBinary, ha, hb], binary_spec rank op aspec bspec⟩

theorem factorStep_success (rank : Formula (Fin ap) → Nat)
    (recur : Formula (Fin ap) → Option (Formula (Fin ap)))
    (f : Formula (Fin ap)) (hf : NNF f)
    (hr : ∀ g, NNF g → factorWeight g < factorWeight f →
      ∃ t, recur g = some t ∧ FactorSpec g t) :
    ∃ t, factorStep rank recur f = some t ∧ FactorSpec f t := by
  unfold factorStep
  split
  · exact ⟨f, rfl, FactorSpec.refl hf⟩
  · cases f with
    | conj f g => exact factorBinary_success rank recur (.boolean true) f g hf.1 hf.2 hr
    | disj f g => exact factorBinary_success rank recur (.boolean false) f g hf.1 hf.2 hr
    | next f => exact factorUnary_success rank recur .next f hf hr
    | eventually f => exact factorUnary_success rank recur .eventual f hf hr
    | globally f => exact factorUnary_success rank recur .global f hf hr
    | «until» f g => exact factorBinary_success rank recur .until f g hf.1 hf.2 hr
    | release f g => exact factorBinary_success rank recur .release f g hf.1 hf.2 hr
    | weakUntil f g => exact factorBinary_success rank recur .weakUntil f g hf.1 hf.2 hr
    | strongRelease f g => exact factorBinary_success rank recur .strongRelease f g hf.1 hf.2 hr
    | _ => exact ⟨_, rfl, FactorSpec.refl hf⟩

/-- The exponential weighted bound suffices even for recursion on a newly
distributed term. Fuel is never assumed to succeed. -/
theorem factorTerm_success (rank : Formula (Fin ap) → Nat) (fuel : Nat)
    (f : Formula (Fin ap)) (hf : NNF f) (hw : factorWeight f < fuel) :
    ∃ t, factorTerm rank fuel f = some t ∧ FactorSpec f t := by
  induction fuel generalizing f with
  | zero => omega
  | succ fuel ih =>
    exact factorStep_success rank _ f hf (fun g hg hgw => ih g hg (by omega))

def factor (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    Option (Formula (Fin ap)) := factorTerm rank (factorWeight f + 1) f

theorem factor_success (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) (hf : NNF f) :
    ∃ t, factor rank f = some t ∧ FactorSpec f t :=
  factorTerm_success rank _ f hf (by omega)

/-- The nonempty cells of C's per-term `factored` memo. Keys are frozen
syntax, never canonical Boolean classes. The C `result + 1` sentinel encoding
is decoded here, as are the term IDs themselves. -/
abbrev FactorMemo (ap : Nat) := List (Formula (Fin ap) × Formula (Fin ap))

def FactorMemo.Valid (memo : FactorMemo ap) : Prop :=
  ∀ f t, (f, t) ∈ memo → FactorSpec f t

theorem FactorMemo.empty_valid : FactorMemo.Valid ([] : FactorMemo ap) := by
  intro f t ht; simp at ht

def lookupFactored (f : Formula (Fin ap)) : FactorMemo ap → Option (Formula (Fin ap))
  | [] => none
  | (a, b) :: memo => if f = a then some b else lookupFactored f memo

theorem lookupFactored_spec (memo : FactorMemo ap) (hm : memo.Valid)
    (f t : Formula (Fin ap)) (ht : lookupFactored f memo = some t) : FactorSpec f t := by
  induction memo with
  | nil => simp [lookupFactored] at ht
  | cons entry memo ih =>
    obtain ⟨a, b⟩ := entry
    simp only [lookupFactored] at ht
    split at ht
    · rename_i he
      subst a
      cases Option.some.inj ht
      exact hm f t (by simp)
    · exact ih (fun a b hab => hm a b (by simp [hab])) ht

theorem FactorMemo.remember_valid (memo : FactorMemo ap) (hm : memo.Valid)
    (h : FactorSpec f t) : FactorMemo.Valid ((f, t) :: memo) := by
  intro a b hab
  rcases List.mem_cons.mp hab with he | he
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he; exact h
  · exact hm a b he

abbrev FactorAction (ap : Nat) :=
  Formula (Fin ap) → FactorMemo ap → Option (Formula (Fin ap) × FactorMemo ap)

def FactorAction.Sound (recur : FactorAction ap) : Prop :=
  ∀ f memo t out, NNF f → memo.Valid → recur f memo = some (t, out) →
    FactorSpec f t ∧ out.Valid

def factorCachedUnary (rank : Formula (Fin ap) → Nat) (recur : FactorAction ap)
    (op : UnaryTerm) (f : Formula (Fin ap)) (memo : FactorMemo ap) :
    Option (Formula (Fin ap) × FactorMemo ap) := do
  let (body, memo) ← recur f memo
  match factorDistribution rank op body with
  | some d => recur d memo
  | none => pure (termUnary op body, memo)

def factorCachedBinary (rank : Formula (Fin ap) → Nat) (recur : FactorAction ap)
    (op : FactorBinary) (f g : Formula (Fin ap)) (memo : FactorMemo ap) :
    Option (Formula (Fin ap) × FactorMemo ap) := do
  let (a, memo) ← recur f memo
  let (b, memo) ← recur g memo
  pure (op.apply rank a b, memo)

def rememberFactored (f : Formula (Fin ap))
    (result : Option (Formula (Fin ap) × FactorMemo ap)) :
    Option (Formula (Fin ap) × FactorMemo ap) := do
  let (t, memo) ← result
  pure (t, (f, t) :: memo)

def factorCachedStep (rank : Formula (Fin ap) → Nat) (recur : FactorAction ap)
    (f : Formula (Fin ap)) (memo : FactorMemo ap) :
    Option (Formula (Fin ap) × FactorMemo ap) :=
  match lookupFactored f memo with
  | some t => some (t, memo)
  | none =>
    if safetyb f || cosafetyb f then some (f, memo) else
    rememberFactored f (match f with
      | .conj f g => factorCachedBinary rank recur (.boolean true) f g memo
      | .disj f g => factorCachedBinary rank recur (.boolean false) f g memo
      | .next f => factorCachedUnary rank recur .next f memo
      | .eventually f => factorCachedUnary rank recur .eventual f memo
      | .globally f => factorCachedUnary rank recur .global f memo
      | .until f g => factorCachedBinary rank recur .until f g memo
      | .release f g => factorCachedBinary rank recur .release f g memo
      | .weakUntil f g => factorCachedBinary rank recur .weakUntil f g memo
      | .strongRelease f g => factorCachedBinary rank recur .strongRelease f g memo
      | _ => some (f, memo))

/-- Stateful factoring, including memo writes after each completed recursive
call and reuse by later siblings. Children are evaluated left before right,
as in `src/lib/dpa_formula.c:524`. Unlike C's bounded arena, this decoded
model has no allocation failure. -/
def factorCachedTerm (rank : Formula (Fin ap) → Nat) : Nat → FactorAction ap
  | 0, _, _ => none
  | fuel + 1, f, memo => factorCachedStep rank (factorCachedTerm rank fuel) f memo

private theorem factorCachedUnary_spec (rank : Formula (Fin ap) → Nat)
    (recur : FactorAction ap) (hr : recur.Sound) (op : UnaryTerm)
    (f : Formula (Fin ap)) (hf : NNF f) (memo : FactorMemo ap) (hm : memo.Valid)
    (t : Formula (Fin ap)) (out : FactorMemo ap)
    (ht : factorCachedUnary rank recur op f memo = some (t, out)) :
    FactorSpec (op.apply f) t ∧ out.Valid := by
  simp only [factorCachedUnary, bind, Option.bind_eq_some_iff] at ht
  obtain ⟨⟨body, mid⟩, hb, ht⟩ := ht
  obtain ⟨bs, bm⟩ := hr f memo body mid hf hm hb
  cases hd : factorDistribution rank op body with
  | none =>
    simp only [hd, pure, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨unary_spec op bs, bm⟩
  | some d =>
    have ds := distributed_body_spec rank op bs hd
    obtain ⟨ts, tm⟩ := hr d mid t out ds.1 bm (by simpa only [hd] using ht)
    exact ⟨ds.trans ts, tm⟩

private theorem factorCachedBinary_spec (rank : Formula (Fin ap) → Nat)
    (recur : FactorAction ap) (hr : recur.Sound) (op : FactorBinary)
    (f g : Formula (Fin ap)) (hf : NNF f) (hg : NNF g)
    (memo : FactorMemo ap) (hm : memo.Valid) (t : Formula (Fin ap)) (out : FactorMemo ap)
    (ht : factorCachedBinary rank recur op f g memo = some (t, out)) :
    FactorSpec (op.raw f g) t ∧ out.Valid := by
  simp only [factorCachedBinary, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨⟨a, mid⟩, ha, ⟨b, last⟩, hb, rfl, rfl⟩ := ht
  obtain ⟨aspec, am⟩ := hr f memo a mid hf hm ha
  obtain ⟨bspec, bm⟩ := hr g mid b last hg am hb
  exact ⟨binary_spec rank op aspec bspec, bm⟩

private theorem rememberFactored_spec (f t : Formula (Fin ap)) (out : FactorMemo ap)
    (result : Option (Formula (Fin ap) × FactorMemo ap))
    (hr : ∀ g memo, result = some (g, memo) → FactorSpec f g ∧ memo.Valid)
    (ht : rememberFactored f result = some (t, out)) : FactorSpec f t ∧ out.Valid := by
  simp only [rememberFactored, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨⟨g, memo⟩, hg, rfl, rfl⟩ := ht
  obtain ⟨gs, gm⟩ := hr g memo hg
  exact ⟨gs, memo.remember_valid gm gs⟩

theorem factorCachedStep_sound (rank : Formula (Fin ap) → Nat) (recur : FactorAction ap)
    (hr : recur.Sound) : FactorAction.Sound (factorCachedStep rank recur) := by
  intro f memo t out hf hm ht
  unfold factorCachedStep at ht
  cases he : lookupFactored f memo with
  | some g =>
    simp only [he, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨lookupFactored_spec memo hm f _ he, hm⟩
  | none =>
    simp only [he] at ht
    split at ht
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht)
      exact ⟨FactorSpec.refl hf, hm⟩
    · apply rememberFactored_spec f t out _ ?_ ht
      intro g last hg
      cases f with
      | conj f g => exact factorCachedBinary_spec rank recur hr (.boolean true) f g hf.1 hf.2 memo hm _ last hg
      | disj f g => exact factorCachedBinary_spec rank recur hr (.boolean false) f g hf.1 hf.2 memo hm _ last hg
      | next f => exact factorCachedUnary_spec rank recur hr .next f hf memo hm _ last hg
      | eventually f => exact factorCachedUnary_spec rank recur hr .eventual f hf memo hm _ last hg
      | globally f => exact factorCachedUnary_spec rank recur hr .global f hf memo hm _ last hg
      | «until» f g => exact factorCachedBinary_spec rank recur hr .until f g hf.1 hf.2 memo hm _ last hg
      | release f g => exact factorCachedBinary_spec rank recur hr .release f g hf.1 hf.2 memo hm _ last hg
      | weakUntil f g => exact factorCachedBinary_spec rank recur hr .weakUntil f g hf.1 hf.2 memo hm _ last hg
      | strongRelease f g => exact factorCachedBinary_spec rank recur hr .strongRelease f g hf.1 hf.2 memo hm _ last hg
      | _ =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hg)
        exact ⟨FactorSpec.refl hf, hm⟩

theorem factorCachedTerm_sound (rank : Formula (Fin ap) → Nat) (fuel : Nat) :
    FactorAction.Sound (factorCachedTerm rank fuel) := by
  induction fuel with
  | zero => intro f memo t out hf hm ht; simp [factorCachedTerm] at ht
  | succ fuel ih => exact factorCachedStep_sound rank _ ih

private theorem factorCachedUnary_success (rank : Formula (Fin ap) → Nat)
    (recur : FactorAction ap) (op : UnaryTerm) (f : Formula (Fin ap)) (hf : NNF f)
    (memo : FactorMemo ap) (hm : memo.Valid)
    (hr : ∀ g mid, NNF g → mid.Valid → factorWeight g < 2 * factorWeight f →
      ∃ t out, recur g mid = some (t, out) ∧ FactorSpec g t ∧ out.Valid) :
    ∃ t out, factorCachedUnary rank recur op f memo = some (t, out) ∧
      FactorSpec (op.apply f) t ∧ out.Valid := by
  obtain ⟨body, mid, hb, bs, bm⟩ := hr f memo hf hm (by have hp := factorWeight_pos f; omega)
  cases hd : factorDistribution rank op body with
  | none => exact ⟨_, mid, by simp [factorCachedUnary, hb, hd], unary_spec op bs, bm⟩
  | some d =>
    have ds := factorDistribution_spec rank op body d bs.1 hd
    have bw := bs.2.1
    obtain ⟨t, out, ht, ts, tm⟩ := hr d mid ds.1 bm (by omega)
    exact ⟨t, out, by simp [factorCachedUnary, hb, hd, ht],
      (distributed_body_spec rank op bs hd).trans ts, tm⟩

private theorem factorCachedBinary_success (rank : Formula (Fin ap) → Nat)
    (recur : FactorAction ap) (op : FactorBinary) (f g : Formula (Fin ap))
    (hf : NNF f) (hg : NNF g) (memo : FactorMemo ap) (hm : memo.Valid)
    (hr : ∀ a mid, NNF a → mid.Valid → factorWeight a < factorWeight f + factorWeight g + 1 →
      ∃ t out, recur a mid = some (t, out) ∧ FactorSpec a t ∧ out.Valid) :
    ∃ t out, factorCachedBinary rank recur op f g memo = some (t, out) ∧
      FactorSpec (op.raw f g) t ∧ out.Valid := by
  obtain ⟨a, mid, ha, aspec, am⟩ := hr f memo hf hm (by omega)
  obtain ⟨b, out, hb, bspec, bm⟩ := hr g mid hg am (by omega)
  exact ⟨_, out, by simp [factorCachedBinary, ha, hb], binary_spec rank op aspec bspec, bm⟩

private theorem rememberFactored_success (f : Formula (Fin ap))
    (result : Option (Formula (Fin ap) × FactorMemo ap))
    (hr : ∃ t out, result = some (t, out) ∧ FactorSpec f t ∧ out.Valid) :
    ∃ t out, rememberFactored f result = some (t, out) ∧ FactorSpec f t ∧ out.Valid := by
  obtain ⟨t, out, ht, ts, tm⟩ := hr
  exact ⟨t, (f, t) :: out, by simp [rememberFactored, ht], ts, out.remember_valid tm ts⟩

theorem factorCachedStep_success (rank : Formula (Fin ap) → Nat) (recur : FactorAction ap)
    (f : Formula (Fin ap)) (hf : NNF f) (memo : FactorMemo ap) (hm : memo.Valid)
    (hr : ∀ g mid, NNF g → mid.Valid → factorWeight g < factorWeight f →
      ∃ t out, recur g mid = some (t, out) ∧ FactorSpec g t ∧ out.Valid) :
    ∃ t out, factorCachedStep rank recur f memo = some (t, out) ∧ FactorSpec f t ∧ out.Valid := by
  unfold factorCachedStep
  cases he : lookupFactored f memo with
  | some t => exact ⟨t, memo, rfl, lookupFactored_spec memo hm f t he, hm⟩
  | none =>
    simp only
    split
    · exact ⟨f, memo, rfl, FactorSpec.refl hf, hm⟩
    · apply rememberFactored_success
      cases f with
      | conj f g => exact factorCachedBinary_success rank recur (.boolean true) f g hf.1 hf.2 memo hm hr
      | disj f g => exact factorCachedBinary_success rank recur (.boolean false) f g hf.1 hf.2 memo hm hr
      | next f => exact factorCachedUnary_success rank recur .next f hf memo hm hr
      | eventually f => exact factorCachedUnary_success rank recur .eventual f hf memo hm hr
      | globally f => exact factorCachedUnary_success rank recur .global f hf memo hm hr
      | «until» f g => exact factorCachedBinary_success rank recur .until f g hf.1 hf.2 memo hm hr
      | release f g => exact factorCachedBinary_success rank recur .release f g hf.1 hf.2 memo hm hr
      | weakUntil f g => exact factorCachedBinary_success rank recur .weakUntil f g hf.1 hf.2 memo hm hr
      | strongRelease f g => exact factorCachedBinary_success rank recur .strongRelease f g hf.1 hf.2 memo hm hr
      | _ => exact ⟨_, memo, rfl, FactorSpec.refl hf, hm⟩

theorem factorCachedTerm_success (rank : Formula (Fin ap) → Nat) (fuel : Nat)
    (f : Formula (Fin ap)) (hf : NNF f) (memo : FactorMemo ap) (hm : memo.Valid)
    (hw : factorWeight f < fuel) :
    ∃ t out, factorCachedTerm rank fuel f memo = some (t, out) ∧ FactorSpec f t ∧ out.Valid := by
  induction fuel generalizing f memo with
  | zero => omega
  | succ fuel ih =>
    exact factorCachedStep_success rank _ f hf memo hm
      (fun g mid hg hm hgw => ih g hg mid hm (by omega))

def factorCached (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    FactorMemo ap → Option (Formula (Fin ap) × FactorMemo ap) :=
  factorCachedTerm rank (factorWeight f + 1) f

theorem factorCached_success (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (hf : NNF f) (memo : FactorMemo ap) (hm : memo.Valid) :
    ∃ t out, factorCached rank f memo = some (t, out) ∧ FactorSpec f t ∧ out.Valid :=
  factorCachedTerm_success rank _ f hf memo hm (by omega)

/-- Unlike `runFactored`, this pipeline actually computes the factored
syntax. The original admission check and fallback still use the original
materialized class (`src/lib/dpa_formula.c:610`). -/
def runFactoring (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (original : Formula (Fin ap)) (s : AcceptanceState ap) : Option (CachedAssembly ap) :=
  if canonicalResearchCheck original then do
    let (factored, _) ← factorCached rank original []
    runFactored rank highFirst safetyFirst buchi original factored s
  else none

theorem runFactoring_presentation (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (original : Formula (Fin ap)) (ho : NNF original)
    (hc : canonicalResearchCheck original = true) (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runFactoring rank highFirst safetyFirst buchi original s = some r ∧
      r.Spec s original ∧ ProductPresentation original (storeClasses r.state.store) r.assembly.skeleton := by
  obtain ⟨factored, memo, ef, sf, _⟩ := factorCached_success rank original ho [] FactorMemo.empty_valid
  obtain ⟨r, er, sr, pr⟩ := runFactored_presentation rank highFirst safetyFirst buchi
    original factored ho sf.1 sf.2.2 hc s hs
  exact ⟨r, by simp [runFactoring, hc, ef, er], sr, pr⟩

def runTransported (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (f : Formula (Fin ap)) (s : AcceptanceState ap) : Option (CachedAssembly ap) := do
  let original ← transport rank f false 0
  runFactoring rank highFirst safetyFirst buchi original s

/-- Input transport, actual recursive factoring, grouped selection and cached
rest-first construction. Neither NNF of the transported/factored syntax nor
factoring's language equality is a hypothesis. This is a product presentation,
not yet the concrete parity export or the positive Büchi syntax selector. -/
theorem runTransported_presentation (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (f original : Formula (Fin ap)) (ht : transport rank f false 0 = some original)
    (hc : canonicalResearchCheck original = true) (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runTransported rank highFirst safetyFirst buchi f s = some r ∧
      r.Spec s f ∧ ProductPresentation f (storeClasses r.state.store) r.assembly.skeleton := by
  obtain ⟨r, er, sr, _⟩ := runFactoring_presentation rank highFirst safetyFirst buchi
    original (transport_nnf rank f false 0 original ht) hc s hs
  have sl : r.Spec s f := sr.language (fun w => by
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
      transport_language rank f false 0 original ht w 0)
  exact ⟨r, by simp [runTransported, ht, er], sl, sl.presentation⟩

def transportedResearchCheck (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) : Bool :=
  (transport rank f false 0).any canonicalResearchCheck

/-- A successful executable input-admission verdict supplies the actual
transport and factoring results; no externally supplied intermediate syntax
or language-preservation premise remains. -/
theorem admitted_transport_factoring_presentation (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (f : Formula (Fin ap)) (ha : transportedResearchCheck rank f = true)
    (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runTransported rank highFirst safetyFirst buchi f s = some r ∧
      r.Spec s f ∧ ProductPresentation f (storeClasses r.state.store) r.assembly.skeleton := by
  unfold transportedResearchCheck at ha
  cases ht : transport rank f false 0 with
  | none => simp [ht] at ha
  | some original =>
    exact runTransported_presentation rank highFirst safetyFirst buchi f original ht
      (by simpa only [ht, Option.any_some] using ha) s hs

end Tlsf.Dpa.Impl
