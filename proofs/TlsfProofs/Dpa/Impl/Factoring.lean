import TlsfProofs.Dpa.Impl.Transport
import TlsfProofs.Dpa.Impl.Selection

/-!
# Recursive factoring of frozen syntax

The decoded traversal of `src/lib/dpa_formula.c:524` retains safety/co-safety
terms, recursively factors children, and repeats on the smart-constructed
distribution of G over conjunction or F over disjunction. In particular it
inspects the *returned* child, which can expose a new Boolean node.

`factorWeight` charges twice the operand weight for unary nodes and the sum
plus one for binary nodes. Distribution strictly decreases this measure,
even though it can increase ordinary syntax size. Fuel is a recursion bound; `factor_success` proves the bound sufficient.
The reference uses no memo table or call trace.
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

/-- Prefer the factored plan, falling back to the admitted original. -/
def factoringPlan (rank atomRank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    Option (AcceptancePlan ap) := do
  let t ← factor rank f
  match canonicalPlan atomRank t with
  | some p => some p
  | none => canonicalPlan atomRank f

theorem factoringPlan_success (rank atomRank : Formula (Fin ap) → Nat)
    (f : Formula (Fin ap)) (hf : NNF f) (hc : canonicalResearchCheck f = true) :
    ∃ p, factoringPlan rank atomRank f = some p ∧ p.Valid ∧
      ∀ w n, Sat none w p.source n ↔ Sat none w f n := by
  obtain ⟨t, ht, hspec⟩ := factor_success rank f hf
  cases hp : canonicalPlan atomRank t with
  | some p =>
    obtain ⟨hv, he⟩ := canonicalPlan_spec atomRank t hspec.1 p hp
    exact ⟨p, by simp [factoringPlan, ht, hp], hv,
      fun w n => (class_language he w n).trans (hspec.2.2 w n)⟩
  | none =>
    obtain ⟨p, he⟩ := canonicalPlan_success atomRank f hc
    obtain ⟨hv, hc⟩ := canonicalPlan_spec atomRank f hf p he
    exact ⟨p, by simp [factoringPlan, ht, hp, he], hv, fun w n => class_language hc w n⟩

def transportedResearchCheck (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) : Bool :=
  (transport rank f false 0).any canonicalResearchCheck

def referencePlan (rank atomRank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    Option (AcceptancePlan ap) := do
  let t ← transport rank f false 0
  factoringPlan rank atomRank t

/-- Input admission supplies all intermediate results of the uncached construction. -/
theorem referencePlan_success (rank atomRank : Formula (Fin ap) → Nat)
    (f : Formula (Fin ap)) (ha : transportedResearchCheck rank f = true) :
    ∃ p, referencePlan rank atomRank f = some p ∧ p.Valid ∧
      ∀ w n, Sat none w p.source n ↔ Sat none w f n := by
  unfold transportedResearchCheck at ha
  cases ht : transport rank f false 0 with
  | none => simp [ht] at ha
  | some t =>
    obtain ⟨p, hp, hv, hl⟩ := factoringPlan_success rank atomRank t
      (transport_nnf rank f false 0 t ht) (by simpa [ht] using ha)
    refine ⟨p, by simp [referencePlan, ht, hp], hv, ?_⟩
    intro w n
    exact (hl w n).trans (by simpa using transport_language rank f false 0 t ht w n)

end Tlsf.Dpa.Impl
