import TlsfProofs.Rewrites

/-!
# STAGE1 §§1–3 / STAGE2 §2: semantic propositional classes

APs are `Fin ap`. Modal atoms (including a formula and its NNF dual) are
independent variables. Only AP negation uses Boolean complementation.
A class is a Boolean function with a finite formula representative; equality
is equality of functions, never equality of LTL languages.
-/
namespace Tlsf.Dpa
open Formula
variable {ap : Nat}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Assignment (ap : Nat) := Formula (Fin ap) → Bool

def propEval (σ : Assignment ap) : Formula (Fin ap) → Bool
  | .tt => true | .ff => false | .ap a => σ (.ap a)
  | .neg f => !(propEval σ f)
  | .conj f g => propEval σ f && propEval σ g
  | .disj f g => propEval σ f || propEval σ g
  | .impl f g => !(propEval σ f) || propEval σ g
  | .equiv f g => propEval σ f == propEval σ g
  | f => σ f

/-- The finite Boolean function represented by a formula. Frozen modalities
are variables, rather than calls to temporal satisfaction. -/
def Class (ap : Nat) := { x : Assignment ap → Bool // ∃ f, x = fun σ => propEval σ f }

namespace Class
instance : CoeFun (Class ap) (fun _ => Assignment ap → Bool) := ⟨fun x => x.val⟩

def ofFormula (f : Formula (Fin ap)) : Class ap := ⟨fun σ => propEval σ f, f, rfl⟩
def top : Class ap := ofFormula .tt
def bot : Class ap := ofFormula .ff
noncomputable def repr (x : Class ap) : Formula (Fin ap) := Classical.choose x.property

theorem repr_eval (x : Class ap) (σ : Assignment ap) : propEval σ x.repr = x σ := by
  have h := congrFun (Classical.choose_spec x.property) σ
  exact h.symm

@[ext] theorem ext {x y : Class ap} (h : ∀ σ, x σ = y σ) : x = y :=
  Subtype.ext (funext h)

/-- Propositional implication (`⇒ₚ`), quantified over independent atom values. -/
def Implies (x y : Class ap) : Prop := ∀ σ, x σ = true → y σ = true
infix:50 " ⇒ₚ " => Implies

theorem implies_refl (x : Class ap) : x ⇒ₚ x := fun _ h => h
theorem implies_trans {x y z : Class ap} (h : x ⇒ₚ y) (h' : y ⇒ₚ z) : x ⇒ₚ z :=
  fun σ hx => h' σ (h σ hx)

noncomputable def meet (x y : Class ap) : Class ap :=
  ⟨fun σ => x σ && y σ, .conj x.repr y.repr, by
    funext σ; simp [propEval, repr_eval]⟩
noncomputable def join (x y : Class ap) : Class ap :=
  ⟨fun σ => x σ || y σ, .disj x.repr y.repr, by
    funext σ; simp [propEval, repr_eval]⟩

/-- A semantic support bound; it is finite even though modal formulas have no
fixed global size bound. -/
def DependsOn (x : Class ap) (atoms : List (Formula (Fin ap))) : Prop :=
  ∀ σ τ, (∀ a, a ∈ atoms → σ a = τ a) → x σ = x τ

end Class
open Class

/-- Non-nested atoms; no descent through a frozen modality. -/
def modalAtoms : Formula α → List (Formula α)
  | .tt | .ff => []
  | .ap a => [.ap a]
  | .neg f => modalAtoms f
  | .conj f g | .disj f g | .impl f g | .equiv f g => modalAtoms f ++ modalAtoms g
  | f => [f]

theorem propEval_local (f : Formula (Fin ap)) (σ τ : Assignment ap)
    (h : ∀ a, a ∈ modalAtoms f → σ a = τ a) : propEval σ f = propEval τ f := by
  induction f with
  | tt | ff => rfl
  | ap a => exact h _ (by simp [modalAtoms])
  | neg f ih => simp only [propEval]; rw [ih h]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    have hf := ihf (fun a ha => h a (by simp [modalAtoms, ha]))
    have hg := ihg (fun a ha => h a (by simp [modalAtoms, ha]))
    simp only [propEval]; rw [hf, hg]
  | _ => exact h _ (by simp [modalAtoms])

theorem class_finite_atoms (x : Class ap) : ∃ atoms, x.DependsOn atoms := by
  refine ⟨modalAtoms x.repr, ?_⟩
  intro σ τ h
  rw [← x.repr_eval σ, ← x.repr_eval τ]
  exact propEval_local _ _ _ h

/-- Syntactic finite-window, safety and co-safety tests (STAGE1 §1).
Negation here is permitted only on an AP. -/
def finite : Formula α → Prop
  | .tt | .ff | .ap _ | .neg (.ap _) => True
  | .conj f g | .disj f g => finite f ∧ finite g
  | .next f => finite f
  | _ => False

def safety : Formula α → Prop
  | .tt | .ff | .ap _ | .neg (.ap _) => True
  | .conj f g | .disj f g | .release f g | .weakUntil f g => safety f ∧ safety g
  | .next f | .globally f => safety f
  | _ => False

def cosafety : Formula α → Prop
  | .tt | .ff | .ap _ | .neg (.ap _) => True
  | .conj f g | .disj f g | .until f g | .strongRelease f g => cosafety f ∧ cosafety g
  | .next f | .eventually f => cosafety f
  | _ => False

def horizon : Formula α → Nat
  | .conj f g | .disj f g | .impl f g | .equiv f g => max (horizon f) (horizon g)
  | .neg f => horizon f
  | .next f | .strongNext f => horizon f + 1
  | _ => 0

/-- Unfolding equations have frozen continuations: recursive calls visit
operands, but never the displayed copy of the original modality. -/
def unfoldSyntax : Formula α → Formula α
  | .neg f => .neg (unfoldSyntax f)
  | .conj f g => .conj (unfoldSyntax f) (unfoldSyntax g)
  | .disj f g => .disj (unfoldSyntax f) (unfoldSyntax g)
  | .impl f g => .impl (unfoldSyntax f) (unfoldSyntax g)
  | .equiv f g => .equiv (unfoldSyntax f) (unfoldSyntax g)
  | .eventually f => .disj (unfoldSyntax f) (.eventually f)
  | .globally f => .conj (unfoldSyntax f) (.globally f)
  | .until f g => .disj (unfoldSyntax g) (.conj (unfoldSyntax f) (.until f g))
  | .weakUntil f g => .disj (unfoldSyntax g) (.conj (unfoldSyntax f) (.weakUntil f g))
  | .release f g => .conj (unfoldSyntax g) (.disj (unfoldSyntax f) (.release f g))
  | .strongRelease f g => .conj (unfoldSyntax g) (.disj (unfoldSyntax f) (.strongRelease f g))
  | f => f

/-- Simultaneous temporal stepping: APs exposed by X are not evaluated. -/
def stepSyntax (v : Letter α) : Formula α → Formula α
  | .ap a => if v a then .tt else .ff
  | .neg f => .neg (stepSyntax v f)
  | .conj f g => .conj (stepSyntax v f) (stepSyntax v g)
  | .disj f g => .disj (stepSyntax v f) (stepSyntax v g)
  | .impl f g => .impl (stepSyntax v f) (stepSyntax v g)
  | .equiv f g => .equiv (stepSyntax v f) (stepSyntax v g)
  | .next f | .strongNext f => f
  | f => f

/-- Boolean substitution underlying unfolding. -/
def unfoldAtom (σ : Assignment ap) (f : Formula (Fin ap)) : Bool :=
  propEval σ (unfoldSyntax f)

/-- Boolean substitution underlying a raw temporal step. -/
def stepAtom (v : Letter (Fin ap)) (σ : Assignment ap) : Formula (Fin ap) → Bool
  | .ap a => v a
  | .next f | .strongNext f => propEval σ f
  | f => σ f

theorem unfold_substitution (f : Formula (Fin ap)) (σ : Assignment ap) :
    propEval σ (unfoldSyntax f) = propEval (unfoldAtom σ) f := by
  induction f with
  | tt | ff | ap _ | next _ | strongNext _ | eventually _ | globally _
  | «until» _ _ | release _ _ | weakUntil _ _ | strongRelease _ _ => rfl
  | neg f ih => simp only [unfoldSyntax, propEval, ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [unfoldSyntax, propEval, ihf, ihg]

theorem step_substitution (f : Formula (Fin ap)) (v : Letter (Fin ap))
    (σ : Assignment ap) : propEval σ (stepSyntax v f) = propEval (stepAtom v σ) f := by
  induction f with
  | ap a => cases h : v a <;> simp [stepSyntax, propEval, stepAtom, h]
  | tt | ff | next _ | strongNext _ | eventually _ | globally _
  | «until» _ _ | release _ _ | weakUntil _ _ | strongRelease _ _ => rfl
  | neg f ih => simp only [stepSyntax, propEval, ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [stepSyntax, propEval, ihf, ihg]

/-- `U` on semantic classes, independent of the chosen representative. -/
noncomputable def U (x : Class ap) : Class ap :=
  ⟨fun σ => x (unfoldAtom σ), unfoldSyntax x.repr, by
    funext σ; rw [unfold_substitution, repr_eval]⟩

/-- Raw `Dᵥ`; the derivative is `U (Dᵥ (U x))`. -/
noncomputable def D (v : Letter (Fin ap)) (x : Class ap) : Class ap :=
  ⟨fun σ => x (stepAtom v σ), stepSyntax v x.repr, by
    funext σ; rw [step_substitution, repr_eval]⟩

noncomputable def delta (v : Letter (Fin ap)) (x : Class ap) : Class ap := U (D v (U x))

theorem U_monotone {x y : Class ap} (h : x ⇒ₚ y) : U x ⇒ₚ U y :=
  fun σ hx => h (unfoldAtom σ) hx

theorem D_monotone {x y : Class ap} (v : Letter (Fin ap)) (h : x ⇒ₚ y) :
    D v x ⇒ₚ D v y := fun σ hx => h (stepAtom v σ) hx

/-- STAGE1 §2, absorption of the second unfolding, as propositional equality. -/
theorem unfold_idempotent_eval (f : Formula (Fin ap)) (σ : Assignment ap) :
    propEval (unfoldAtom σ) (unfoldSyntax f) = propEval σ (unfoldSyntax f) := by
  induction f with
  | tt | ff | ap _ | next _ | strongNext _ => rfl
  | neg f ih => simp only [unfoldSyntax, propEval, ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [unfoldSyntax, propEval, ihf, ihg]
  | eventually f ih | globally f ih =>
    simp only [unfoldSyntax, propEval, ih]
    simp only [unfoldAtom, unfoldSyntax, propEval]
    cases propEval σ (unfoldSyntax f) <;> cases σ _ <;> rfl
  | «until» f g ihf ihg | weakUntil f g ihf ihg
  | release f g ihf ihg | strongRelease f g ihf ihg =>
    simp only [unfoldSyntax, propEval, ihf, ihg]
    simp only [unfoldAtom, unfoldSyntax, propEval]
    cases propEval σ (unfoldSyntax f) <;> cases propEval σ (unfoldSyntax g) <;>
      cases σ _ <;> rfl

theorem U_idempotent (x : Class ap) : U (U x) = U x := by
  apply Class.ext; intro σ
  change x (unfoldAtom (unfoldAtom σ)) = x (unfoldAtom σ)
  calc
    _ = propEval (unfoldAtom (unfoldAtom σ)) x.repr := (repr_eval _ _).symm
    _ = propEval (unfoldAtom σ) (unfoldSyntax x.repr) := (unfold_substitution _ _).symm
    _ = propEval σ (unfoldSyntax x.repr) := unfold_idempotent_eval _ _
    _ = propEval (unfoldAtom σ) x.repr := unfold_substitution _ _
    _ = _ := repr_eval _ _

noncomputable def truthAssignment (w : Word (Fin ap)) (j : Nat) : Assignment ap :=
  fun f => @decide (Sat none w f j) (Classical.propDecidable _)

noncomputable def Holds (w : Word (Fin ap)) (j : Nat) (x : Class ap) : Prop :=
  x (truthAssignment w j) = true

theorem implication_sound {x y : Class ap} (h : x ⇒ₚ y) (hw : Holds w j x) : Holds w j y :=
  h _ hw

/-- Evaluation of the propositional abstraction recovers the existing LTL core. -/
theorem propEval_truth (f : Formula (Fin ap)) (w : Word (Fin ap)) (j : Nat) :
    propEval (truthAssignment w j) f = true ↔ Sat none w f j := by
  classical
  induction f with
  | tt | ff | ap _ | next _ | strongNext _ | eventually _ | globally _
  | «until» _ _ | release _ _ | weakUntil _ _ | strongRelease _ _ =>
    simp [propEval, truthAssignment, Sat, InRange]
  | neg f ih => simpa [propEval, Sat, InRange] using not_congr ih
  | conj f g ihf ihg | disj f g ihf ihg =>
    simp [propEval, Sat, InRange, ihf, ihg]
  | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [propEval, Sat, InRange, true_and]
    cases hf : propEval (truthAssignment w j) f <;>
      cases hg : propEval (truthAssignment w j) g <;> simp_all

theorem ofFormula_holds (f : Formula (Fin ap)) :
    Holds w j (Class.ofFormula f) ↔ Sat none w f j := propEval_truth _ _ _

/-- One-letter equation, with an explicit next on the continuation. -/
theorem until_step {p q : Nat → Prop} :
    UntilAt none j p q ↔ q j ∨ (p j ∧ UntilAt none (j+1) p q) := by
  constructor
  · rintro ⟨k, hjk, _, hq, hp⟩
    by_cases h : k = j
    · exact Or.inl (h ▸ hq)
    · exact Or.inr ⟨hp j (Nat.le_refl _) (by omega), k, by omega,
        trivial, hq, fun i hi hik => hp i (by omega) hik⟩
  · rintro (hq | ⟨hp, k, hjk, _, hq, hall⟩)
    · exact ⟨j, Nat.le_refl _, trivial, hq, fun i hi hik => by omega⟩
    · exact ⟨k, by omega, trivial, hq, fun i hi hik => by
        by_cases h : i = j
        · exact h ▸ hp
        · exact hall i (by omega) hik⟩

theorem future_step {p : Nat → Prop} :
    AllFuture none j p ↔ p j ∧ AllFuture none (j+1) p := by
  constructor
  · intro h; exact ⟨h j (Nat.le_refl _) trivial, fun k hk _ => h k (by omega) trivial⟩
  · rintro ⟨hp, h⟩ k hk _
    by_cases he : k = j
    · exact he ▸ hp
    · exact h k (by omega) trivial

theorem eventually_step (f : Formula α) (w : Word α) :
    Sat none w (.eventually f) j ↔ Sat none w f j ∨ Sat none w (.eventually f) (j+1) := by
  simp only [Sat, InRange, true_and]
  constructor
  · rintro ⟨k, hk, h⟩
    by_cases he : k = j
    · exact Or.inl (he ▸ h)
    · exact Or.inr ⟨k, by omega, h⟩
  · rintro (h | ⟨k, hk, h⟩)
    · exact ⟨j, Nat.le_refl _, h⟩
    · exact ⟨k, by omega, h⟩

theorem globally_step (f : Formula α) (w : Word α) :
    Sat none w (.globally f) j ↔ Sat none w f j ∧ Sat none w (.globally f) (j+1) := by
  simpa only [Sat, InRange, true_and] using (future_step (p := Sat none w f) (j := j))

theorem weakUntil_step {p q : Nat → Prop} :
    (UntilAt none j p q ∨ AllFuture none j p) ↔
      q j ∨ (p j ∧ (UntilAt none (j+1) p q ∨ AllFuture none (j+1) p)) := by
  rw [until_step, future_step]
  constructor
  · rintro ((hq | ⟨hp, hu⟩) | ⟨hp, hg⟩)
    · exact Or.inl hq
    · exact Or.inr ⟨hp, Or.inl hu⟩
    · exact Or.inr ⟨hp, Or.inr hg⟩
  · rintro (hq | ⟨hp, hu | hg⟩)
    · exact Or.inl (Or.inl hq)
    · exact Or.inl (Or.inr ⟨hp, hu⟩)
    · exact Or.inr ⟨hp, hg⟩

/-- All six unbounded modalities use their own continuation after one letter. -/
theorem temporal_step (f g : Formula α) (w : Word α) (j : Nat) :
    (Sat none w (.until f g) j ↔
      Sat none w g j ∨ (Sat none w f j ∧ Sat none w (.until f g) (j+1))) ∧
    (Sat none w (.weakUntil f g) j ↔
      Sat none w g j ∨ (Sat none w f j ∧ Sat none w (.weakUntil f g) (j+1))) ∧
    (Sat none w (.release f g) j ↔
      Sat none w g j ∧ (Sat none w f j ∨ Sat none w (.release f g) (j+1))) ∧
    (Sat none w (.strongRelease f g) j ↔
      Sat none w g j ∧ (Sat none w f j ∨ Sat none w (.strongRelease f g) (j+1))) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Sat, InRange, true_and] using (until_step (p := Sat none w f) (q := Sat none w g))
  · simpa only [Sat, InRange, true_and] using (weakUntil_step (p := Sat none w f) (q := Sat none w g))
  · simp only [Sat, InRange, true_and]
    rw [until_step]; simp only [not_or, not_and, Classical.not_not]
    by_cases h : Sat none w f j <;> simp [h]
  · simp only [Sat, InRange, true_and]
    rw [weakUntil_step]; simp only [not_or, not_and, Classical.not_not]
    by_cases h : Sat none w f j <;> simp [h]

theorem unfold_sat (f : Formula (Fin ap)) (w : Word (Fin ap)) (j : Nat) :
    Sat none w (unfoldSyntax f) j ↔ Sat none w f j := by
  classical
  induction f with
  | tt | ff | ap _ | next _ | strongNext _ => rfl
  | neg f ih => simpa only [unfoldSyntax, Sat] using and_congr Iff.rfl (not_congr ih)
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [unfoldSyntax, Sat, InRange, true_and, ihf, ihg]
  | eventually f ih =>
    change (True ∧ (Sat none w (unfoldSyntax f) j ∨ Sat none w (.eventually f) j)) ↔ _
    simp only [true_and, ih]
    constructor
    · rintro (h | h)
      · exact ⟨trivial, j, Nat.le_refl _, trivial, h⟩
      · exact h
    · exact Or.inr
  | globally f ih =>
    change (True ∧ (Sat none w (unfoldSyntax f) j ∧ Sat none w (.globally f) j)) ↔ _
    simp only [true_and, ih]
    exact ⟨And.right, fun h => ⟨h.2 j (Nat.le_refl _) trivial, h⟩⟩
  | «until» f g ihf ihg =>
    change (True ∧ (Sat none w (unfoldSyntax g) j ∨
      (True ∧ Sat none w (unfoldSyntax f) j ∧ Sat none w (.until f g) j))) ↔ _
    simp only [true_and, ihf, ihg]
    rw [(temporal_step f g w j).1]
    by_cases hf : Sat none w f j <;> by_cases hg : Sat none w g j <;> simp [hf, hg]
  | weakUntil f g ihf ihg =>
    change (True ∧ (Sat none w (unfoldSyntax g) j ∨
      (True ∧ Sat none w (unfoldSyntax f) j ∧ Sat none w (.weakUntil f g) j))) ↔ _
    simp only [true_and, ihf, ihg]
    rw [(temporal_step f g w j).2.1]
    by_cases hf : Sat none w f j <;> by_cases hg : Sat none w g j <;> simp [hf, hg]
  | release f g ihf ihg =>
    change (True ∧ (Sat none w (unfoldSyntax g) j ∧
      (True ∧ (Sat none w (unfoldSyntax f) j ∨ Sat none w (.release f g) j)))) ↔ _
    simp only [true_and, ihf, ihg]
    rw [(temporal_step f g w j).2.2.1]
    by_cases hf : Sat none w f j <;> by_cases hg : Sat none w g j <;> simp [hf, hg]
  | strongRelease f g ihf ihg =>
    change (True ∧ (Sat none w (unfoldSyntax g) j ∧
      (True ∧ (Sat none w (unfoldSyntax f) j ∨ Sat none w (.strongRelease f g) j)))) ↔ _
    simp only [true_and, ihf, ihg]
    rw [(temporal_step f g w j).2.2.2]
    by_cases hf : Sat none w f j <;> by_cases hg : Sat none w g j <;> simp [hf, hg]

/-- STAGE1 §3: unfolding preserves the LTL interpretation of every class. -/
theorem U_holds (x : Class ap) : Holds w j (U x) ↔ Holds w j x := by
  change x (unfoldAtom (truthAssignment w j)) = true ↔ x (truthAssignment w j) = true
  rw [← repr_eval, ← repr_eval, ← unfold_substitution]
  exact (propEval_truth _ _ _).trans ((unfold_sat _ _ _).trans (propEval_truth _ _ _).symm)

/-- The raw one-step equations, including the simultaneous-X convention. -/
theorem derivative_syntax (f : Formula (Fin ap)) (w : Word (Fin ap)) (j : Nat) :
    Sat none w (stepSyntax (w j) (unfoldSyntax f)) (j+1) ↔ Sat none w f j := by
  classical
  induction f with
  | tt | ff => simp [unfoldSyntax, stepSyntax, Sat, InRange]
  | ap a => cases h : w j a <;> simp [unfoldSyntax, stepSyntax, Sat, InRange, h]
  | next f | strongNext f => simp [unfoldSyntax, stepSyntax, Sat, InRange]
  | neg f ih => simpa only [unfoldSyntax, stepSyntax, Sat, InRange, true_and] using not_congr ih
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [unfoldSyntax, stepSyntax, Sat, InRange, true_and, ihf, ihg]
  | eventually f ih =>
    simpa only [unfoldSyntax, stepSyntax, Sat, InRange, true_and, ih] using (eventually_step f w).symm
  | globally f ih =>
    simpa only [unfoldSyntax, stepSyntax, Sat, InRange, true_and, ih] using (globally_step f w).symm
  | «until» f g ihf ihg =>
    simpa only [unfoldSyntax, stepSyntax, Sat, InRange, true_and, ihf, ihg] using (temporal_step f g w j).1.symm
  | weakUntil f g ihf ihg =>
    simpa only [unfoldSyntax, stepSyntax, Sat, InRange, true_and, ihf, ihg] using (temporal_step f g w j).2.1.symm
  | release f g ihf ihg =>
    simpa only [unfoldSyntax, stepSyntax, Sat, InRange, true_and, ihf, ihg] using (temporal_step f g w j).2.2.1.symm
  | strongRelease f g ihf ihg =>
    simpa only [unfoldSyntax, stepSyntax, Sat, InRange, true_and, ihf, ihg] using (temporal_step f g w j).2.2.2.symm

/-- STAGE1 §3 (1): suffix notation is expressed by the position parameter. -/
theorem derivative (x : Class ap) (w : Word (Fin ap)) (j : Nat) :
    Holds w j x ↔ Holds w (j+1) (delta (w j) x) := by
  rw [delta, U_holds]
  change x (truthAssignment w j) = true ↔ x (unfoldAtom (stepAtom (w j) (truthAssignment w (j+1)))) = true
  rw [← repr_eval, ← repr_eval, ← unfold_substitution, ← step_substitution]
  exact (propEval_truth _ _ _).trans ((derivative_syntax _ _ _).symm.trans (propEval_truth _ _ _).symm)

/-- Assignment update used to define exact, semantic support. -/
def setAtom (σ : Assignment ap) (a : Formula (Fin ap)) (b : Bool) : Assignment ap :=
  fun t => if t = a then b else σ t

/-- A variable is supported exactly when changing it can change the function. -/
def Uses (x : Class ap) (a : Formula (Fin ap)) : Prop :=
  ∃ σ b, x (setAtom σ a b) ≠ x σ

theorem not_uses (h : ¬Uses x a) (σ : Assignment ap) (b : Bool) :
    x (setAtom σ a b) = x σ := by
  classical
  exact Classical.byContradiction (fun hn => h ⟨σ, b, hn⟩)

theorem uses_in_bound {atoms : List (Formula (Fin ap))} {x : Class ap}
    (h : x.DependsOn atoms) (ha : Uses x a) : a ∈ atoms := by
  classical
  apply Classical.byContradiction; intro hn
  obtain ⟨σ, b, hb⟩ := ha
  exact hb (h _ _ (fun t ht => by simp [setAtom, show t ≠ a from fun he => hn (he ▸ ht)]))

/-- Change a finite list of coordinates to their values in τ. -/
def patch (atoms : List (Formula (Fin ap))) (σ τ : Assignment ap) : Assignment ap :=
  match atoms with
  | [] => σ
  | a :: rest => patch rest (setAtom σ a (τ a)) τ

theorem patch_agrees (atoms : List (Formula (Fin ap))) (σ τ : Assignment ap) :
    ∀ a, a ∈ atoms → patch atoms σ τ a = τ a := by
  induction atoms generalizing σ with
  | nil => simp
  | cons a rest ih =>
    intro t ht
    rcases List.mem_cons.mp ht with he | ht
    · subst t
      by_cases hr : a ∈ rest
      · exact ih _ a hr
      · have outside : ∀ (xs : List (Formula (Fin ap))) (υ : Assignment ap),
            a ∉ xs → patch xs υ τ a = υ a := by
          intro xs; induction xs with
          | nil => intro υ _; rfl
          | cons b bs ihb =>
            intro υ hn
            rw [patch, ihb _ (fun hh => hn (by simp [hh]))]
            simp [setAtom, show a ≠ b from fun he => hn (by simp [he])]
        rw [patch, outside rest _ hr]
        simp [setAtom]
    · exact ih _ t ht

theorem patch_preserves (atoms : List (Formula (Fin ap))) (x : Class ap)
    (σ τ : Assignment ap) (h : ∀ a, a ∈ atoms → Uses x a → σ a = τ a) :
    x (patch atoms σ τ) = x σ := by
  classical
  induction atoms generalizing σ with
  | nil => rfl
  | cons a rest ih =>
    have hs : x (setAtom σ a (τ a)) = x σ := by
      by_cases hu : Uses x a
      · have he := h a (by simp) hu
        have heq : setAtom σ a (τ a) = σ := by
          funext t; by_cases ht : t = a <;> simp_all [setAtom]
        rw [heq]
      · exact not_uses hu σ _
    rw [patch, ih, hs]
    intro t ht hu
    by_cases he : t = a
    · simp [setAtom, he]
    · simp only [setAtom, he, ↓reduceIte]
      exact h t (by simp [ht]) hu

theorem support_locality (x : Class ap) (σ τ : Assignment ap)
    (h : ∀ a, Uses x a → σ a = τ a) : x σ = x τ := by
  obtain ⟨atoms, hd⟩ := class_finite_atoms x
  calc
    _ = x (patch atoms σ τ) := (patch_preserves atoms x σ τ (fun a _ => h a)).symm
    _ = _ := hd _ _ (patch_agrees atoms σ τ)

/-- Exact support tests, independent of a chosen syntax representative. -/
def HasTag (tag : Formula (Fin ap) → Prop) (x : Class ap) : Prop :=
  ∀ a, Uses x a → tag a

def isAP : Formula α → Prop
  | .ap _ => True | _ => False

def nonXModal : Formula α → Prop
  | .eventually _ | .globally _ | .until _ _ | .release _ _
  | .weakUntil _ _ | .strongRelease _ _ => True
  | _ => False

def isX : Formula α → Prop
  | .next _ => True | _ => False

def subformulas : Formula α → List (Formula α)
  | .tt => [.tt] | .ff => [.ff] | .ap a => [.ap a]
  | .neg f => .neg f :: subformulas f
  | .next f => .next f :: subformulas f
  | .strongNext f => .strongNext f :: subformulas f
  | .eventually f => .eventually f :: subformulas f
  | .globally f => .globally f :: subformulas f
  | .conj f g => .conj f g :: (subformulas f ++ subformulas g)
  | .disj f g => .disj f g :: (subformulas f ++ subformulas g)
  | .impl f g => .impl f g :: (subformulas f ++ subformulas g)
  | .equiv f g => .equiv f g :: (subformulas f ++ subformulas g)
  | .until f g => .until f g :: (subformulas f ++ subformulas g)
  | .release f g => .release f g :: (subformulas f ++ subformulas g)
  | .weakUntil f g => .weakUntil f g :: (subformulas f ++ subformulas g)
  | .strongRelease f g => .strongRelease f g :: (subformulas f ++ subformulas g)

/-- Protection is recomputed from the current reduced support. -/
def Protected (x : Class ap) (t : Formula (Fin ap)) : Prop :=
  ∃ a, Uses x a ∧ nonXModal a ∧ t ∈ subformulas a

noncomputable def replaceTrueSyntax (p : Formula (Fin ap) → Prop) :
    Formula (Fin ap) → Formula (Fin ap)
  | .tt => .tt | .ff => .ff
  | .neg f => .neg (replaceTrueSyntax p f)
  | .conj f g => .conj (replaceTrueSyntax p f) (replaceTrueSyntax p g)
  | .disj f g => .disj (replaceTrueSyntax p f) (replaceTrueSyntax p g)
  | .impl f g => .impl (replaceTrueSyntax p f) (replaceTrueSyntax p g)
  | .equiv f g => .equiv (replaceTrueSyntax p f) (replaceTrueSyntax p g)
  | f => @ite _ (p f) (Classical.propDecidable _) .tt f

theorem replaceTrue_eval (p : Formula (Fin ap) → Prop) (f : Formula (Fin ap))
    (σ : Assignment ap) : propEval σ (replaceTrueSyntax p f) =
      propEval (fun a => @ite _ (p a) (Classical.propDecidable _) true (σ a)) f := by
  classical
  induction f with
  | tt | ff => rfl
  | neg f ih => simp only [replaceTrueSyntax, propEval, ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [replaceTrueSyntax, propEval, ihf, ihg]
  | _ => simp only [replaceTrueSyntax]; split <;> simp_all [propEval]

noncomputable def replaceTrue (p : Formula (Fin ap) → Prop) (x : Class ap) : Class ap :=
  ⟨fun σ => x (fun a => @ite _ (p a) (Classical.propDecidable _) true (σ a)),
    replaceTrueSyntax p x.repr, by funext σ; rw [replaceTrue_eval, repr_eval]⟩

theorem replaceTrue_uses {p : Formula (Fin ap) → Prop} (h : Uses (replaceTrue p x) a) :
    Uses x a ∧ ¬p a := by
  classical
  obtain ⟨σ, b, hb⟩ := h
  have hpa : ¬p a := by
    intro hp
    apply hb
    change x _ = x _
    apply congrArg x; funext t
    by_cases ht : t = a <;> simp_all [setAtom]
  refine ⟨⟨(fun t => if p t then true else σ t), b, ?_⟩, hpa⟩
  have he : (fun t => if p t then true else setAtom σ a b t) =
      setAtom (fun t => if p t then true else σ t) a b := by
    funext t; by_cases ht : t = a <;> simp_all [setAtom]
  change x (fun t => if p t then true else setAtom σ a b t) ≠ _ at hb
  rwa [he] at hb

/-- Positive in modal variables; AP values need not be monotone. -/
def Positive (x : Class ap) : Prop :=
  ∀ σ τ, (∀ a, isAP a → σ a = τ a) →
    (∀ a, ¬isAP a → σ a = true → τ a = true) → x σ = true → x τ = true

theorem replaceTrue_weakens (hx : Positive x) (p : Formula (Fin ap) → Prop)
    (hp : ∀ a, isAP a → ¬p a) : x ⇒ₚ replaceTrue p x := by
  classical
  intro σ hs
  apply hx σ _ _ _ hs
  · intro a ha; simp [hp a ha]
  · intro a _ ha; simp [ha]

noncomputable def reduce (x : Class ap) : Class ap :=
  replaceTrue (fun a => ¬isAP a ∧ ¬cosafety a) x

noncomputable def dropX (x : Class ap) : Class ap :=
  replaceTrue (fun a => isX a ∧ ¬Protected x a) x

/-- A bounded implementation of the support-decreasing removal loop. -/
noncomputable def elideFuel : Nat → Class ap → Class ap
  | 0, x => x
  | n+1, x => if dropX x = x then x else elideFuel n (dropX x)

/-- The initial support size bounds the number of changing removal passes. -/
noncomputable def elide (x : Class ap) : Class ap :=
  elideFuel (modalAtoms x.repr).length x

noncomputable def extractPass (x : Class ap) : Class ap := U (elide (reduce x))

/-- `ρ`: exactly one possible retry, on the idempotently unfolded raw class. -/
noncomputable def rho (x : Class ap) : Class ap :=
  if HasTag finite (extractPass x) ∧ x ≠ U x then extractPass (U x) else extractPass x

theorem replaceTrue_bound {p : Formula (Fin ap) → Prop} {atoms : List (Formula (Fin ap))}
    (h : x.DependsOn atoms) : (replaceTrue p x).DependsOn atoms := by
  intro σ τ he
  apply h
  intro a ha
  by_cases hp : p a <;> simp [hp, he a ha]

theorem replaceTrue_eq (p : Formula (Fin ap) → Prop) (x : Class ap)
    (h : ∀ a, Uses x a → ¬p a) : replaceTrue p x = x := by
  apply Class.ext; intro σ
  change x (fun a => if p a then true else σ a) = x σ
  apply support_locality
  intro a ha
  simp [h a ha]

def supportMass (atoms : List (Formula (Fin ap))) (x : Class ap) : Nat :=
  (atoms.filter (fun a => decide (Uses x a))).length

theorem filter_strict {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a, a ∈ xs → q a = true → p a = true)
    (lost : ∃ a, a ∈ xs ∧ p a = true ∧ q a = false) :
    (xs.filter q).length < (xs.filter p).length := by
  induction xs with
  | nil => obtain ⟨a, ha, _⟩ := lost; contradiction
  | cons a xs ih =>
    have ht : ∀ t, t ∈ xs → q t = true → p t = true := fun t ht => h t (by simp [ht])
    by_cases hl : ∃ t, t ∈ xs ∧ p t = true ∧ q t = false
    · have hi := ih ht hl
      have hh := h a (by simp)
      cases hp : p a <;> cases hq : q a <;> simp_all <;> omega
    · obtain ⟨t, ht', hpt, hqt⟩ := lost
      have he : t = a := by
        rcases List.mem_cons.mp ht' with he | ht
        · exact he
        · exact False.elim (hl ⟨t, ht, hpt, hqt⟩)
      subst t
      have hsub : xs.filter q = xs.filter p := by
        apply List.filter_congr
        intro t hm
        have htp := ht t hm
        by_cases hp : p t = true
        · have hq : q t = true := by
            cases hq : q t
            · exact False.elim (hl ⟨t, hm, hp, hq⟩)
            · rfl
          simp [hp, hq]
        · have hq : q t = false := by
            cases hq : q t
            · rfl
            · exact False.elim (hp (htp hq))
          simp [Bool.eq_false_iff.mpr hp, hq]
      simp [hpt, hqt, hsub]

theorem dropX_mass_lt {atoms : List (Formula (Fin ap))} (hd : x.DependsOn atoms)
    (hne : dropX x ≠ x) : supportMass atoms (dropX x) < supportMass atoms x := by
  have hlost : ∃ a, Uses x a ∧ isX a ∧ ¬Protected x a := by
    apply Classical.byContradiction; intro hn
    apply hne
    apply replaceTrue_eq
    intro a ha hp
    exact hn ⟨a, ha, hp⟩
  obtain ⟨a, ha, hp⟩ := hlost
  apply filter_strict
  · intro t _ ht
    exact decide_eq_true (replaceTrue_uses (of_decide_eq_true ht)).1
  · refine ⟨a, uses_in_bound hd ha, decide_eq_true ha, ?_⟩
    apply decide_eq_false
    intro hu
    exact (replaceTrue_uses hu).2 hp

theorem elideFuel_stable (n : Nat) (x : Class ap) (atoms : List (Formula (Fin ap)))
    (hd : x.DependsOn atoms) (hn : supportMass atoms x ≤ n) :
    dropX (elideFuel n x) = elideFuel n x := by
  induction n generalizing x with
  | zero =>
    by_cases he : dropX x = x
    · exact he
    · have ht := dropX_mass_lt hd he; omega
  | succ n ih =>
    by_cases he : dropX x = x
    · simp only [elideFuel, he, ↓reduceIte]
    · simp only [elideFuel, he, ↓reduceIte]
      apply ih _ (replaceTrue_bound hd)
      change supportMass atoms (dropX x) ≤ n
      have ht := dropX_mass_lt hd he; omega

theorem elide_stable (x : Class ap) : dropX (elide x) = elide x := by
  apply elideFuel_stable
  · intro σ τ h
    rw [← repr_eval, ← repr_eval]
    exact propEval_local _ _ _ h
  · exact List.length_filter_le _ _

/-- Idempotence makes a second retry impossible. -/
theorem rho_retry_stops (x : Class ap) : ¬(U x ≠ U (U x)) := by
  rw [U_idempotent]; exact fun h => h rfl

theorem U_ofFormula (f : Formula (Fin ap)) : U (Class.ofFormula f) = Class.ofFormula (unfoldSyntax f) := by
  apply Class.ext; intro σ
  exact (unfold_substitution f σ).symm

theorem D_ofFormula (v : Letter (Fin ap)) (f : Formula (Fin ap)) :
    D v (Class.ofFormula f) = Class.ofFormula (stepSyntax v f) := by
  apply Class.ext; intro σ
  exact (step_substitution f v σ).symm

/-- Prefix derivatives, starting with the unfolded input. -/
def derivatives (w : Word (Fin ap)) (j : Nat) : Nat → Class ap → Class ap
  | 0, x => U x
  | n+1, x => derivatives w (j+1) n (delta (w j) x)

theorem derivatives_holds (w : Word (Fin ap)) (j n : Nat) (x : Class ap) :
    Holds w (j+n) (derivatives w j n x) ↔ Holds w j x := by
  induction n generalizing j x with
  | zero => exact U_holds x
  | succ n ih =>
    have h := ih (j+1) (delta (w j) x)
    have he : j + (n+1) = (j+1)+n := by omega
    rw [derivatives, he, h]
    exact (derivative x w j).symm

/-- The finite-window locality statement of STAGE1 §3. -/
theorem finite_window (f : Formula (Fin ap)) (hf : finite f)
    (w v : Word (Fin ap)) (j : Nat)
    (hw : ∀ k, j ≤ k → k ≤ j + horizon f → w k = v k) :
    Sat none w f j ↔ Sat none v f j := by
  induction f generalizing j with
  | tt | ff => rfl
  | ap a => simp [Sat, InRange, hw j (Nat.le_refl _) (by omega)]
  | neg f ih =>
    cases f <;> simp only [finite] at hf
    case ap a => simp [Sat, InRange, hw j (Nat.le_refl _) (by omega)]
  | conj f g ihf ihg | disj f g ihf ihg =>
    have h1 := ihf hf.1 j (fun k hk hkj => hw k hk (by simp only [horizon] at *; omega))
    have h2 := ihg hf.2 j (fun k hk hkj => hw k hk (by simp only [horizon] at *; omega))
    simp only [Sat]; rw [h1, h2]
  | next f ih =>
    have h1 := ih hf (j+1) (fun k hk hkj => hw k (by omega) (by simp only [horizon] at *; omega))
    simp only [Sat]; rw [h1]
  | _ => contradiction

/-- Positive NNF, with Boolean constants also allowed under literal negation. -/
def NNF : Formula α → Prop
  | .tt | .ff | .ap _ | .neg (.ap _) | .neg .tt | .neg .ff => True
  | .conj f g | .disj f g | .until f g | .release f g
  | .weakUntil f g | .strongRelease f g => NNF f ∧ NNF g
  | .next f | .eventually f | .globally f => NNF f
  | _ => False

def NNFClass (x : Class ap) : Prop := ∃ f, NNF f ∧ Class.ofFormula f = x

theorem nnf_positive (f : Formula (Fin ap)) (hf : NNF f) : Positive (Class.ofFormula f) := by
  intro σ τ hap hmodal hs
  change propEval σ f = true at hs
  change propEval τ f = true
  induction f with
  | tt => rfl
  | ff => exact hs
  | ap a =>
    change σ (.ap a) = true at hs
    change τ (.ap a) = true
    rwa [← hap (.ap a) trivial]
  | neg f ih =>
    cases f <;> simp only [NNF] at hf
    case tt => exact hs
    case ff => rfl
    case ap a => simpa only [propEval, hap (.ap a) trivial] using hs
  | conj f g ihf ihg =>
    simp only [propEval, Bool.and_eq_true] at hs ⊢
    exact ⟨ihf hf.1 hs.1, ihg hf.2 hs.2⟩
  | disj f g ihf ihg =>
    simp only [propEval, Bool.or_eq_true] at hs ⊢
    exact hs.elim (fun h => Or.inl (ihf hf.1 h)) (fun h => Or.inr (ihg hf.2 h))
  | impl _ _ | equiv _ _ | strongNext _ => contradiction
  | _ => exact hmodal _ (by simp [isAP]) hs

theorem unfold_nnf (f : Formula α) (h : NNF f) : NNF (unfoldSyntax f) := by
  induction f with
  | tt | ff | ap _ | next _ => exact h
  | neg f ih => cases f <;> simp_all [NNF, unfoldSyntax]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf h.1, ihg h.2⟩
  | eventually f ih | globally f ih => exact ⟨ih h, h⟩
  | «until» f g ihf ihg | weakUntil f g ihf ihg
  | release f g ihf ihg | strongRelease f g ihf ihg => exact ⟨ihg h.2, ihf h.1, h⟩
  | _ => contradiction

theorem U_positive (h : NNFClass x) : Positive (U x) := by
  obtain ⟨f, hf, rfl⟩ := h
  rw [U_ofFormula]
  exact nnf_positive _ (unfold_nnf f hf)

theorem replaceTrue_positive (h : Positive x) (p : Formula (Fin ap) → Prop) :
    Positive (replaceTrue p x) := by
  intro σ τ hap hmodal hs
  apply h _ _ _ _ hs
  · intro a ha; by_cases hp : p a <;> simp [hp, hap a ha]
  · intro a ha ht
    by_cases hp : p a
    · simp [hp]
    · simp only [hp, ↓reduceIte] at ht ⊢
      exact hmodal a ha ht

theorem elideFuel_positive (n : Nat) (h : Positive x) : Positive (elideFuel n x) := by
  induction n generalizing x with
  | zero => exact h
  | succ n ih =>
    simp only [elideFuel]; split
    · exact h
    · exact ih (replaceTrue_positive h _)

theorem elideFuel_weakens (n : Nat) (h : Positive x) : x ⇒ₚ elideFuel n x := by
  induction n generalizing x with
  | zero => exact implies_refl _
  | succ n ih =>
    simp only [elideFuel]; split
    · exact implies_refl _
    · apply implies_trans (replaceTrue_weakens h _ ?_) (ih (replaceTrue_positive h _))
      intro a ha hp
      cases a <;> simp_all [isAP, isX]

/-- STAGE2 §3 (1), the propositional weakening part, including the retry. -/
theorem rho_weakens {x : Class ap} (hx : NNFClass x) : U x ⇒ₚ rho x := by
  have pass : ∀ y : Class ap, Positive y → U y ⇒ₚ extractPass y := by
    intro y hy
    apply U_monotone
    apply implies_trans (replaceTrue_weakens hy _ ?_) (elideFuel_weakens _ (replaceTrue_positive hy _))
    intro a ha hp
    exact hp.1 ha
  unfold rho
  split
  · have h := pass (U x) (U_positive hx)
    rwa [U_idempotent] at h
  · obtain ⟨f, hf, rfl⟩ := hx
    exact pass _ (nnf_positive f hf)

/-- Function complement is used only in Boolean algebra lemmas. NNF
complement of a temporal class additionally dualizes its atom names. -/
def Class.compl (x : Class ap) : Class ap :=
  ⟨fun σ => !(x σ), .neg x.repr, by funext σ; simp [propEval, repr_eval]⟩

theorem U_top : U (Class.top : Class ap) = Class.top := by apply Class.ext; intro σ; rfl
theorem delta_top (v : Letter (Fin ap)) : delta v Class.top = Class.top := by apply Class.ext; intro σ; rfl
theorem delta_bot (v : Letter (Fin ap)) : delta v Class.bot = Class.bot := by apply Class.ext; intro σ; rfl

theorem U_meet (x y : Class ap) : U (meet x y) = meet (U x) (U y) := by apply Class.ext; intro σ; rfl
theorem U_join (x y : Class ap) : U (join x y) = join (U x) (U y) := by apply Class.ext; intro σ; rfl
theorem delta_meet (v : Letter (Fin ap)) (x y : Class ap) :
    delta v (meet x y) = meet (delta v x) (delta v y) := by apply Class.ext; intro σ; rfl
theorem delta_join (v : Letter (Fin ap)) (x y : Class ap) :
    delta v (join x y) = join (delta v x) (delta v y) := by apply Class.ext; intro σ; rfl

theorem delta_monotone (v : Letter (Fin ap)) (h : x ⇒ₚ y) : delta v x ⇒ₚ delta v y :=
  U_monotone (D_monotone v (U_monotone h))

theorem derivatives_monotone (w : Word (Fin ap)) (j n : Nat) (h : x ⇒ₚ y) :
    derivatives w j n x ⇒ₚ derivatives w j n y := by
  induction n generalizing j x y with
  | zero => exact U_monotone h
  | succ n ih => exact ih _ (delta_monotone _ h)

theorem derivatives_U (w : Word (Fin ap)) (j n : Nat) (x : Class ap) :
    derivatives w j n (U x) = derivatives w j n x := by
  cases n with
  | zero => exact U_idempotent x
  | succ n => simp only [derivatives, delta, U_idempotent]

theorem derivatives_top (w : Word (Fin ap)) (j n : Nat) :
    derivatives w j n Class.top = Class.top := by
  induction n generalizing j with
  | zero => exact U_top
  | succ n ih => simp only [derivatives, delta_top]; exact ih _

theorem derivatives_meet (w : Word (Fin ap)) (j n : Nat) (x y : Class ap) :
    derivatives w j n (meet x y) = meet (derivatives w j n x) (derivatives w j n y) := by
  induction n generalizing j x y with
  | zero => exact U_meet x y
  | succ n ih => simp only [derivatives, delta_meet]; exact ih _ _ _

/-- A finite good certificate is propositional truth, not just LTL truth. -/
def EventuallyTop (w : Word (Fin ap)) (j : Nat) (x : Class ap) : Prop :=
  ∃ n, derivatives w j n x = Class.top

theorem top_of_implied (h : Class.top ⇒ₚ x) : x = Class.top := by
  apply Class.ext; intro σ; exact h σ rfl

theorem EventuallyTop.mono (h : EventuallyTop w j x) (hxy : x ⇒ₚ y) : EventuallyTop w j y := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, top_of_implied ?_⟩
  have ht := derivatives_monotone w j n hxy
  rwa [hn] at ht

theorem EventuallyTop.of_U (h : EventuallyTop w j (U x)) : EventuallyTop w j x := by
  simpa only [EventuallyTop, derivatives_U] using h

theorem EventuallyTop.to_U (h : EventuallyTop w j x) : EventuallyTop w j (U x) := by
  simpa only [EventuallyTop, derivatives_U] using h

theorem EventuallyTop.step : EventuallyTop w j x ↔ EventuallyTop w (j+1) (delta (w j) x) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      refine ⟨0, ?_⟩
      change U (U (D (w j) (U x))) = Class.top
      change U x = Class.top at hn
      rw [hn]
      rfl
    | succ n => exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n+1, hn⟩

theorem derivatives_add (w : Word (Fin ap)) (j n k : Nat) (x : Class ap) :
    derivatives w j (n+k) x = derivatives w (j+n) k (derivatives w j n x) := by
  induction n generalizing j x with
  | zero => simpa only [Nat.zero_add, Nat.add_zero, derivatives] using (derivatives_U w j k x).symm
  | succ n ih =>
    have he : n+1+k = (n+k)+1 := by omega
    rw [he, derivatives, ih]
    have hj : j+1+n = j+(n+1) := by omega
    rw [hj]; rfl

theorem derivatives_top_persists (h : derivatives w j n x = Class.top) (hm : n ≤ m) :
    derivatives w j m x = Class.top := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [derivatives_add, h, derivatives_top]

theorem EventuallyTop.meet (hx : EventuallyTop w j x) (hy : EventuallyTop w j y) :
    EventuallyTop w j (meet x y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  refine ⟨n+m, ?_⟩
  rw [derivatives_meet, derivatives_top_persists hn (by omega),
    derivatives_top_persists hm (by omega)]
  apply Class.ext; intro σ; rfl

theorem EventuallyTop.join_left (h : EventuallyTop w j x) : EventuallyTop w j (join x y) :=
  h.mono (fun σ hx => by change x σ || y σ = true; simp [hx])

theorem EventuallyTop.join_right (h : EventuallyTop w j y) : EventuallyTop w j (join x y) :=
  h.mono (fun σ hy => by change x σ || y σ = true; simp [hy])

theorem finite_implies_cosafety (f : Formula α) (h : finite f) : cosafety f := by
  induction f with
  | tt | ff | ap _ => trivial
  | neg f ih => cases f <;> simp_all [finite, cosafety]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf h.1, ihg h.2⟩
  | next f ih => exact ih h
  | _ => contradiction

theorem U_eventually (f : Formula (Fin ap)) : U (Class.ofFormula (.eventually f)) =
    join (U (Class.ofFormula f)) (Class.ofFormula (.eventually f)) := by
  apply Class.ext; intro σ
  change (propEval σ (unfoldSyntax f) || σ (.eventually f)) =
    (propEval (unfoldAtom σ) f || σ (.eventually f))
  rw [unfold_substitution]

theorem U_until (f g : Formula (Fin ap)) : U (Class.ofFormula (.until f g)) =
    join (U (Class.ofFormula g)) (meet (U (Class.ofFormula f)) (Class.ofFormula (.until f g))) := by
  apply Class.ext; intro σ
  change (propEval σ (unfoldSyntax g) || (propEval σ (unfoldSyntax f) && σ (.until f g))) =
    (propEval (unfoldAtom σ) g || (propEval (unfoldAtom σ) f && σ (.until f g)))
  rw [unfold_substitution, unfold_substitution]

theorem U_strongRelease (f g : Formula (Fin ap)) : U (Class.ofFormula (.strongRelease f g)) =
    meet (U (Class.ofFormula g)) (join (U (Class.ofFormula f)) (Class.ofFormula (.strongRelease f g))) := by
  apply Class.ext; intro σ
  change (propEval σ (unfoldSyntax g) && (propEval σ (unfoldSyntax f) || σ (.strongRelease f g))) =
    (propEval (unfoldAtom σ) g && (propEval (unfoldAtom σ) f || σ (.strongRelease f g)))
  rw [unfold_substitution, unfold_substitution]

theorem D_meet (v : Letter (Fin ap)) (x y : Class ap) : D v (meet x y) = meet (D v x) (D v y) := by
  apply Class.ext; intro σ; rfl

theorem D_join (v : Letter (Fin ap)) (x y : Class ap) : D v (join x y) = join (D v x) (D v y) := by
  apply Class.ext; intro σ; rfl

theorem delta_eventually (v : Letter (Fin ap)) (f : Formula (Fin ap)) :
    delta v (Class.ofFormula (.eventually f)) =
      join (delta v (Class.ofFormula f)) (U (Class.ofFormula (.eventually f))) := by
  have hd : D v (Class.ofFormula (.eventually f)) = Class.ofFormula (.eventually f) := by
    apply Class.ext; intro σ; rfl
  rw [delta, U_eventually, D_join, U_join, hd, U_eventually]
  rfl

theorem delta_until (v : Letter (Fin ap)) (f g : Formula (Fin ap)) :
    delta v (Class.ofFormula (.until f g)) =
      join (delta v (Class.ofFormula g))
        (meet (delta v (Class.ofFormula f)) (U (Class.ofFormula (.until f g)))) := by
  have hd : D v (Class.ofFormula (.until f g)) = Class.ofFormula (.until f g) := by
    apply Class.ext; intro σ; rfl
  rw [delta, U_until, D_join, D_meet, U_join, U_meet, hd, U_until]
  rfl

theorem delta_strongRelease (v : Letter (Fin ap)) (f g : Formula (Fin ap)) :
    delta v (Class.ofFormula (.strongRelease f g)) =
      meet (delta v (Class.ofFormula g))
        (join (delta v (Class.ofFormula f)) (U (Class.ofFormula (.strongRelease f g)))) := by
  have hd : D v (Class.ofFormula (.strongRelease f g)) = Class.ofFormula (.strongRelease f g) := by
    apply Class.ext; intro σ; rfl
  rw [delta, U_strongRelease, D_meet, D_join, U_meet, U_join, hd, U_strongRelease]
  rfl

theorem cosafety_witness (f : Formula (Fin ap)) (hf : cosafety f)
    (w : Word (Fin ap)) (j : Nat) (hs : Sat none w f j) :
    EventuallyTop w j (Class.ofFormula f) := by
  induction f generalizing j with
  | tt => exact ⟨0, rfl⟩
  | ff => exact False.elim hs.2
  | ap a =>
    refine ⟨1, ?_⟩
    apply Class.ext; intro σ
    change w j a = true
    exact hs.2
  | neg f ih =>
    cases f <;> simp only [cosafety] at hf
    case ap a =>
      refine ⟨1, ?_⟩
      apply Class.ext; intro σ
      change !(w j a) = true
      have he : w j a = false := Bool.eq_false_iff.mpr (fun ht => hs.2 ⟨trivial, ht⟩)
      simp [he]
  | conj f g ihf ihg => exact (ihf hf.1 j hs.2.1).meet (ihg hf.2 j hs.2.2)
  | disj f g ihf ihg =>
    rcases hs.2 with h | h
    · exact (ihf hf.1 j h).join_left (y := Class.ofFormula g)
    · exact (ihg hf.2 j h).join_right (x := Class.ofFormula f)
  | next f ih =>
    apply EventuallyTop.step.mpr
    have he : delta (w j) (Class.ofFormula (.next f)) = U (Class.ofFormula f) := by
      apply Class.ext; intro σ; rfl
    rw [he]
    exact (ih hf (j+1) (hs.2.resolve_left (fun h => h trivial))).to_U
  | eventually f ih =>
    obtain ⟨k, hjk, hrange, hk⟩ := hs.2
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
    have hk' : Sat none w f (j+d) := hd ▸ hk
    clear hs hjk hk hd hrange k
    induction d generalizing j with
    | zero =>
      apply EventuallyTop.of_U
      rw [U_eventually]
      exact (ih hf j hk').to_U.join_left
    | succ d ihd =>
      apply EventuallyTop.step.mpr
      rw [delta_eventually]
      have ht := ihd (j+1) (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hk')
      exact ht.to_U.join_right
  | «until» f g ihf ihg =>
    obtain ⟨k, hjk, hrange, hg, hall⟩ := hs.2
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
    have hg' : Sat none w g (j+d) := hd ▸ hg
    have hall' : ∀ i, j ≤ i → i < j+d → Sat none w f i := by simpa only [← hd] using hall
    clear hs hjk hg hall hd hrange k
    induction d generalizing j with
    | zero =>
      apply EventuallyTop.of_U
      rw [U_until]
      exact (ihg hf.2 j hg').to_U.join_left
    | succ d ihd =>
      apply EventuallyTop.step.mpr
      rw [delta_until]
      have ht := ihd (j+1)
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hg')
        (fun i hi hik => hall' i (by omega) (by omega))
      have hfirst := EventuallyTop.step.mp (ihf hf.1 j (hall' j (Nat.le_refl _) (by omega)))
      exact (hfirst.meet ht.to_U).join_right
  | strongRelease f g ihf ihg =>
    have he := (Tlsf.Rewrites.strongRelease_eq (len := none) (w := w) (a := f) (b := g) (j := j) trivial).mp hs
    obtain ⟨k, hjk, hrange, hfg, hall⟩ := he.2
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
    have hfg' : Sat none w f (j+d) ∧ Sat none w g (j+d) := hd ▸ hfg.2
    have hall' : ∀ i, j ≤ i → i < j+d → Sat none w g i := by simpa only [← hd] using hall
    clear hs he hjk hfg hall hd hrange k
    induction d generalizing j with
    | zero =>
      apply EventuallyTop.of_U
      rw [U_strongRelease]
      exact (ihg hf.2 j hfg'.2).to_U.meet (ihf hf.1 j hfg'.1).to_U.join_left
    | succ d ihd =>
      apply EventuallyTop.step.mpr
      rw [delta_strongRelease]
      have ht := ihd (j+1)
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hfg')
        (fun i hi hik => hall' i (by omega) (by omega))
      have hg := EventuallyTop.step.mp (ihg hf.2 j (hall' j (Nat.le_refl _) (by omega)))
      exact hg.meet ht.to_U.join_right
  | _ => contradiction

theorem U_compl (x : Class ap) : U x.compl = (U x).compl := by apply Class.ext; intro σ; rfl

theorem delta_compl (v : Letter (Fin ap)) (x : Class ap) :
    delta v x.compl = (delta v x).compl := by apply Class.ext; intro σ; rfl

theorem derivatives_compl (w : Word (Fin ap)) (j n : Nat) (x : Class ap) :
    derivatives w j n x.compl = (derivatives w j n x).compl := by
  induction n generalizing j x with
  | zero => exact U_compl x
  | succ n ih => simp only [derivatives, delta_compl]; exact ih _ _

def EventuallyBot (w : Word (Fin ap)) (j : Nat) (x : Class ap) : Prop :=
  ∃ n, derivatives w j n x = Class.bot

theorem compl_eq_top (x : Class ap) : x.compl = Class.top ↔ x = Class.bot := by
  constructor <;> intro h <;> apply Class.ext <;> intro σ
  · have ht := congrArg (fun y : Class ap => y σ) h
    change !(x σ) = true at ht
    change x σ = false
    simpa using ht
  · have ht := congrArg (fun y : Class ap => y σ) h
    change x σ = false at ht
    change !(x σ) = true
    simp [ht]

theorem eventuallyBot_iff (x : Class ap) :
    EventuallyBot w j x ↔ EventuallyTop w j x.compl := by
  simp only [EventuallyBot, EventuallyTop, derivatives_compl, compl_eq_top]

theorem EventuallyBot.step : EventuallyBot w j x ↔ EventuallyBot w (j+1) (delta (w j) x) := by
  rw [eventuallyBot_iff, EventuallyTop.step, delta_compl, ← eventuallyBot_iff]

theorem EventuallyBot.of_U (h : EventuallyBot w j (U x)) : EventuallyBot w j x := by
  simpa only [EventuallyBot, derivatives_U] using h

theorem EventuallyBot.to_U (h : EventuallyBot w j x) : EventuallyBot w j (U x) := by
  simpa only [EventuallyBot, derivatives_U] using h

theorem EventuallyBot.join (hx : EventuallyBot w j x) (hy : EventuallyBot w j y) :
    EventuallyBot w j (join x y) := by
  rw [eventuallyBot_iff] at *
  have he : (Class.join x y).compl = meet x.compl y.compl := by
    apply Class.ext; intro σ; exact Bool.not_or ..
  rw [he]; exact hx.meet hy

theorem EventuallyBot.meet_left (h : EventuallyBot w j x) : EventuallyBot w j (meet x y) := by
  rw [eventuallyBot_iff] at *
  apply h.mono
  intro σ hx
  change (!(x σ && y σ)) = true
  change (!(x σ)) = true at hx
  have hx' : x σ = false := by simpa using hx
  simp [hx']

theorem EventuallyBot.meet_right (h : EventuallyBot w j y) : EventuallyBot w j (meet x y) := by
  rw [eventuallyBot_iff] at *
  apply h.mono
  intro σ hy
  change (!(x σ && y σ)) = true
  change (!(y σ)) = true at hy
  have hy' : y σ = false := by simpa using hy
  simp [hy']

theorem U_globally (f : Formula (Fin ap)) : U (Class.ofFormula (.globally f)) =
    meet (U (Class.ofFormula f)) (Class.ofFormula (.globally f)) := by
  apply Class.ext; intro σ
  change (propEval σ (unfoldSyntax f) && σ (.globally f)) =
    (propEval (unfoldAtom σ) f && σ (.globally f))
  rw [unfold_substitution]

theorem U_release (f g : Formula (Fin ap)) : U (Class.ofFormula (.release f g)) =
    meet (U (Class.ofFormula g)) (join (U (Class.ofFormula f)) (Class.ofFormula (.release f g))) := by
  apply Class.ext; intro σ
  change (propEval σ (unfoldSyntax g) && (propEval σ (unfoldSyntax f) || σ (.release f g))) =
    (propEval (unfoldAtom σ) g && (propEval (unfoldAtom σ) f || σ (.release f g)))
  rw [unfold_substitution, unfold_substitution]

theorem U_weakUntil (f g : Formula (Fin ap)) : U (Class.ofFormula (.weakUntil f g)) =
    join (U (Class.ofFormula g)) (meet (U (Class.ofFormula f)) (Class.ofFormula (.weakUntil f g))) := by
  apply Class.ext; intro σ
  change (propEval σ (unfoldSyntax g) || (propEval σ (unfoldSyntax f) && σ (.weakUntil f g))) =
    (propEval (unfoldAtom σ) g || (propEval (unfoldAtom σ) f && σ (.weakUntil f g)))
  rw [unfold_substitution, unfold_substitution]

theorem delta_globally (v : Letter (Fin ap)) (f : Formula (Fin ap)) :
    delta v (Class.ofFormula (.globally f)) =
      meet (delta v (Class.ofFormula f)) (U (Class.ofFormula (.globally f))) := by
  have hd : D v (Class.ofFormula (.globally f)) = Class.ofFormula (.globally f) := by
    apply Class.ext; intro σ; rfl
  rw [delta, U_globally, D_meet, U_meet, hd, U_globally]
  rfl

theorem delta_release (v : Letter (Fin ap)) (f g : Formula (Fin ap)) :
    delta v (Class.ofFormula (.release f g)) =
      meet (delta v (Class.ofFormula g))
        (join (delta v (Class.ofFormula f)) (U (Class.ofFormula (.release f g)))) := by
  have hd : D v (Class.ofFormula (.release f g)) = Class.ofFormula (.release f g) := by
    apply Class.ext; intro σ; rfl
  rw [delta, U_release, D_meet, D_join, U_meet, U_join, hd, U_release]
  rfl

theorem delta_weakUntil (v : Letter (Fin ap)) (f g : Formula (Fin ap)) :
    delta v (Class.ofFormula (.weakUntil f g)) =
      join (delta v (Class.ofFormula g))
        (meet (delta v (Class.ofFormula f)) (U (Class.ofFormula (.weakUntil f g)))) := by
  have hd : D v (Class.ofFormula (.weakUntil f g)) = Class.ofFormula (.weakUntil f g) := by
    apply Class.ext; intro σ; rfl
  rw [delta, U_weakUntil, D_join, D_meet, U_join, U_meet, hd, U_weakUntil]
  rfl

/-- STAGE1 §3: every violation of safety has a propositional bad prefix. -/
theorem safety_bad_prefix (f : Formula (Fin ap)) (hf : safety f)
    (w : Word (Fin ap)) (j : Nat) (hs : ¬Sat none w f j) :
    EventuallyBot w j (Class.ofFormula f) := by
  induction f generalizing j with
  | tt => exact False.elim (hs ⟨trivial, trivial⟩)
  | ff => exact ⟨0, rfl⟩
  | ap a =>
    refine ⟨1, ?_⟩
    apply Class.ext; intro σ
    change w j a = false
    exact Bool.eq_false_iff.mpr (fun ht => hs ⟨trivial, ht⟩)
  | neg f ih =>
    cases f <;> simp only [safety] at hf
    case ap a =>
      refine ⟨1, ?_⟩
      apply Class.ext; intro σ
      change (!(w j a)) = false
      have he : w j a = true := by
        cases he : w j a
        · exact False.elim (hs ⟨trivial, fun h => Bool.noConfusion (he.symm.trans h.2)⟩)
        · rfl
      simp [he]
  | conj f g ihf ihg =>
    by_cases h : Sat none w f j
    · have hg : ¬Sat none w g j := fun hg => hs ⟨trivial, h, hg⟩
      exact (ihg hf.2 j hg).meet_right (x := Class.ofFormula f)
    · exact (ihf hf.1 j h).meet_left (y := Class.ofFormula g)
  | disj f g ihf ihg =>
    exact (ihf hf.1 j (fun h => hs ⟨trivial, Or.inl h⟩)).join
      (ihg hf.2 j (fun h => hs ⟨trivial, Or.inr h⟩))
  | next f ih =>
    apply EventuallyBot.step.mpr
    have he : delta (w j) (Class.ofFormula (.next f)) = U (Class.ofFormula f) := by
      apply Class.ext; intro σ; rfl
    rw [he]
    exact (ih hf (j+1) (fun h => hs ⟨trivial, Or.inr h⟩)).to_U
  | globally f ih =>
    have hex : ∃ k, j ≤ k ∧ ¬Sat none w f k := by
      apply Classical.byContradiction; intro hn
      apply hs; refine ⟨trivial, ?_⟩
      intro k hk _
      exact Classical.byContradiction (fun h => hn ⟨k, hk, h⟩)
    obtain ⟨k, hjk, hk⟩ := hex
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
    have hk' : ¬Sat none w f (j+d) := hd ▸ hk
    clear hs hjk hk hd k
    induction d generalizing j with
    | zero =>
      apply EventuallyBot.of_U
      rw [U_globally]
      exact (ih hf j hk').to_U.meet_left
    | succ d ihd =>
      apply EventuallyBot.step.mpr
      rw [delta_globally]
      have ht := ihd (j+1) (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hk')
      exact ht.to_U.meet_right
  | release f g ihf ihg =>
    have hu : UntilAt none j (fun k => ¬Sat none w f k) (fun k => ¬Sat none w g k) :=
      Classical.byContradiction (fun hn => hs ⟨trivial, hn⟩)
    obtain ⟨k, hjk, hrange, hg, hall⟩ := hu
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
    have hg' : ¬Sat none w g (j+d) := hd ▸ hg
    have hall' : ∀ i, j ≤ i → i < j+d → ¬Sat none w f i := by simpa only [← hd] using hall
    clear hs hjk hg hall hd hrange k
    induction d generalizing j with
    | zero =>
      apply EventuallyBot.of_U
      rw [U_release]
      exact (ihg hf.2 j hg').to_U.meet_left
    | succ d ihd =>
      apply EventuallyBot.step.mpr
      rw [delta_release]
      have ht := ihd (j+1)
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hg')
        (fun i hi hik => hall' i (by omega) (by omega))
      have hfirst := EventuallyBot.step.mp (ihf hf.1 j (hall' j (Nat.le_refl _) (by omega)))
      exact (hfirst.join ht.to_U).meet_right
  | weakUntil f g ihf ihg =>
    have hn : ¬(UntilAt none j (Sat none w f) (Sat none w g) ∨ AllFuture none j (Sat none w f)) :=
      fun h => hs ⟨trivial, h⟩
    have hu := (Tlsf.Rewrites.not_weakUntil_dual (len := none) (j := j)
      (p := fun k => ¬Sat none w f k) (q := fun k => ¬Sat none w g k)).mp
      (by simpa only [Classical.not_not] using hn)
    obtain ⟨k, hjk, hrange, hfg, hall⟩ := hu
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
    have hfg' : ¬Sat none w f (j+d) ∧ ¬Sat none w g (j+d) := hd ▸ hfg
    have hall' : ∀ i, j ≤ i → i < j+d → ¬Sat none w g i := by simpa only [← hd] using hall
    clear hs hn hjk hfg hall hd hrange k
    induction d generalizing j with
    | zero =>
      apply EventuallyBot.of_U
      rw [U_weakUntil]
      exact (ihg hf.2 j hfg'.2).to_U.join (ihf hf.1 j hfg'.1).to_U.meet_left
    | succ d ihd =>
      apply EventuallyBot.step.mpr
      rw [delta_weakUntil]
      have ht := ihd (j+1)
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hfg')
        (fun i hi hik => hall' i (by omega) (by omega))
      have hg := EventuallyBot.step.mp (ihg hf.2 j (hall' j (Nat.le_refl _) (by omega)))
      exact hg.join ht.to_U.meet_right
  | _ => contradiction

/-- Auxiliary Boolean closure of the finite grammar; this permits the
unsimplified `¬true` produced by a simultaneous raw step. -/
def Bounded : Formula α → Prop
  | .tt | .ff | .ap _ => True
  | .neg f => Bounded f
  | .conj f g | .disj f g | .impl f g | .equiv f g => Bounded f ∧ Bounded g
  | .next f | .strongNext f => Bounded f
  | _ => False

theorem finite_bounded (f : Formula α) (hf : finite f) : Bounded f := by
  induction f with
  | tt | ff | ap _ => trivial
  | neg f ih => cases f <;> simp_all [finite, Bounded]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | next f ih => exact ih hf
  | _ => contradiction

theorem unfold_bounded (f : Formula α) (hf : Bounded f) : unfoldSyntax f = f := by
  induction f with
  | tt | ff | ap _ | next _ | strongNext _ => rfl
  | neg f ih => simp only [unfoldSyntax, ih hf]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [unfoldSyntax, ihf hf.1, ihg hf.2]
  | _ => contradiction

theorem step_bounded (f : Formula α) (hf : Bounded f) (v : Letter α) : Bounded (stepSyntax v f) := by
  induction f with
  | tt | ff => trivial
  | ap a => cases h : v a <;> simp [stepSyntax, h, Bounded]
  | neg f ih => exact ih hf
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    exact ⟨ihf hf.1, ihg hf.2⟩
  | next f | strongNext f => exact hf
  | _ => contradiction

def rawSyntax (w : Word α) (j : Nat) : Nat → Formula α → Formula α
  | 0, f => f
  | n+1, f => rawSyntax w (j+1) n (stepSyntax (w j) f)

theorem rawSyntax_tt (w : Word α) (j n : Nat) : rawSyntax w j n .tt = .tt := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => exact ih _

theorem rawSyntax_ff (w : Word α) (j n : Nat) : rawSyntax w j n .ff = .ff := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => exact ih _

theorem rawSyntax_neg (w : Word α) (j n : Nat) (f : Formula α) :
    rawSyntax w j n (.neg f) = .neg (rawSyntax w j n f) := by
  induction n generalizing j f with
  | zero => rfl
  | succ n ih => exact ih _ _

theorem rawSyntax_binary (w : Word α) (j n : Nat) (f g : Formula α) :
    rawSyntax w j n (.conj f g) = .conj (rawSyntax w j n f) (rawSyntax w j n g) ∧
    rawSyntax w j n (.disj f g) = .disj (rawSyntax w j n f) (rawSyntax w j n g) ∧
    rawSyntax w j n (.impl f g) = .impl (rawSyntax w j n f) (rawSyntax w j n g) ∧
    rawSyntax w j n (.equiv f g) = .equiv (rawSyntax w j n f) (rawSyntax w j n g) := by
  induction n generalizing j f g with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih => exact ih _ _ _

theorem derivatives_bounded (w : Word (Fin ap)) (j n : Nat)
    (f : Formula (Fin ap)) (hf : Bounded f) :
    derivatives w j n (Class.ofFormula f) = Class.ofFormula (rawSyntax w j n f) := by
  induction n generalizing j f with
  | zero => rw [derivatives, U_ofFormula, unfold_bounded f hf]; rfl
  | succ n ih =>
    have he : delta (w j) (Class.ofFormula f) = Class.ofFormula (stepSyntax (w j) f) := by
      rw [delta, U_ofFormula, unfold_bounded f hf, D_ofFormula, U_ofFormula,
        unfold_bounded _ (step_bounded f hf _)]
    rw [derivatives, he]
    exact ih _ _ (step_bounded f hf _)

/-- After the last possible finite-window position, the raw expression has
no remaining dependence on boundary atom values. -/
theorem bounded_constant_eval (f : Formula (Fin ap)) (hf : Bounded f)
    (w : Word (Fin ap)) (j n : Nat) (hn : horizon f < n) (σ : Assignment ap) :
    propEval σ (rawSyntax w j n f) = true ↔ Sat none w f j := by
  induction f generalizing j n with
  | tt => simp [rawSyntax_tt, propEval, Sat, InRange]
  | ff => simp [rawSyntax_ff, propEval, Sat, InRange]
  | ap a =>
    cases n with
    | zero => omega
    | succ n =>
      cases he : w j a <;> simp [rawSyntax, stepSyntax, he, rawSyntax_tt, rawSyntax_ff, propEval, Sat, InRange]
  | neg f ih =>
    rw [rawSyntax_neg]
    simpa only [propEval, Bool.not_eq_true', Bool.eq_false_iff, Sat, InRange, true_and] using not_congr (ih hf j n hn)
  | conj f g ihf ihg =>
    rw [(rawSyntax_binary w j n f g).1]
    simp only [propEval, Bool.and_eq_true, Sat, InRange, true_and,
      ihf hf.1 j n (by simp only [horizon] at hn; omega),
      ihg hf.2 j n (by simp only [horizon] at hn; omega)]
  | disj f g ihf ihg =>
    rw [(rawSyntax_binary w j n f g).2.1]
    simp only [propEval, Bool.or_eq_true, Sat, InRange, true_and,
      ihf hf.1 j n (by simp only [horizon] at hn; omega),
      ihg hf.2 j n (by simp only [horizon] at hn; omega)]
  | impl f g ihf ihg | equiv f g ihf ihg =>
    have hb := rawSyntax_binary w j n f g
    first | rw [hb.2.2.1] | rw [hb.2.2.2]
    have h1 := ihf hf.1 j n (by simp only [horizon] at hn; omega)
    have h2 := ihg hf.2 j n (by simp only [horizon] at hn; omega)
    simp only [propEval, Sat, InRange, true_and]
    cases hfe : propEval σ (rawSyntax w j n f) <;>
      cases hge : propEval σ (rawSyntax w j n g) <;> simp_all
  | next f ih | strongNext f ih =>
    cases n with
    | zero => omega
    | succ n =>
      change propEval σ (rawSyntax w (j+1) n f) = true ↔ _
      simpa only [Sat, InRange, true_and, not_true_eq_false, false_or] using
        ih hf (j+1) n (by simp only [horizon] at hn; omega)
  | _ => contradiction

/-- STAGE1 §3: at `h+1` letters a finite window is its actual truth constant. -/
theorem finite_window_constant (f : Formula (Fin ap)) (hf : finite f)
    (w : Word (Fin ap)) (j : Nat) :
    derivatives w j (horizon f + 1) (Class.ofFormula f) =
      (if Sat none w f j then Class.top else Class.bot) := by
  rw [derivatives_bounded _ _ _ _ (finite_bounded f hf)]
  apply Class.ext; intro σ
  have he := bounded_constant_eval f (finite_bounded f hf) w j (horizon f+1) (by omega) σ
  by_cases hs : Sat none w f j
  · simp only [hs, ↓reduceIte]
    exact he.mpr hs
  · simp only [hs, ↓reduceIte]
    exact Bool.eq_false_iff.mpr (fun ht => hs (he.mp ht))

theorem U_uses (h : Uses (U x) t) :
    ∃ a, Uses x a ∧ Uses (Class.ofFormula (unfoldSyntax a)) t := by
  apply Classical.byContradiction; intro hn
  obtain ⟨σ, b, hb⟩ := h
  apply hb
  change x (unfoldAtom (setAtom σ t b)) = x (unfoldAtom σ)
  apply support_locality
  intro a ha
  have hh : ¬Uses (Class.ofFormula (unfoldSyntax a)) t := fun hu => hn ⟨a, ha, hu⟩
  exact not_uses hh σ b

theorem cosafety_atoms (f : Formula (Fin ap)) (hf : cosafety f)
    (a : Formula (Fin ap)) (ha : a ∈ modalAtoms f) : cosafety a := by
  induction f with
  | tt | ff => contradiction
  | ap b =>
    have he : a = .ap b := List.mem_singleton.mp ha
    subst a; exact hf
  | neg f ih => cases f <;> simp_all [cosafety, modalAtoms]
  | conj f g ihf ihg | disj f g ihf ihg =>
    rcases List.mem_append.mp ha with h | h
    · exact ihf hf.1 h
    · exact ihg hf.2 h
  | next f | eventually f | «until» f g | strongRelease f g =>
    have he : a = _ := List.mem_singleton.mp ha
    exact he ▸ hf
  | _ => contradiction

theorem unfold_cosafety (f : Formula α) (h : cosafety f) : cosafety (unfoldSyntax f) := by
  induction f with
  | tt | ff | ap _ | next _ => exact h
  | neg f ih => cases f <;> simp_all [cosafety, unfoldSyntax]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf h.1, ihg h.2⟩
  | eventually f ih => exact ⟨ih h, h⟩
  | «until» f g ihf ihg | strongRelease f g ihf ihg => exact ⟨ihg h.2, ihf h.1, h⟩
  | _ => contradiction

theorem U_cosafety (h : HasTag cosafety x) : HasTag cosafety (U x) := by
  intro t ht
  obtain ⟨a, ha, hat⟩ := U_uses ht
  have hd : (Class.ofFormula (unfoldSyntax a)).DependsOn (modalAtoms (unfoldSyntax a)) :=
    fun σ τ hh => propEval_local _ _ _ hh
  exact cosafety_atoms _ (unfold_cosafety a (h a ha)) t (uses_in_bound hd hat)

theorem replaceTrue_tag (h : HasTag tag x) (p : Formula (Fin ap) → Prop) :
    HasTag tag (replaceTrue p x) := fun a ha => h a (replaceTrue_uses ha).1

theorem reduce_cosafety (x : Class ap) : HasTag cosafety (reduce x) := by
  intro a ha
  have hn := (replaceTrue_uses ha).2
  by_cases hap : isAP a
  · cases a <;> simp_all [isAP, cosafety]
  · exact Classical.byContradiction (fun hco => hn ⟨hap, hco⟩)

theorem elideFuel_tag (n : Nat) (h : HasTag tag x) : HasTag tag (elideFuel n x) := by
  induction n generalizing x with
  | zero => exact h
  | succ n ih =>
    simp only [elideFuel]; split
    · exact h
    · exact ih (replaceTrue_tag h _)

theorem rho_cosafety (x : Class ap) : HasTag cosafety (rho x) := by
  have hp : ∀ y : Class ap, HasTag cosafety (extractPass y) :=
    fun y => U_cosafety (elideFuel_tag _ (reduce_cosafety y))
  unfold rho; split <;> apply hp

/-- STAGE2 §3 (1), unfoldedness and co-safety of every extracted seed. -/
theorem rho_unfolded (x : Class ap) : U (rho x) = rho x := by
  unfold rho; split <;> exact U_idempotent _

def supportList (x : Class ap) : List (Formula (Fin ap)) :=
  (modalAtoms x.repr).filter (fun a => decide (Uses x a))

theorem mem_supportList (x : Class ap) (a : Formula (Fin ap)) : a ∈ supportList x ↔ Uses x a := by
  simp only [supportList, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro h
    refine ⟨uses_in_bound ?_ h, h⟩
    intro σ τ he
    rw [← repr_eval, ← repr_eval]
    exact propEval_local _ _ _ he

def allMeet : List (Class ap) → Class ap
  | [] => Class.top
  | x :: xs => meet x (allMeet xs)

theorem allMeet_true (xs : List (Class ap)) (σ : Assignment ap) :
    allMeet xs σ = true ↔ ∀ x, x ∈ xs → x σ = true := by
  induction xs with
  | nil => simp [allMeet, Class.top, Class.ofFormula, propEval]
  | cons x xs ih =>
    change (x σ && allMeet xs σ) = true ↔ _
    simp only [Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]

theorem allMeet_witness (xs : List (Class ap))
    (h : ∀ x, x ∈ xs → EventuallyTop w j x) : EventuallyTop w j (allMeet xs) := by
  induction xs with
  | nil => exact ⟨0, U_top⟩
  | cons x xs ih =>
    exact (h x (by simp)).meet (ih (fun y hy => h y (by simp [hy])))

/-- A sufficient positive branch: assign current APs exactly, keep every
true modal atom, and impose nothing on false modal atoms. -/
def goodFactor (σ : Assignment ap) (a : Formula (Fin ap)) : Class ap :=
  if isAP a then
    if σ a then Class.ofFormula a else (Class.ofFormula a).compl
  else if σ a then Class.ofFormula a else Class.top

theorem propEval_mem_atom (f : Formula (Fin ap)) (a : Formula (Fin ap))
    (ha : a ∈ modalAtoms f) (σ : Assignment ap) : propEval σ a = σ a := by
  induction f with
  | tt | ff => contradiction
  | ap p | next f | strongNext f | eventually f | globally f
  | «until» f g | release f g | weakUntil f g | strongRelease f g =>
    have he := List.mem_singleton.mp ha
    subst a; rfl
  | neg f ih => exact ih ha
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    exact (List.mem_append.mp ha).elim ihf ihg

theorem propEval_used_atom (h : Uses x a) (σ : Assignment ap) : propEval σ a = σ a := by
  apply propEval_mem_atom x.repr a _ σ
  have hd : x.DependsOn (modalAtoms x.repr) := by
    intro τ υ he
    rw [← repr_eval, ← repr_eval]
    exact propEval_local _ _ _ he
  exact uses_in_bound hd h

theorem goodBranch_implies (x : Class ap) (hx : Positive x) (σ : Assignment ap)
    (hs : x σ = true) : allMeet ((supportList x).map (goodFactor σ)) ⇒ₚ x := by
  intro τ ht
  have hf : ∀ a, Uses x a → goodFactor σ a τ = true := by
    intro a ha
    exact (allMeet_true _ _).mp ht _ (List.mem_map.mpr ⟨a, (mem_supportList x a).mpr ha, rfl⟩)
  let υ : Assignment ap := fun a => if Uses x a then τ a else σ a
  have hυ : x υ = true := by
    apply hx σ υ _ _ hs
    · intro a ha
      by_cases hu : Uses x a
      · have hfa := hf a hu
        have heval := propEval_used_atom hu τ
        change σ a = (if Uses x a then τ a else σ a)
        rw [ite_eq_left hu]
        cases he : σ a <;> simp_all [goodFactor, Class.ofFormula, Class.compl]
      · simp [υ, hu]
    · intro a ha hsa
      by_cases hu : Uses x a
      · have hfa := hf a hu
        have heval := propEval_used_atom hu τ
        simpa [υ, hu, goodFactor, ha, hsa, Class.ofFormula, heval] using hfa
      · simpa [υ, hu] using hsa
  have he : x υ = x τ := by
    apply support_locality
    intro a ha; simp [υ, ha]
  exact he ▸ hυ

/-- STAGE1 §3 for semantic classes passing the co-safety support test. -/
theorem class_cosafety_witness (x : Class ap) (hx : Positive x) (hc : HasTag cosafety x)
    (hs : Holds w j x) : EventuallyTop w j x := by
  apply (allMeet_witness ((supportList x).map (goodFactor (truthAssignment w j))) ?_).mono
    (goodBranch_implies x hx _ hs)
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  have hu := (mem_supportList x a).mp ha
  have haCo := hc a hu
  unfold goodFactor
  split
  · rename_i hap
    cases a <;> simp only [isAP] at hap
    case ap p =>
      split
      · rename_i hs'
        apply cosafety_witness _ haCo _ _
        simpa only [truthAssignment, decide_eq_true_eq] using hs'
      · rename_i hs'
        have hn : ¬Sat none w (.ap p) j := by
          simpa only [truthAssignment, decide_eq_true_eq] using hs'
        have hw : Sat none w (.neg (.ap p)) j := ⟨trivial, hn⟩
        exact cosafety_witness (.neg (.ap p)) (by trivial) _ _ hw
  · split
    · rename_i hs'
      apply cosafety_witness _ haCo _ _
      simpa only [truthAssignment, decide_eq_true_eq] using hs'
    · exact ⟨0, U_top⟩

theorem EventuallyBot.antimono (h : EventuallyBot w j y) (hxy : x ⇒ₚ y) : EventuallyBot w j x := by
  rw [eventuallyBot_iff] at *
  apply h.mono
  intro σ hy
  have hy' : y σ = false := by simpa only [Class.compl, Bool.not_eq_true'] using hy
  change (!(x σ)) = true
  have hx : x σ = false := Bool.eq_false_iff.mpr (fun ht => Bool.noConfusion (hy'.symm.trans (hxy σ ht)))
  simp [hx]

def allJoin : List (Class ap) → Class ap
  | [] => Class.bot
  | x :: xs => join x (allJoin xs)

theorem allJoin_false (xs : List (Class ap)) (σ : Assignment ap) :
    allJoin xs σ = false ↔ ∀ x, x ∈ xs → x σ = false := by
  induction xs with
  | nil => simp [allJoin, Class.bot, Class.ofFormula, propEval]
  | cons x xs ih =>
    change (x σ || allJoin xs σ) = false ↔ _
    simp only [Bool.or_eq_false_iff, ih, List.mem_cons, forall_eq_or_imp]

theorem allJoin_bad_prefix (xs : List (Class ap))
    (h : ∀ x, x ∈ xs → EventuallyBot w j x) : EventuallyBot w j (allJoin xs) := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih => exact (h x (by simp)).join (ih (fun y hy => h y (by simp [hy])))

/-- A clause false at σ: negate the fixed true APs, retain false modal
atoms, and use false for the true modal atoms. -/
def badFactor (σ : Assignment ap) (a : Formula (Fin ap)) : Class ap :=
  if isAP a then
    if σ a then (Class.ofFormula a).compl else Class.ofFormula a
  else if σ a then Class.bot else Class.ofFormula a

theorem implies_badClause (x : Class ap) (hx : Positive x) (σ : Assignment ap)
    (hs : x σ = false) : x ⇒ₚ allJoin ((supportList x).map (badFactor σ)) := by
  intro τ ht
  apply Classical.byContradiction
  intro hn
  have hfalse : allJoin ((supportList x).map (badFactor σ)) τ = false := Bool.eq_false_iff.mpr hn
  have hf : ∀ a, Uses x a → badFactor σ a τ = false := by
    intro a ha
    exact (allJoin_false _ _).mp hfalse _ (List.mem_map.mpr ⟨a, (mem_supportList x a).mpr ha, rfl⟩)
  let υ : Assignment ap := fun a => if Uses x a then σ a else τ a
  have hυ : x υ = true := by
    apply hx τ υ _ _ ht
    · intro a ha
      by_cases hu : Uses x a
      · have hfa := hf a hu
        have heval := propEval_used_atom hu τ
        change τ a = (if Uses x a then σ a else τ a)
        rw [ite_eq_left hu]
        cases he : σ a <;> simp_all [badFactor, Class.ofFormula, Class.compl]
      · simp [υ, hu]
    · intro a ha hta
      by_cases hu : Uses x a
      · have hfa := hf a hu
        have heval := propEval_used_atom hu τ
        have hsa : σ a = true := by
          cases he : σ a
          · simp [badFactor, ha, he, Class.ofFormula, heval, hta] at hfa
          · rfl
        simp [υ, hu, hsa]
      · simpa [υ, hu] using hta
  have he : x υ = x σ := by
    apply support_locality
    intro a ha; simp [υ, ha]
  exact Bool.noConfusion (hs.symm.trans (he ▸ hυ))

/-- STAGE1 §3 for semantic classes passing the safety support test. -/
theorem class_safety_bad_prefix (x : Class ap) (hx : Positive x) (hc : HasTag safety x)
    (hs : ¬Holds w j x) : EventuallyBot w j x := by
  have hxfalse : x (truthAssignment w j) = false := Bool.eq_false_iff.mpr hs
  apply (allJoin_bad_prefix ((supportList x).map (badFactor (truthAssignment w j))) ?_).antimono
    (implies_badClause x hx _ hxfalse)
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  have hu := (mem_supportList x a).mp ha
  have haSa := hc a hu
  unfold badFactor
  split
  · rename_i hap
    cases a <;> simp only [isAP] at hap
    case ap p =>
      split
      · rename_i hs'
        have hw : ¬Sat none w (.neg (.ap p)) j := by
          intro hneg
          apply hneg.2
          simpa only [truthAssignment, decide_eq_true_eq] using hs'
        exact safety_bad_prefix (.neg (.ap p)) (by trivial) _ _ hw
      · rename_i hs'
        apply safety_bad_prefix _ haSa _ _
        simpa only [truthAssignment, decide_eq_true_eq] using hs'
  · split
    · exact ⟨0, rfl⟩
    · rename_i hs'
      apply safety_bad_prefix _ haSa _ _
      simpa only [truthAssignment, decide_eq_true_eq] using hs'

theorem D_uses (v : Letter (Fin ap)) (h : Uses (D v x) t) :
    ∃ a, Uses x a ∧ Uses (Class.ofFormula (stepSyntax v a)) t := by
  apply Classical.byContradiction; intro hn
  obtain ⟨σ, b, hb⟩ := h
  apply hb
  change x (stepAtom v (setAtom σ t b)) = x (stepAtom v σ)
  apply support_locality
  intro a ha
  have hh : ¬Uses (Class.ofFormula (stepSyntax v a)) t := fun hu => hn ⟨a, ha, hu⟩
  have he := not_uses hh σ b
  change propEval (setAtom σ t b) (stepSyntax v a) = propEval σ (stepSyntax v a) at he
  rw [step_substitution, step_substitution, propEval_used_atom ha, propEval_used_atom ha] at he
  exact he

theorem safety_atoms (f : Formula (Fin ap)) (hf : safety f)
    (a : Formula (Fin ap)) (ha : a ∈ modalAtoms f) : safety a := by
  induction f with
  | tt | ff => contradiction
  | ap b => have he := List.mem_singleton.mp ha; subst a; exact hf
  | neg f ih => cases f <;> simp_all [safety, modalAtoms]
  | conj f g ihf ihg | disj f g ihf ihg =>
    exact (List.mem_append.mp ha).elim (ihf hf.1) (ihg hf.2)
  | next f | globally f | release f g | weakUntil f g =>
    have he := List.mem_singleton.mp ha; subst a; exact hf
  | _ => contradiction

theorem finite_atoms (f : Formula (Fin ap)) (hf : finite f)
    (a : Formula (Fin ap)) (ha : a ∈ modalAtoms f) : finite a := by
  induction f with
  | tt | ff => contradiction
  | ap b => have he := List.mem_singleton.mp ha; subst a; exact hf
  | neg f ih => cases f <;> simp_all [finite, modalAtoms]
  | conj f g ihf ihg | disj f g ihf ihg =>
    exact (List.mem_append.mp ha).elim (ihf hf.1) (ihg hf.2)
  | next f => have he := List.mem_singleton.mp ha; subst a; exact hf
  | _ => contradiction

theorem unfold_safety (f : Formula α) (h : safety f) : safety (unfoldSyntax f) := by
  induction f with
  | tt | ff | ap _ | next _ => exact h
  | neg f ih => cases f <;> simp_all [safety, unfoldSyntax]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf h.1, ihg h.2⟩
  | globally f ih => exact ⟨ih h, h⟩
  | release f g ihf ihg | weakUntil f g ihf ihg => exact ⟨ihg h.2, ihf h.1, h⟩
  | _ => contradiction

theorem U_safety (h : HasTag safety x) : HasTag safety (U x) := by
  intro t ht
  obtain ⟨a, ha, hat⟩ := U_uses ht
  have hd : (Class.ofFormula (unfoldSyntax a)).DependsOn (modalAtoms (unfoldSyntax a)) :=
    fun σ τ hh => propEval_local _ _ _ hh
  exact safety_atoms _ (unfold_safety a (h a ha)) t (uses_in_bound hd hat)

theorem step_cosafety_atoms (f : Formula (Fin ap)) (hf : cosafety f) (v : Letter (Fin ap))
    (a : Formula (Fin ap)) (ha : a ∈ modalAtoms (stepSyntax v f)) : cosafety a := by
  induction f with
  | tt | ff => contradiction
  | ap p => cases he : v p <;> simp_all [stepSyntax, modalAtoms]
  | neg f ih =>
    cases f <;> simp only [cosafety] at hf
    case ap p => cases he : v p <;> simp_all [stepSyntax, modalAtoms]
  | conj f g ihf ihg | disj f g ihf ihg =>
    exact (List.mem_append.mp ha).elim (ihf hf.1) (ihg hf.2)
  | next f => exact cosafety_atoms f hf a ha
  | eventually f | «until» f g | strongRelease f g =>
    have he := List.mem_singleton.mp ha; subst a; exact hf
  | _ => contradiction

theorem step_safety_atoms (f : Formula (Fin ap)) (hf : safety f) (v : Letter (Fin ap))
    (a : Formula (Fin ap)) (ha : a ∈ modalAtoms (stepSyntax v f)) : safety a := by
  induction f with
  | tt | ff => contradiction
  | ap p => cases he : v p <;> simp_all [stepSyntax, modalAtoms]
  | neg f ih =>
    cases f <;> simp only [safety] at hf
    case ap p => cases he : v p <;> simp_all [stepSyntax, modalAtoms]
  | conj f g ihf ihg | disj f g ihf ihg =>
    exact (List.mem_append.mp ha).elim (ihf hf.1) (ihg hf.2)
  | next f => exact safety_atoms f hf a ha
  | globally f | release f g | weakUntil f g =>
    have he := List.mem_singleton.mp ha; subst a; exact hf
  | _ => contradiction

theorem D_cosafety (v : Letter (Fin ap)) (h : HasTag cosafety x) : HasTag cosafety (D v x) := by
  intro t ht
  obtain ⟨a, ha, hat⟩ := D_uses v ht
  have hd : (Class.ofFormula (stepSyntax v a)).DependsOn (modalAtoms (stepSyntax v a)) :=
    fun σ τ hh => propEval_local _ _ _ hh
  exact step_cosafety_atoms a (h a ha) v t (uses_in_bound hd hat)

theorem D_safety (v : Letter (Fin ap)) (h : HasTag safety x) : HasTag safety (D v x) := by
  intro t ht
  obtain ⟨a, ha, hat⟩ := D_uses v ht
  have hd : (Class.ofFormula (stepSyntax v a)).DependsOn (modalAtoms (stepSyntax v a)) :=
    fun σ τ hh => propEval_local _ _ _ hh
  exact step_safety_atoms a (h a ha) v t (uses_in_bound hd hat)

theorem step_nnf (f : Formula α) (h : NNF f) (v : Letter α) : NNF (stepSyntax v f) := by
  induction f with
  | tt | ff => trivial
  | ap p => cases he : v p <;> simp [stepSyntax, he, NNF]
  | neg f ih =>
    cases f <;> simp only [NNF] at h
    case tt => trivial
    case ff => trivial
    case ap p => cases he : v p <;> simp [stepSyntax, he, NNF]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf h.1, ihg h.2⟩
  | next f | eventually f | globally f | «until» f g | release f g
  | weakUntil f g | strongRelease f g => exact h
  | _ => contradiction

theorem U_nnfClass (h : NNFClass x) : NNFClass (U x) := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨_, unfold_nnf f hf, (U_ofFormula f).symm⟩

theorem D_nnfClass (v : Letter (Fin ap)) (h : NNFClass x) : NNFClass (D v x) := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨_, step_nnf f hf v, (D_ofFormula v f).symm⟩

theorem safety_cosafety_finite (f : Formula α) (hs : safety f) (hc : cosafety f) : finite f := by
  induction f with
  | tt | ff | ap _ => trivial
  | neg f ih => cases f <;> simp_all [safety, cosafety, finite]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf hs.1 hc.1, ihg hs.2 hc.2⟩
  | next f ih => exact ih hs hc
  | _ => first | contradiction | cases hs | cases hc

theorem tags_intersection (hs : HasTag safety x) (hc : HasTag cosafety x) : HasTag finite x :=
  fun a ha => safety_cosafety_finite a (hs a ha) (hc a ha)

theorem derivatives_unfolded (w : Word (Fin ap)) (j n : Nat) (x : Class ap) :
    U (derivatives w j n x) = derivatives w j n x := by
  induction n generalizing j x with
  | zero => exact U_idempotent x
  | succ n ih => exact ih _ _

theorem derivatives_snoc (w : Word (Fin ap)) (j n : Nat) (x : Class ap) :
    derivatives w j (n+1) x = U (D (w (j+n)) (derivatives w j n x)) := by
  rw [derivatives_add w j n 1 x]
  change U (U (D (w (j+n)) (U (derivatives w j n x)))) = _
  rw [derivatives_unfolded, U_idempotent]

theorem derivatives_nnf (w : Word (Fin ap)) (j n : Nat) (h : NNFClass x) :
    NNFClass (derivatives w j n x) := by
  induction n generalizing j x with
  | zero => exact U_nnfClass h
  | succ n ih => exact ih _ (U_nnfClass (D_nnfClass _ (U_nnfClass h)))

theorem nnfClass_positive (h : NNFClass x) : Positive x := by
  obtain ⟨f, hf, rfl⟩ := h
  exact nnf_positive f hf

theorem derivatives_bot (w : Word (Fin ap)) (j n : Nat) :
    derivatives w j n Class.bot = Class.bot := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [derivatives, delta_bot]; exact ih _

theorem derivatives_bot_persists (h : derivatives w j n x = Class.bot) (hm : n ≤ m) :
    derivatives w j m x = Class.bot := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [derivatives_add, h, derivatives_bot]

theorem replaceTrue_ofFormula (p : Formula (Fin ap) → Prop) (f : Formula (Fin ap)) :
    replaceTrue p (Class.ofFormula f) = Class.ofFormula (replaceTrueSyntax p f) := by
  apply Class.ext; intro σ; exact (replaceTrue_eval p f σ).symm

theorem replaceTrue_nnf (p : Formula (Fin ap) → Prop) (f : Formula (Fin ap)) (hf : NNF f) :
    NNF (replaceTrueSyntax p f) := by
  induction f with
  | tt | ff => trivial
  | ap a => simp only [replaceTrueSyntax]; split <;> trivial
  | neg f ih =>
    cases f <;> simp only [NNF] at hf
    case tt => trivial
    case ff => trivial
    case ap a =>
      simp only [replaceTrueSyntax]; split <;> trivial
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | next f | eventually f | globally f | «until» f g | release f g
  | weakUntil f g | strongRelease f g =>
    simp only [replaceTrueSyntax]; split
    · trivial
    · exact hf
  | _ => contradiction

theorem replaceTrue_nnfClass (p : Formula (Fin ap) → Prop) (h : NNFClass x) :
    NNFClass (replaceTrue p x) := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨_, replaceTrue_nnf p f hf, (replaceTrue_ofFormula p f).symm⟩

theorem elideFuel_nnfClass (n : Nat) (h : NNFClass x) : NNFClass (elideFuel n x) := by
  induction n generalizing x with
  | zero => exact h
  | succ n ih =>
    simp only [elideFuel]; split
    · exact h
    · exact ih (replaceTrue_nnfClass _ h)

theorem rho_nnfClass {x : Class ap} (h : NNFClass x) : NNFClass (rho x) := by
  have hp : ∀ y : Class ap, NNFClass y → NNFClass (extractPass y) := by
    intro y hy
    exact U_nnfClass (elideFuel_nnfClass _ (replaceTrue_nnfClass _ hy))
  unfold rho; split
  · exact hp _ (U_nnfClass h)
  · exact hp _ h

theorem meet_nnfClass (hx : NNFClass x) (hy : NNFClass y) : NNFClass (meet x y) := by
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨.conj f g, ⟨hf, hg⟩, rfl⟩

theorem meet_uses (h : Uses (meet x y) a) : Uses x a ∨ Uses y a := by
  apply Classical.byContradiction; intro hn
  have hx : ¬Uses x a := fun ha => hn (Or.inl ha)
  have hy : ¬Uses y a := fun ha => hn (Or.inr ha)
  obtain ⟨σ, b, hb⟩ := h
  apply hb
  change (x (setAtom σ a b) && y (setAtom σ a b)) = (x σ && y σ)
  rw [not_uses hx, not_uses hy]

theorem meet_tag (hx : HasTag tag x) (hy : HasTag tag y) : HasTag tag (meet x y) :=
  fun a ha => (meet_uses ha).elim (hx a) (hy a)

end
end Tlsf.Dpa
