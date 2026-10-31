import TlsfProofs.Dpa.Classes

/-!
# Executable propositional classes

`src/lib/dpa_formula.c:3` interns Boolean functions, and `:66` obtains their
reduced Shannon children. This reference uses exhaustive truth tables instead
of a BDD manager. The ordered finite atom list is explicit; the table is
canonical for that list. Frozen modal formulas are independent variables,
including a formula and its temporal dual. AP negation is complementation.

The executable definitions below do not use classical decision procedures.
The refinement theorems identify equality and support with `Classes.lean`.
The reference is exponential in the number of modal atoms, as a truth table
must be; it is not a proposed replacement for the production BDD library.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

/-- Executable assignment update, corresponding to a Boolean cofactor. -/
def write (σ : Assignment ap) (a : Formula (Fin ap)) (b : Bool) : Assignment ap :=
  fun t => if t = a then b else σ t

theorem write_eq (σ : Assignment ap) (a : Formula (Fin ap)) (b : Bool) :
    write σ a b = setAtom σ a b := by
  funext t
  by_cases h : t = a <;> simp [write, setAtom, h]

/-- Enumerate all valuations on a finite atom list, false outside the list.
Duplicates in the list are harmless; no completeness premise is hidden. -/
def assignments : List (Formula (Fin ap)) → List (Assignment ap)
  | [] => [fun _ => false]
  | a :: atoms => (assignments atoms).flatMap
      (fun σ => [write σ a false, write σ a true])

theorem assignments_complete (atoms : List (Formula (Fin ap))) (σ : Assignment ap) :
    ∃ τ, τ ∈ assignments atoms ∧ ∀ a, a ∈ atoms → τ a = σ a := by
  induction atoms with
  | nil => exact ⟨fun _ => false, by simp [assignments], by simp⟩
  | cons a atoms ih =>
    obtain ⟨τ, hτ, he⟩ := ih
    refine ⟨write τ a (σ a), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨τ, hτ, ?_⟩
      cases h : σ a <;> simp
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [write]
      · by_cases h : b = a
        · subst b; simp [write]
        · simp [write, h, he b hb]

/-- The canonical truth vector for a fixed ordered alphabet. -/
def table (atoms : List (Formula (Fin ap))) (f : Formula (Fin ap)) : List Bool :=
  (assignments atoms).map (fun σ => propEval σ f)

theorem table_exact (atoms : List (Formula (Fin ap))) (f g : Formula (Fin ap))
    (hf : (Class.ofFormula f).DependsOn atoms)
    (hg : (Class.ofFormula g).DependsOn atoms) :
    table atoms f = table atoms g ↔ Class.ofFormula f = Class.ofFormula g := by
  constructor
  · intro he
    apply Class.ext
    intro σ
    obtain ⟨τ, hτ, hagree⟩ := assignments_complete atoms σ
    have ht : propEval τ f = propEval τ g := (List.map_inj_left.mp he) τ hτ
    exact (hf τ σ hagree).symm.trans (ht.trans (hg τ σ hagree))
  · intro he
    apply List.map_congr_left
    intro σ _
    exact congrArg (fun x : Class ap => x σ) he

/-- C class identity (`dpa_class`) as a decidable, executable test. The common
alphabet covers both inputs, including their absorbed Boolean variables. -/
def equivalent (f g : Formula (Fin ap)) : Bool :=
  let atoms := (modalAtoms f ++ modalAtoms g).eraseDups
  decide (table atoms f = table atoms g)

theorem equivalent_exact (f g : Formula (Fin ap)) :
    equivalent f g = true ↔ Class.ofFormula f = Class.ofFormula g := by
  unfold equivalent
  rw [decide_eq_true_eq]
  apply table_exact
  · intro σ τ h
    exact propEval_local f σ τ (fun a ha => h a (by simp [ha]))
  · intro σ τ h
    exact propEval_local g σ τ (fun a ha => h a (by simp [ha]))

/-- C's reduced BDD support (`dpa_children`/`tags_impl`, lines 66/81).
Only essential variables survive, including under Boolean absorption. -/
def uses (f a : Formula (Fin ap)) : Bool :=
  (assignments (modalAtoms f).eraseDups).any (fun σ =>
    propEval (write σ a false) f != propEval σ f ||
    propEval (write σ a true) f != propEval σ f)

theorem uses_exact (f a : Formula (Fin ap)) :
    uses f a = true ↔ Uses (Class.ofFormula f) a := by
  rw [uses, List.any_eq_true]
  constructor
  · rintro ⟨σ, _, h⟩
    simp only [Bool.or_eq_true, bne_iff_ne, write_eq] at h
    exact h.elim (fun h => ⟨σ, false, h⟩) (fun h => ⟨σ, true, h⟩)
  · rintro ⟨σ, b, hb⟩
    obtain ⟨τ, hτ, he⟩ := assignments_complete (modalAtoms f).eraseDups σ
    have he' : ∀ a, a ∈ modalAtoms f → τ a = σ a := fun a ha => he a (by simp [ha])
    have hv : propEval τ f = propEval σ f := propEval_local _ _ _ he'
    have hw : propEval (write τ a b) f = propEval (setAtom σ a b) f := by
      apply propEval_local
      intro t ht
      by_cases h : t = a <;> simp [write, setAtom, h, he' t ht]
    refine ⟨τ, hτ, ?_⟩
    have hne : propEval (write τ a b) f ≠ propEval τ f := by
      rw [hw, hv]; exact hb
    cases b <;> simp_all

/-- A support predicate supplied as an executable test; later callers use it
for tags, protection and simultaneous substitution. -/
def hasTag (tag : Formula (Fin ap) → Bool) (f : Formula (Fin ap)) : Bool :=
  (modalAtoms f).all (fun a => !uses f a || tag a)

theorem hasTag_exact (tag : Formula (Fin ap) → Bool) (f : Formula (Fin ap)) :
    hasTag tag f = true ↔ HasTag (fun a => tag a = true) (Class.ofFormula f) := by
  simp only [hasTag, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h a ha
    have hm := uses_in_bound (fun σ τ hh => propEval_local f σ τ hh) ha
    rcases h a hm with hf | ht
    · have hu := (uses_exact f a).mpr ha
      simp_all
    · exact ht
  · intro h a _
    cases hu : uses f a
    · exact Or.inl rfl
    · exact Or.inr (h a ((uses_exact f a).mp hu))

end Tlsf.Dpa.Impl
