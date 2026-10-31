import TlsfProofs.Dpa.Classes

/-!
# Executable propositional classes

`src/lib/dpa_formula.c:3` interns Boolean functions, and `:64` obtains their
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

def propAnd : Formula α → Formula α → Formula α
  | .ff, _ | _, .ff => .ff
  | .tt, g => g
  | f, .tt => f
  | f, g => .conj f g

def propOr : Formula α → Formula α → Formula α
  | .tt, _ | _, .tt => .tt
  | .ff, g => g
  | f, .ff => f
  | f, g => .disj f g

def propNot : Formula α → Formula α
  | .tt => .ff
  | .ff => .tt
  | f => .neg f

theorem propAnd_eval (σ : Assignment ap) (f g : Formula (Fin ap)) :
    propEval σ (propAnd f g) = (propEval σ f && propEval σ g) := by
  cases f <;> cases g <;> simp [propAnd, propEval]

theorem propOr_eval (σ : Assignment ap) (f g : Formula (Fin ap)) :
    propEval σ (propOr f g) = (propEval σ f || propEval σ g) := by
  cases f <;> cases g <;> simp [propOr, propEval]

theorem propNot_eval (σ : Assignment ap) (f : Formula (Fin ap)) :
    propEval σ (propNot f) = !propEval σ f := by
  cases f <;> simp [propNot, propEval]

/-- Simplify only outer propositional structure. Frozen modal operands stay
verbatim, so this preserves Boolean classes, not merely temporal languages. -/
def reduceProp : Formula α → Formula α
  | .neg f => propNot (reduceProp f)
  | .conj f g => propAnd (reduceProp f) (reduceProp g)
  | .disj f g => propOr (reduceProp f) (reduceProp g)
  | .impl f g => propOr (propNot (reduceProp f)) (reduceProp g)
  | .equiv f g =>
    let a := reduceProp f
    let b := reduceProp g
    propOr (propAnd a b) (propAnd (propNot a) (propNot b))
  | f => f

theorem reduceProp_eval (σ : Assignment ap) (f : Formula (Fin ap)) :
    propEval σ (reduceProp f) = propEval σ f := by
  induction f with
  | neg _ ih => simp only [reduceProp, propNot_eval, ih, propEval]
  | conj _ _ ih ih' => simp only [reduceProp, propAnd_eval, ih, ih', propEval]
  | disj _ _ ih ih' => simp only [reduceProp, propOr_eval, ih, ih', propEval]
  | impl _ _ ih ih' => simp only [reduceProp, propOr_eval, propNot_eval, ih, ih', propEval]
  | equiv f g ih ih' =>
    simp only [reduceProp, propOr_eval, propAnd_eval, propNot_eval, ih, ih', propEval]
    cases propEval σ f <;> cases propEval σ g <;> rfl
  | _ => rfl

theorem reduceProp_class (f : Formula (Fin ap)) :
    Class.ofFormula (reduceProp f) = Class.ofFormula f :=
  Class.ext (fun σ => reduceProp_eval σ f)

/-- Canonical class identity, with constant propagation and a structural
fast path before the exhaustive, short-circuiting truth comparison. -/
def equivalent (f g : Formula (Fin ap)) : Bool :=
  let f := reduceProp f
  let g := reduceProp g
  let atoms := (modalAtoms f ++ modalAtoms g).eraseDups
  if f = g then true else
    (assignments atoms).all (fun σ => propEval σ f == propEval σ g)

theorem equivalent_exact (f g : Formula (Fin ap)) :
    equivalent f g = true ↔ Class.ofFormula f = Class.ofFormula g := by
  unfold equivalent
  dsimp only
  split
  · rename_i he
    simp only [true_iff]
    exact (reduceProp_class f).symm.trans ((congrArg Class.ofFormula he).trans (reduceProp_class g))
  · rw [List.all_eq_true]
    simp only [beq_iff_eq]
    rw [← List.map_inj_left]
    change table _ (reduceProp f) = table _ (reduceProp g) ↔ _
    rw [table_exact]
    · rw [reduceProp_class, reduceProp_class]
    · intro σ τ h
      exact propEval_local _ σ τ (fun a ha => h a (by simp [ha]))
    · intro σ τ h
      exact propEval_local _ σ τ (fun a ha => h a (by simp [ha]))

/-- Boolean cofactor: modal operands remain frozen. Negated AP constants are
allowed by `NNF`; the canonical class removes their syntax when tested. -/
def cofactor (a : Formula (Fin ap)) (value : Bool) : Formula (Fin ap) → Formula (Fin ap)
  | .tt => .tt
  | .ff => .ff
  | .neg f => .neg (cofactor a value f)
  | .conj f g => .conj (cofactor a value f) (cofactor a value g)
  | .disj f g => .disj (cofactor a value f) (cofactor a value g)
  | .impl f g => .impl (cofactor a value f) (cofactor a value g)
  | .equiv f g => .equiv (cofactor a value f) (cofactor a value g)
  | f => if f = a then (if value then .tt else .ff) else f

theorem cofactor_eval (a f : Formula (Fin ap)) (value : Bool) (σ : Assignment ap) :
    propEval σ (cofactor a value f) = propEval (setAtom σ a value) f := by
  induction f with
  | tt | ff => rfl
  | neg _ ih => simp only [cofactor, propEval, ih]
  | conj _ _ ih ih' | disj _ _ ih ih' | impl _ _ ih ih' | equiv _ _ ih ih' =>
    simp only [cofactor, propEval, ih, ih']
  | _ => simp only [cofactor]; split <;> cases value <;> simp_all [propEval, setAtom]

theorem cofactor_unused (f a : Formula (Fin ap)) :
    Class.ofFormula (cofactor a false f) = Class.ofFormula (cofactor a true f) ↔
      ¬Uses (Class.ofFormula f) a := by
  constructor
  · intro he hu
    obtain ⟨σ, b, hb⟩ := hu
    have h : propEval (setAtom σ a false) f = propEval (setAtom σ a true) f := by
      have hh := congrArg (fun c : Class ap => c σ) he
      simpa only [Class.ofFormula, cofactor_eval] using hh
    have hid : setAtom σ a (σ a) = σ := by
      funext t; by_cases ht : t = a <;> simp [setAtom, ht]
    have same (b c : Bool) : propEval (setAtom σ a b) f = propEval (setAtom σ a c) f := by
      cases b <;> cases c
      · rfl
      · exact h
      · exact h.symm
      · rfl
    apply hb
    change propEval (setAtom σ a b) f = propEval σ f
    rw [same b (σ a), hid]
  · intro hn
    apply Class.ext
    intro σ
    change propEval σ (cofactor a false f) = propEval σ (cofactor a true f)
    rw [cofactor_eval, cofactor_eval]
    exact (not_uses hn σ false).trans (not_uses hn σ true).symm

/-- Support via simplified Shannon cofactors. Unlike three evaluations of the
unreduced formula for every assignment, constant cofactors terminate early. -/
def uses (f a : Formula (Fin ap)) : Bool :=
  !equivalent (cofactor a false f) (cofactor a true f)

theorem uses_exact (f a : Formula (Fin ap)) :
    uses f a = true ↔ Uses (Class.ofFormula f) a := by
  simp only [uses, Bool.not_eq_true', Bool.eq_false_iff, Ne, equivalent_exact,
    cofactor_unused, Classical.not_not]

/-- A support predicate supplied as an executable test; later callers use it
for tags, protection and simultaneous substitution. -/
def hasTag (tag : Formula (Fin ap) → Bool) (f : Formula (Fin ap)) : Bool :=
  (modalAtoms f).eraseDups.all (fun a => tag a || !uses f a)

theorem hasTag_exact (tag : Formula (Fin ap) → Bool) (f : Formula (Fin ap)) :
    hasTag tag f = true ↔ HasTag (fun a => tag a = true) (Class.ofFormula f) := by
  simp only [hasTag, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h a ha
    have hm := uses_in_bound (fun σ τ hh => propEval_local f σ τ hh) ha
    rcases h a (by simpa using hm) with ht | hf
    · exact ht
    · have hu := (uses_exact f a).mpr ha
      simp_all
  · intro h a _
    cases hu : uses f a
    · exact Or.inr rfl
    · exact Or.inl (h a ((uses_exact f a).mp hu))

end Tlsf.Dpa.Impl
