import TlsfProofs.Dpa.Classes

/-!
# Executable propositional classes

`src/lib/dpa_formula.c:3` interns Boolean functions, and `:64` obtains their
reduced Shannon children. This reference uses branch-pruned Shannon comparison
over an explicit finite atom list, independently of a BDD manager.
Frozen modal formulas are independent variables,
including a formula and its temporal dual. AP negation is complementation.

The executable definitions below do not use classical decision procedures.
The refinement theorems identify equality and support with `Classes.lean`.
The reference has exponential worst-case cost in the number of modal atoms;
it is not a proposed replacement for the production BDD library.
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

def propAnd [DecidableEq α] (f g : Formula α) : Formula α :=
  if f = g then f else
  match f, g with
  | .ff, _ | _, .ff => .ff
  | .tt, g => g
  | f, .tt => f
  | f, g => .conj f g

def propOr [DecidableEq α] (f g : Formula α) : Formula α :=
  if f = g then f else
  match f, g with
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
  unfold propAnd
  split
  · rename_i h; subst g; simp
  · cases f <;> cases g <;> simp [propEval]

theorem propOr_eval (σ : Assignment ap) (f g : Formula (Fin ap)) :
    propEval σ (propOr f g) = (propEval σ f || propEval σ g) := by
  unfold propOr
  split
  · rename_i h; subst g; simp
  · cases f <;> cases g <;> simp [propEval]

theorem propNot_eval (σ : Assignment ap) (f : Formula (Fin ap)) :
    propEval σ (propNot f) = !propEval σ f := by
  cases f <;> simp [propNot, propEval]

/-- Simplify only outer propositional structure. Frozen modal operands stay
verbatim, so this preserves Boolean classes, not merely temporal languages. -/
def reduceProp [DecidableEq α] : Formula α → Formula α
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

theorem cofactor_depends (f a : Formula (Fin ap)) (b : Bool) {atoms : List (Formula (Fin ap))}
    (hf : (Class.ofFormula f).DependsOn (a :: atoms)) :
    (Class.ofFormula (cofactor a b f)).DependsOn atoms := by
  intro σ τ h
  change propEval σ (cofactor a b f) = propEval τ (cofactor a b f)
  rw [cofactor_eval, cofactor_eval]
  apply hf
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · simp [setAtom]
  · by_cases he : t = a
    · subst t; simp [setAtom]
    · simp [setAtom, he, h t ht]

theorem cofactor_pair_exact (a f g : Formula (Fin ap)) :
    (Class.ofFormula (cofactor a false f) = Class.ofFormula (cofactor a false g) ∧
      Class.ofFormula (cofactor a true f) = Class.ofFormula (cofactor a true g)) ↔
      Class.ofFormula f = Class.ofFormula g := by
  constructor
  · rintro ⟨hl, hh⟩
    apply Class.ext
    intro σ
    change propEval σ f = propEval σ g
    have hid : setAtom σ a (σ a) = σ := by
      funext t; by_cases ht : t = a <;> simp [setAtom, ht]
    have he : propEval (setAtom σ a (σ a)) f = propEval (setAtom σ a (σ a)) g := by
      cases h : σ a
      · have he := congrArg (fun c : Class ap => c σ) hl
        simpa only [Class.ofFormula, cofactor_eval, h] using he
      · have he := congrArg (fun c : Class ap => c σ) hh
        simpa only [Class.ofFormula, cofactor_eval, h] using he
    simpa only [hid] using he
  · intro h
    constructor <;> apply Class.ext <;> intro σ
    · exact (cofactor_eval a f false σ).trans
        ((congrArg (fun c : Class ap => c (setAtom σ a false)) h).trans (cofactor_eval a g false σ).symm)
    · exact (cofactor_eval a f true σ).trans
        ((congrArg (fun c : Class ap => c (setAtom σ a true)) h).trans (cofactor_eval a g true σ).symm)

/-- Exhaustive Shannon equality with constant propagation at every branch.
Equal residuals stop immediately; no truth-vector allocation or memo is used. -/
def equivalentOn : List (Formula (Fin ap)) → Formula (Fin ap) → Formula (Fin ap) → Bool
  | [], f, g => propEval (fun _ => false) (reduceProp f) == propEval (fun _ => false) (reduceProp g)
  | a :: atoms, f, g =>
    let f := reduceProp f
    let g := reduceProp g
    if f = g then true else
      let f0 := cofactor a false f
      let g0 := cofactor a false g
      let f1 := cofactor a true f
      let g1 := cofactor a true g
      if f0 = f1 ∧ g0 = g1 then equivalentOn atoms f0 g0 else
        equivalentOn atoms f0 g0 && equivalentOn atoms f1 g1

theorem equivalentOn_exact (atoms : List (Formula (Fin ap))) (f g : Formula (Fin ap))
    (hf : (Class.ofFormula f).DependsOn atoms) (hg : (Class.ofFormula g).DependsOn atoms) :
    equivalentOn atoms f g = true ↔ Class.ofFormula f = Class.ofFormula g := by
  induction atoms generalizing f g with
  | nil =>
    simp only [equivalentOn, reduceProp_eval, beq_iff_eq]
    constructor
    · intro he; apply Class.ext; intro σ
      exact (hf σ (fun _ => false) (by simp)).trans
        (he.trans (hg σ (fun _ => false) (by simp)).symm)
    · intro he; exact congrArg (fun c : Class ap => c (fun _ => false)) he
  | cons a atoms ih =>
    have hf' : (Class.ofFormula (reduceProp f)).DependsOn (a :: atoms) := by
      simpa only [reduceProp_class] using hf
    have hg' : (Class.ofFormula (reduceProp g)).DependsOn (a :: atoms) := by
      simpa only [reduceProp_class] using hg
    simp only [equivalentOn]
    split
    · rename_i he
      simp only [true_iff]
      exact (reduceProp_class f).symm.trans ((congrArg Class.ofFormula he).trans (reduceProp_class g))
    · split
      · rename_i he
        rw [ih _ _ (cofactor_depends _ _ false hf') (cofactor_depends _ _ false hg')]
        have hc := cofactor_pair_exact a (reduceProp f) (reduceProp g)
        rw [← he.1, ← he.2, and_self] at hc
        exact hc.trans (by rw [reduceProp_class, reduceProp_class])
      · rw [Bool.and_eq_true, ih _ _ (cofactor_depends _ _ false hf') (cofactor_depends _ _ false hg'),
          ih _ _ (cofactor_depends _ _ true hf') (cofactor_depends _ _ true hg'), cofactor_pair_exact]
        rw [reduceProp_class, reduceProp_class]

/-- Cheap necessary equality tests separate most unequal residuals before
Shannon recursion. Every sampled assignment is only a rejection filter. -/
def probeCode : Formula (Fin ap) → Nat
  | .tt => 1 | .ff => 2 | .ap a => 3 + 31 * a.val
  | .neg f => (5 + 37 * probeCode f) % 65521
  | .next f => (7 + 37 * probeCode f) % 65521
  | .strongNext f => (11 + 37 * probeCode f) % 65521
  | .eventually f => (13 + 37 * probeCode f) % 65521
  | .globally f => (17 + 37 * probeCode f) % 65521
  | .conj f g => (19 + 37 * probeCode f + 101 * probeCode g) % 65521
  | .disj f g => (23 + 37 * probeCode f + 101 * probeCode g) % 65521
  | .impl f g => (29 + 37 * probeCode f + 101 * probeCode g) % 65521
  | .equiv f g => (31 + 37 * probeCode f + 101 * probeCode g) % 65521
  | .until f g => (41 + 37 * probeCode f + 101 * probeCode g) % 65521
  | .release f g => (43 + 37 * probeCode f + 101 * probeCode g) % 65521
  | .weakUntil f g => (47 + 37 * probeCode f + 101 * probeCode g) % 65521
  | .strongRelease f g => (53 + 37 * probeCode f + 101 * probeCode g) % 65521

def probeValue (seed code : Nat) : Bool :=
  let threshold := match seed % 4 with
    | 0 => 32760 | 1 => 60000 | 2 => 5521 | _ => 64500
  decide ((code * (seed + 1) ^ 2 + 17 * seed) % 65521 < threshold)

def probeAssignment (seed : Nat) (a : Formula (Fin ap)) : Bool :=
  probeValue seed (probeCode a)

/-- Compile frozen atoms to probe codes once before evaluating a fingerprint. -/
inductive ProbeExpr where
  | literal (b : Bool) | atom (code : Nat) | neg (f : ProbeExpr)
  | conj (f g : ProbeExpr) | disj (f g : ProbeExpr)
  | impl (f g : ProbeExpr) | equiv (f g : ProbeExpr)

def probeExpr : Formula (Fin ap) → ProbeExpr
  | .tt => .literal true | .ff => .literal false
  | .neg f => .neg (probeExpr f)
  | .conj f g => .conj (probeExpr f) (probeExpr g)
  | .disj f g => .disj (probeExpr f) (probeExpr g)
  | .impl f g => .impl (probeExpr f) (probeExpr g)
  | .equiv f g => .equiv (probeExpr f) (probeExpr g)
  | f => .atom (probeCode f)

def ProbeExpr.eval (seed : Nat) : ProbeExpr → Bool
  | .literal b => b | .atom code => probeValue seed code
  | .neg f => !f.eval seed
  | .conj f g => f.eval seed && g.eval seed
  | .disj f g => f.eval seed || g.eval seed
  | .impl f g => !f.eval seed || g.eval seed
  | .equiv f g => f.eval seed == g.eval seed

theorem probeExpr_eval (f : Formula (Fin ap)) (seed : Nat) :
    (probeExpr f).eval seed = propEval (probeAssignment seed) f := by
  induction f <;> simp_all [probeExpr, ProbeExpr.eval, propEval, probeAssignment]

def classFingerprint (f : Formula (Fin ap)) : Nat :=
  let e := probeExpr (reduceProp f)
  (List.range 128).foldl (fun code seed => 2*code + if e.eval seed then 1 else 0) 0

theorem classFingerprint_congr (f g : Formula (Fin ap))
    (h : Class.ofFormula f = Class.ofFormula g) : classFingerprint f = classFingerprint g := by
  have hc : Class.ofFormula (reduceProp f) = Class.ofFormula (reduceProp g) := by
    simpa only [reduceProp_class] using h
  have he (seed : Nat) : (probeExpr (reduceProp f)).eval seed =
      (probeExpr (reduceProp g)).eval seed := by
    rw [probeExpr_eval, probeExpr_eval]
    exact congrArg (fun c : Class ap => c (probeAssignment seed)) hc
  unfold classFingerprint
  apply congrArg (fun step : Nat → Nat → Nat => (List.range 128).foldl step 0)
  funext code seed
  rw [he]

def sampleAgreement (atoms : List (Formula (Fin ap))) (f g : Formula (Fin ap)) : Bool :=
  if f = g then true else
  (List.range 16).all (fun seed => propEval (probeAssignment seed) f ==
    propEval (probeAssignment seed) g) &&
  atoms.all (fun a =>
    (propEval (setAtom (fun _ => false) a true) f ==
      propEval (setAtom (fun _ => false) a true) g) &&
    (propEval (setAtom (fun _ => true) a false) f ==
      propEval (setAtom (fun _ => true) a false) g))

theorem sampleAgreement_of_eq (atoms : List (Formula (Fin ap))) (f g : Formula (Fin ap))
    (he : Class.ofFormula f = Class.ofFormula g) : sampleAgreement atoms f g = true := by
  unfold sampleAgreement
  split
  · rfl
  · simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro seed _
      exact congrArg (fun c : Class ap => c (probeAssignment seed)) he
    · intro a _
      exact ⟨congrArg (fun c : Class ap => c (setAtom (fun _ => false) a true)) he,
        congrArg (fun c : Class ap => c (setAtom (fun _ => true) a false)) he⟩

def conjuncts : Formula α → List (Formula α)
  | .tt => [] | .conj f g => conjuncts f ++ conjuncts g | f => [f]

def disjuncts : Formula α → List (Formula α)
  | .ff => [] | .disj f g => disjuncts f ++ disjuncts g | f => [f]

theorem conjuncts_eval (f : Formula (Fin ap)) (σ : Assignment ap) :
    (conjuncts f).all (propEval σ) = propEval σ f := by
  induction f <;> simp_all [conjuncts, propEval, List.all_append]

theorem disjuncts_eval (f : Formula (Fin ap)) (σ : Assignment ap) :
    (disjuncts f).any (propEval σ) = propEval σ f := by
  induction f <;> simp_all [disjuncts, propEval, List.any_append]

def sameTerms [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => decide (x ∈ ys)) && ys.all (fun y => decide (y ∈ xs))

theorem sameTerms_mem [DecidableEq α] (xs ys : List α) (h : sameTerms xs ys = true) :
    ∀ x, x ∈ xs ↔ x ∈ ys := by
  simp only [sameTerms, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun x => ⟨h.1 x, h.2 x⟩

def associationAgreement (f g : Formula (Fin ap)) : Bool :=
  sameTerms (conjuncts f) (conjuncts g) || sameTerms (disjuncts f) (disjuncts g)

theorem associationAgreement_sound (f g : Formula (Fin ap))
    (h : associationAgreement f g = true) : Class.ofFormula f = Class.ofFormula g := by
  rcases Bool.or_eq_true_iff.mp h with hc | hd
  · have hm := sameTerms_mem _ _ hc
    apply Class.ext
    intro σ
    change propEval σ f = propEval σ g
    rw [← conjuncts_eval f σ, ← conjuncts_eval g σ]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact ⟨fun h x hx => h x ((hm x).mpr hx), fun h x hx => h x ((hm x).mp hx)⟩
  · have hm := sameTerms_mem _ _ hd
    apply Class.ext
    intro σ
    change propEval σ f = propEval σ g
    rw [← disjuncts_eval f σ, ← disjuncts_eval g σ]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    exact ⟨fun ⟨x, hx, hv⟩ => ⟨x, (hm x).mp hx, hv⟩,
      fun ⟨x, hx, hv⟩ => ⟨x, (hm x).mpr hx, hv⟩⟩

def equivalent (f g : Formula (Fin ap)) : Bool :=
  if f = g then true else
  let f := reduceProp f
  let g := reduceProp g
  if f = g then true else
  let atoms := (modalAtoms f ++ modalAtoms g).eraseDups
  sampleAgreement atoms f g && (associationAgreement f g || equivalentOn atoms f g)

theorem equivalent_exact (f g : Formula (Fin ap)) :
    equivalent f g = true ↔ Class.ofFormula f = Class.ofFormula g := by
  unfold equivalent
  split
  · rename_i he
    simp only [true_iff]
    exact congrArg Class.ofFormula he
  · dsimp only
    split
    · rename_i he
      simp only [true_iff]
      exact (reduceProp_class f).symm.trans
        ((congrArg Class.ofFormula he).trans (reduceProp_class g))
    · have hf : (Class.ofFormula (reduceProp f)).DependsOn
          (modalAtoms (reduceProp f) ++ modalAtoms (reduceProp g)).eraseDups := by
        intro σ τ h
        exact propEval_local _ σ τ (fun a ha => h a (by simp [ha]))
      have hg : (Class.ofFormula (reduceProp g)).DependsOn
          (modalAtoms (reduceProp f) ++ modalAtoms (reduceProp g)).eraseDups := by
        intro σ τ h
        exact propEval_local _ σ τ (fun a ha => h a (by simp [ha]))
      rw [Bool.and_eq_true, Bool.or_eq_true, equivalentOn_exact _ _ _ hf hg]
      constructor
      · intro h
        have he := h.2.elim (associationAgreement_sound _ _) id
        simpa only [reduceProp_class] using he
      · intro h
        have he : Class.ofFormula (reduceProp f) = Class.ofFormula (reduceProp g) := by
          simpa only [reduceProp_class] using h
        exact ⟨sampleAgreement_of_eq _ _ _ he, Or.inr he⟩

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
