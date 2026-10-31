import TlsfProofs.Dpa.Impl.Component

/-!
# NNF dual classification and general Σ₂ components

`src/lib/dpa_formula.c:971` (`dpa_dual`) complements a Boolean class while
renaming modal atoms to their NNF duals. It does not take the Boolean function
complement with unchanged modal variables. `src/lib/dpa_dela.c:93` chooses
the Π₂ orientation and shares a complete run with complemented acceptance.

The theorems below close the semantic NNF classification bridge on arbitrary
canonical support, including absorbed unsupported syntax. They do not yet
verify C's syntax IDs, dual cache or the sharing/constructor algorithm.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

def dual (f : Formula α) : Formula α := Rewrites.to_nnf f false false

theorem safety_dual_cosafety (f : Formula α) (h : safety f) : cosafety (dual f) := by
  induction f with
  | neg f _ => cases f <;> simp_all [safety, dual, Rewrites.to_nnf, cosafety]
  | _ => simp_all [safety, dual, Rewrites.to_nnf, cosafety]

theorem cosafety_dual_safety (f : Formula α) (h : cosafety f) : safety (dual f) := by
  induction f with
  | neg f _ => cases f <;> simp_all [cosafety, dual, Rewrites.to_nnf, safety]
  | _ => simp_all [cosafety, dual, Rewrites.to_nnf, safety]

theorem sigma2_dual_pi2 (h : Sigma2 f) : Pi2 (dual f) := by
  induction h with
  | base hs => exact .base (safety_dual_cosafety _ hs)
  | conj _ _ ih ih' => exact .disj ih ih'
  | disj _ _ ih ih' => exact .conj ih ih'
  | next _ ih => exact .next ih
  | eventual _ ih => exact .global ih
  | «until» _ _ ih ih' => exact .release ih ih'
  | strongRelease _ _ ih ih' => exact .weakUntil ih ih'

theorem pi2_dual_sigma2 (h : Pi2 f) : Sigma2 (dual f) := by
  induction h with
  | base hc => exact .base (cosafety_dual_safety _ hc)
  | conj _ _ ih ih' => exact .disj ih ih'
  | disj _ _ ih ih' => exact .conj ih ih'
  | next _ ih => exact .next ih
  | global _ ih => exact .eventual ih
  | release _ _ ih ih' => exact .until ih ih'
  | weakUntil _ _ ih ih' => exact .strongRelease ih ih'

theorem nnf_to_nnf (f : Formula α) (hn : NNF f) (pol : Bool) :
    NNF (Rewrites.to_nnf f pol false) := by
  induction f generalizing pol with
  | neg f _ => cases f <;> cases pol <;> simp_all [NNF, Rewrites.to_nnf]
  | _ => cases pol <;> simp_all [NNF, Rewrites.to_nnf]

theorem dual_nnf (f : Formula α) (hn : NNF f) : NNF (dual f) := nnf_to_nnf f hn false

/-- The complemented Boolean substitution associated with modal renaming.
On an AP it simplifies to its original valuation. -/
def dualAssignment (σ : Assignment ap) (a : Formula (Fin ap)) : Bool :=
  !propEval σ (dual a)

theorem dual_eval (f : Formula (Fin ap)) (hn : NNF f) (σ : Assignment ap) :
    propEval σ (dual f) = !propEval (dualAssignment σ) f := by
  induction f with
  | tt | ff | ap _ => simp [dual, Rewrites.to_nnf, propEval, dualAssignment]
  | neg f _ => cases f <;> simp_all [NNF, dual, Rewrites.to_nnf, propEval, dualAssignment]
  | conj f g ih ih' =>
    change (propEval σ (dual f) || propEval σ (dual g)) = _
    rw [ih hn.1, ih' hn.2]
    simp [propEval, Bool.not_and]
  | disj f g ih ih' =>
    change (propEval σ (dual f) && propEval σ (dual g)) = _
    rw [ih hn.1, ih' hn.2]
    simp [propEval, Bool.not_or]
  | impl _ _ _ _ | equiv _ _ _ _ | strongNext _ _ => contradiction
  | _ => simp only [propEval, dualAssignment, Bool.not_not]

/-- NNF dualization is well-defined on canonical classes, rather than just
on the syntax selected to represent a class. -/
theorem dual_class_congr (f g : Formula (Fin ap)) (hf : NNF f) (hg : NNF g)
    (he : Class.ofFormula f = Class.ofFormula g) :
    Class.ofFormula (dual f) = Class.ofFormula (dual g) := by
  apply Class.ext
  intro σ
  change propEval σ (dual f) = propEval σ (dual g)
  rw [dual_eval f hf, dual_eval g hg]
  exact congrArg Bool.not (congrArg (fun x : Class ap => x (dualAssignment σ)) he)

/-- Exact support, not syntactic membership of the original representative,
suffices for the Σ₂-to-Π₂ orientation. Absorbed syntax stays irrelevant. -/
theorem class_sigma2_dual_pi2 (f : Formula (Fin ap)) (hn : NNF f)
    (hs : HasTag Sigma2 (Class.ofFormula f)) :
    HasTag Pi2 (Class.ofFormula (dual f)) := by
  classical
  intro b hb
  apply Classical.byContradiction
  intro hbad
  obtain ⟨σ, v, hne⟩ := hb
  apply hne
  change propEval (setAtom σ b v) (dual f) = propEval σ (dual f)
  rw [dual_eval f hn, dual_eval f hn]
  apply congrArg Bool.not
  apply support_locality (Class.ofFormula f)
  intro a ha
  have hdual : HasTag Pi2 (Class.ofFormula (dual a)) :=
    syntax_tag_lower (dual a) .pi2 (sigma2_dual_pi2 (hs a ha))
  have hnu : ¬Uses (Class.ofFormula (dual a)) b := fun h => hbad (hdual b h)
  exact congrArg Bool.not (not_uses hnu σ v)

theorem classTag_sigma2_dual_pi2 (f : Formula (Fin ap)) (hn : NNF f)
    (hs : classTag .sigma2 f = true) : classTag .pi2 (dual f) = true :=
  (classTag_exact .pi2 (dual f)).mpr
    (class_sigma2_dual_pi2 f hn ((classTag_exact .sigma2 f).mp hs))

theorem dual_language (f : Formula (Fin ap)) (w : Word (Fin ap)) (j : Nat) :
    Sat none w (dual f) j ↔ ¬Sat none w f j := by
  simpa only [dual, Bool.false_eq_true, ↓reduceIte] using
    (Rewrites.nnf_sat (len := none) (fin := false) (Or.inr rfl) f false w (j := j) trivial)

/-- Every research Σ₂ support class has a correct complete dual run. -/
theorem sigma2_language (f : Formula (Fin ap)) (hn : NNF f)
    (hs : classTag .sigma2 f = true) (w : Word (Fin ap)) :
    FinMarks (marks (dual f) w) ↔ Sat none w f 0 := by
  classical
  rw [pi2_complement (dual f) (dual_nnf f hn) (classTag_sigma2_dual_pi2 f hn hs),
    dual_language, Classical.not_not]

theorem sigma2_parity (f : Formula (Fin ap)) (hn : NNF f)
    (hs : classTag .sigma2 f = true) (w : Word (Fin ap)) :
    (MinEven (oneSetMin true (marks (dual f) w)) ↔ Sat none w f 0) ∧
    (MaxOdd (oneSetExport true (marks (dual f) w)) ↔ Sat none w f 0) :=
  ⟨(oneSet_min_fin _).trans (sigma2_language f hn hs w),
    (oneSet_max_fin _).trans (sigma2_language f hn hs w)⟩

/-- The fresh-component orientation in `component`, before colour sharing. -/
def orientedFormula (f : Formula (Fin ap)) : Formula (Fin ap) :=
  if classTag .pi2 f then f else dual f

def complemented (f : Formula (Fin ap)) : Bool := !classTag .pi2 f

def componentMin (f : Formula (Fin ap)) (w : Word (Fin ap)) : Nat → Nat :=
  oneSetMin (complemented f) (marks (orientedFormula f) w)

def componentMax (f : Formula (Fin ap)) (w : Word (Fin ap)) : Nat → Nat :=
  oneSetExport (complemented f) (marks (orientedFormula f) w)

/-- Both numeric parity languages for every accepted research whole class,
including canonical support mixtures that are not syntactically Σ₂/Π₂. -/
theorem research_component_language (f : Formula (Fin ap)) (hn : NNF f)
    (ha : researchAdmitted f = true) (w : Word (Fin ap)) :
    (MinEven (componentMin f w) ↔ Sat none w f 0) ∧
    (MaxOdd (componentMax f w) ↔ Sat none w f 0) := by
  cases hpi : classTag .pi2 f
  · have hs : classTag .sigma2 f = true := by simpa [researchAdmitted, hpi] using ha
    simpa only [componentMin, componentMax, orientedFormula, complemented, hpi,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false] using sigma2_parity f hn hs w
  · simpa only [componentMin, componentMax, orientedFormula, complemented, hpi,
      ↓reduceIte, Bool.not_true] using pi2_parity f hn hpi w

end Tlsf.Dpa.Impl
