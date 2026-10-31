import TlsfProofs.Dpa.Impl.Classes
import TlsfProofs.Dpa.Refinements

/-!
# Executable structural fragment tags

These are the five bits of `src/lib/dpa_internal.h:10`, computed by the
operator transfers in `src/lib/dpa_formula.c:254` (`term`) and `:207`
(`dpa_atom`). `classTag` performs the exact support intersection of
`src/lib/dpa_formula.c:81` in research mode. That mode deliberately does not
recursively refine frozen modal operands. Default-mode refinement is a
separate algorithm and is not identified with these structural predicates.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

def finiteb : Formula α → Bool
  | .tt | .ff | .ap _ | .neg (.ap _) => true
  | .conj f g | .disj f g => finiteb f && finiteb g
  | .next f => finiteb f
  | _ => false

def safetyb : Formula α → Bool
  | .tt | .ff | .ap _ | .neg (.ap _) => true
  | .conj f g | .disj f g | .release f g | .weakUntil f g => safetyb f && safetyb g
  | .next f | .globally f => safetyb f
  | _ => false

def cosafetyb : Formula α → Bool
  | .tt | .ff | .ap _ | .neg (.ap _) => true
  | .conj f g | .disj f g | .until f g | .strongRelease f g => cosafetyb f && cosafetyb g
  | .next f | .eventually f => cosafetyb f
  | _ => false

theorem finiteb_exact (f : Formula α) : finiteb f = true ↔ finite f := by
  induction f with
  | neg f _ => cases f <;> simp [finiteb, finite]
  | _ => simp_all [finiteb, finite]

theorem safetyb_exact (f : Formula α) : safetyb f = true ↔ safety f := by
  induction f with
  | neg f _ => cases f <;> simp [safetyb, safety]
  | _ => simp_all [safetyb, safety]

theorem cosafetyb_exact (f : Formula α) : cosafetyb f = true ↔ cosafety f := by
  induction f with
  | neg f _ => cases f <;> simp [cosafetyb, cosafety]
  | _ => simp_all [cosafetyb, cosafety]

def pi2b : Formula α → Bool
  | .tt | .ff | .ap _ | .neg (.ap _) => true
  | .conj f g | .disj f g | .release f g | .weakUntil f g => pi2b f && pi2b g
  | .next f | .globally f => pi2b f
  | .eventually f => cosafetyb f
  | .until f g | .strongRelease f g => cosafetyb f && cosafetyb g
  | _ => false

def sigma2b : Formula α → Bool
  | .tt | .ff | .ap _ | .neg (.ap _) => true
  | .conj f g | .disj f g | .until f g | .strongRelease f g => sigma2b f && sigma2b g
  | .next f | .eventually f => sigma2b f
  | .globally f => safetyb f
  | .release f g | .weakUntil f g => safetyb f && safetyb g
  | _ => false

theorem cosafety_pi2b (h : cosafety f) : pi2b f = true := by
  induction f with
  | neg f _ => cases f <;> simp_all [cosafety, pi2b]
  | _ => simp_all [cosafety, pi2b, cosafetyb_exact]

theorem safety_sigma2b (h : safety f) : sigma2b f = true := by
  induction f with
  | neg f _ => cases f <;> simp_all [safety, sigma2b]
  | _ => simp_all [safety, sigma2b, safetyb_exact]

theorem pi2b_sound (f : Formula α) (h : pi2b f = true) : Pi2 f := by
  induction f with
  | tt | ff | ap _ => exact .base trivial
  | neg f _ =>
    cases f <;> simp only [pi2b, Bool.false_eq_true] at h
    exact .base trivial
  | conj f g ih ih' => exact .conj (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | disj f g ih ih' => exact .disj (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | next f ih => exact .next (ih h)
  | globally f ih => exact .global (ih h)
  | release f g ih ih' => exact .release (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | weakUntil f g ih ih' => exact .weakUntil (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | eventually f _ => exact .base ((cosafetyb_exact f).mp h)
  | «until» f g _ _ | strongRelease f g _ _ =>
    exact .base ⟨(cosafetyb_exact f).mp (Bool.and_eq_true_iff.mp h).1,
      (cosafetyb_exact g).mp (Bool.and_eq_true_iff.mp h).2⟩
  | _ => contradiction

theorem pi2b_exact (f : Formula α) : pi2b f = true ↔ Pi2 f := by
  refine ⟨pi2b_sound f, ?_⟩
  intro h
  induction h with
  | base hc => exact cosafety_pi2b hc
  | _ => simp_all [pi2b]

theorem sigma2b_sound (f : Formula α) (h : sigma2b f = true) : Sigma2 f := by
  induction f with
  | tt | ff | ap _ => exact .base trivial
  | neg f _ =>
    cases f <;> simp only [sigma2b, Bool.false_eq_true] at h
    exact .base trivial
  | conj f g ih ih' => exact .conj (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | disj f g ih ih' => exact .disj (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | next f ih => exact .next (ih h)
  | eventually f ih => exact .eventual (ih h)
  | «until» f g ih ih' => exact .until (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | strongRelease f g ih ih' => exact .strongRelease (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | globally f _ => exact .base ((safetyb_exact f).mp h)
  | release f g _ _ | weakUntil f g _ _ =>
    exact .base ⟨(safetyb_exact f).mp (Bool.and_eq_true_iff.mp h).1,
      (safetyb_exact g).mp (Bool.and_eq_true_iff.mp h).2⟩
  | _ => contradiction

theorem sigma2b_exact (f : Formula α) : sigma2b f = true ↔ Sigma2 f := by
  refine ⟨sigma2b_sound f, ?_⟩
  intro h
  induction h with
  | base hs => exact safety_sigma2b hs
  | _ => simp_all [sigma2b]

def syntaxTag : FragmentTag → Formula α → Bool
  | .finite => finiteb | .safety => safetyb | .cosafety => cosafetyb
  | .pi2 => pi2b | .sigma2 => sigma2b

theorem syntaxTag_exact (t : FragmentTag) (f : Formula α) :
    syntaxTag t f = true ↔ fragmentSyntax t f := by
  cases t
  · exact finiteb_exact f
  · exact safetyb_exact f
  · exact cosafetyb_exact f
  · exact pi2b_exact f
  · exact sigma2b_exact f

def classTag (t : FragmentTag) (f : Formula (Fin ap)) : Bool := hasTag (syntaxTag t) f

theorem classTag_exact (t : FragmentTag) (f : Formula (Fin ap)) :
    classTag t f = true ↔ HasTag (fragmentSyntax t) (Class.ofFormula f) := by
  rw [classTag, hasTag_exact]
  constructor
  · intro h a ha; exact (syntaxTag_exact t a).mp (h a ha)
  · intro h a ha; exact (syntaxTag_exact t a).mpr (h a ha)

/-- The research whole-class fast path, not the Boolean acceptance recursion
or the grouped constructor. C: `dpa_admitted`, research branch, line 191. -/
def researchAdmitted (f : Formula (Fin ap)) : Bool := classTag .pi2 f || classTag .sigma2 f

theorem researchAdmitted_exact (f : Formula (Fin ap)) :
    researchAdmitted f = true ↔
      HasTag Pi2 (Class.ofFormula f) ∨ HasTag Sigma2 (Class.ofFormula f) := by
  simp only [researchAdmitted, Bool.or_eq_true, classTag_exact, fragmentSyntax]

/-- The bit numbering is shared with `dpa_internal.h`. -/
def tagMask (f : Formula (Fin ap)) : Nat :=
  (if classTag .finite f then 1 else 0) +
  (if classTag .safety f then 2 else 0) +
  (if classTag .cosafety f then 4 else 0) +
  (if classTag .pi2 f then 8 else 0) +
  (if classTag .sigma2 f then 16 else 0)

end Tlsf.Dpa.Impl
