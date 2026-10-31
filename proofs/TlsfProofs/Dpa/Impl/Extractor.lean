import TlsfProofs.Dpa.Impl.Tags

/-!
# Executable research-mode extractor

Reference for `src/lib/dpa_formula.c:664` (REDUCE and DROP_X), `:891`/`:914`
(syntactic protection from current support), and `:938` (elision and retry).
The definitions run on formula representatives; every equality decision uses
the executable canonical truth tables, never structural formula equality.
Theorems identify their results with the semantic classes of `Classes.lean`.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

def isAPb : Formula α → Bool
  | .ap _ => true | _ => false

def isXb : Formula α → Bool
  | .next _ => true | _ => false

def nonXModalb : Formula α → Bool
  | .eventually _ | .globally _ | .until _ _ | .release _ _
  | .weakUntil _ _ | .strongRelease _ _ => true
  | _ => false

theorem isAPb_exact (a : Formula α) : isAPb a = true ↔ isAP a := by
  cases a <;> simp [isAPb, isAP]

theorem isXb_exact (a : Formula α) : isXb a = true ↔ isX a := by
  cases a <;> simp [isXb, isX]

theorem nonXModalb_exact (a : Formula α) : nonXModalb a = true ↔ nonXModal a := by
  cases a <;> simp [nonXModalb, nonXModal]

def protectedb (f t : Formula (Fin ap)) : Bool :=
  (modalAtoms f).any (fun a => uses f a && nonXModalb a && decide (t ∈ subformulas a))

theorem protected_exact (f t : Formula (Fin ap)) :
    protectedb f t = true ↔ Protected (Class.ofFormula f) t := by
  simp only [protectedb, List.any_eq_true, Bool.and_eq_true, uses_exact,
    nonXModalb_exact, decide_eq_true_eq]
  constructor
  · rintro ⟨a, _, ⟨ha, hm⟩, ht⟩; exact ⟨a, ha, hm, ht⟩
  · rintro ⟨a, ha, hm, ht⟩
    exact ⟨a, uses_in_bound (fun σ τ hh => propEval_local f σ τ hh) ha, ⟨ha, hm⟩, ht⟩

/-- Simultaneous substitution; frozen modal operands are not traversed. -/
def replace (p : Formula (Fin ap) → Bool) : Formula (Fin ap) → Formula (Fin ap)
  | .tt => .tt | .ff => .ff
  | .neg f => .neg (replace p f)
  | .conj f g => .conj (replace p f) (replace p g)
  | .disj f g => .disj (replace p f) (replace p g)
  | .impl f g => .impl (replace p f) (replace p g)
  | .equiv f g => .equiv (replace p f) (replace p g)
  | f => if p f then .tt else f

theorem replace_eval (p : Formula (Fin ap) → Bool) (f : Formula (Fin ap))
    (σ : Assignment ap) :
    propEval σ (replace p f) = propEval (fun a => if p a then true else σ a) f := by
  induction f with
  | tt | ff => rfl
  | neg f ih => simp only [replace, propEval, ih]
  | conj f g ih ih' | disj f g ih ih' | impl f g ih ih' | equiv f g ih ih' =>
    simp only [replace, propEval, ih, ih']
  | _ => simp only [replace]; split <;> simp_all [propEval]

theorem replace_exact (p : Formula (Fin ap) → Bool) (f : Formula (Fin ap)) :
    Class.ofFormula (replace p f) = replaceTrue (fun a => p a = true) (Class.ofFormula f) := by
  apply Class.ext
  intro σ
  change propEval σ (replace p f) = propEval _ f
  rw [replace_eval]
  congr 1
  funext a
  by_cases h : p a = true <;> simp [h]

def reduce (f : Formula (Fin ap)) : Formula (Fin ap) :=
  replace (fun a => !isAPb a && !cosafetyb a) f

theorem reduce_exact (f : Formula (Fin ap)) :
    Class.ofFormula (reduce f) = Dpa.reduce (Class.ofFormula f) := by
  rw [reduce, replace_exact]
  have hp : (fun a : Formula (Fin ap) => (!isAPb a && !cosafetyb a) = true) =
      (fun a => ¬isAP a ∧ ¬cosafety a) := by
    funext a
    simp [Bool.eq_false_iff, isAPb_exact, cosafetyb_exact]
  rw [hp]
  rfl

def dropX (f : Formula (Fin ap)) : Formula (Fin ap) :=
  replace (fun a => isXb a && !protectedb f a) f

theorem dropX_exact (f : Formula (Fin ap)) :
    Class.ofFormula (dropX f) = Dpa.dropX (Class.ofFormula f) := by
  rw [dropX, replace_exact]
  have hp : (fun a : Formula (Fin ap) => (isXb a && !protectedb f a) = true) =
      (fun a => isX a ∧ ¬Protected (Class.ofFormula f) a) := by
    funext a
    simp [Bool.eq_false_iff, isXb_exact, protected_exact]
  rw [hp]
  rfl

def elideFuel : Nat → Formula (Fin ap) → Formula (Fin ap)
  | 0, f => f
  | n+1, f => if equivalent (dropX f) f then f else elideFuel n (dropX f)

theorem elideFuel_exact (n : Nat) (f : Formula (Fin ap)) :
    Class.ofFormula (elideFuel n f) = Dpa.elideFuel n (Class.ofFormula f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [elideFuel, Dpa.elideFuel]
    have ht : equivalent (dropX f) f = true ↔ Dpa.dropX (Class.ofFormula f) = Class.ofFormula f := by
      rw [equivalent_exact, dropX_exact]
    by_cases h : Dpa.dropX (Class.ofFormula f) = Class.ofFormula f
    · simp [h, ht.mpr h]
    · simp only [h, ↓reduceIte, show equivalent (dropX f) f = false from Bool.eq_false_iff.mpr (fun he => h (ht.mp he))]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih, dropX_exact]

theorem semantic_elideFuel_fixed (n : Nat) (x : Class ap) (h : Dpa.dropX x = x) :
    Dpa.elideFuel n x = x := by
  cases n <;> simp [Dpa.elideFuel, h]

theorem semantic_elideFuel_add (n m : Nat) (x : Class ap) :
    Dpa.elideFuel (n+m) x = Dpa.elideFuel m (Dpa.elideFuel n x) := by
  classical
  induction n generalizing x with
  | zero => simp only [Nat.zero_add, Dpa.elideFuel]
  | succ n ih =>
    by_cases h : Dpa.dropX x = x
    · rw [semantic_elideFuel_fixed (n+1+m) x h, semantic_elideFuel_fixed (n+1) x h,
        semantic_elideFuel_fixed m x h]
    · simpa only [Nat.succ_add, Dpa.elideFuel, h, ↓reduceIte] using ih (Dpa.dropX x)

/-- Any two sufficiently long bounded elision runs agree. This removes the
semantic model's arbitrary representative from the executable fuel bound. -/
theorem semantic_elideFuel_unique (n m : Nat) (x : Class ap)
    (hn : Dpa.dropX (Dpa.elideFuel n x) = Dpa.elideFuel n x)
    (hm : Dpa.dropX (Dpa.elideFuel m x) = Dpa.elideFuel m x) :
    Dpa.elideFuel n x = Dpa.elideFuel m x := by
  calc
    _ = Dpa.elideFuel m (Dpa.elideFuel n x) := (semantic_elideFuel_fixed _ _ hn).symm
    _ = Dpa.elideFuel (n+m) x := (semantic_elideFuel_add ..).symm
    _ = Dpa.elideFuel (m+n) x := by rw [Nat.add_comm]
    _ = Dpa.elideFuel n (Dpa.elideFuel m x) := semantic_elideFuel_add ..
    _ = _ := semantic_elideFuel_fixed _ _ hm

def elide (f : Formula (Fin ap)) : Formula (Fin ap) := elideFuel (modalAtoms f).length f

theorem elide_exact (f : Formula (Fin ap)) :
    Class.ofFormula (elide f) = Dpa.elide (Class.ofFormula f) := by
  rw [elide, elideFuel_exact]
  apply semantic_elideFuel_unique
  · apply elideFuel_stable _ _ (modalAtoms f)
    · intro σ τ h; exact propEval_local f σ τ h
    · exact List.length_filter_le _ _
  · exact elide_stable _

def extractPass (f : Formula (Fin ap)) : Formula (Fin ap) := unfoldSyntax (elide (reduce f))

theorem extractPass_exact (f : Formula (Fin ap)) :
    Class.ofFormula (extractPass f) = Dpa.extractPass (Class.ofFormula f) := by
  rw [extractPass, ← U_ofFormula, elide_exact, reduce_exact]
  rfl

def rho (f : Formula (Fin ap)) : Formula (Fin ap) :=
  let first := extractPass f
  if classTag .finite first && !equivalent f (unfoldSyntax f)
  then extractPass (unfoldSyntax f) else first

theorem rho_exact (f : Formula (Fin ap)) :
    Class.ofFormula (rho f) = Dpa.rho (Class.ofFormula f) := by
  classical
  have ht : (classTag .finite (extractPass f) && !equivalent f (unfoldSyntax f)) = true ↔
      HasTag finite (Dpa.extractPass (Class.ofFormula f)) ∧
        Class.ofFormula f ≠ U (Class.ofFormula f) := by
    simp only [Bool.and_eq_true, classTag_exact, fragmentSyntax,
      Bool.not_eq_true', extractPass_exact]
    simp only [Bool.eq_false_iff, ne_eq, equivalent_exact, ← U_ofFormula]
  simp only [rho, Dpa.rho]
  split
  · rename_i h
    rw [ite_eq_left (ht.mp h), extractPass_exact, ← U_ofFormula]
  · rename_i h
    rw [ite_eq_right (fun hc => h (ht.mpr hc)), extractPass_exact]

end Tlsf.Dpa.Impl
