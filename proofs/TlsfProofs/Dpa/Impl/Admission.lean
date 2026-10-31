import TlsfProofs.Dpa.Impl.Dual

/-!
# Executable canonical research admission and grouping decisions

The full canonical success domain of `src/lib/dpa_formula.c:505`
(`check_admission`) is the support-wise union of the Π₂/Σ₂ atom grammars.
`canonicalResearchCheck_exact` and `canonicalResearchCheck_shannon` justify
that domain independently of a particular BDD variable order. They do not
yet simulate allocation of components by `syntax_acceptance`.

`compatibleGroups` implements the actual folded-class identity comparison
at `src/lib/dpa_formula.c:597`; a nonempty operand list can fold to identity.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

def canonicalResearchCheck (f : Formula (Fin ap)) : Bool :=
  hasTag (fun a => pi2b a || sigma2b a) f

theorem canonicalResearchCheck_exact (f : Formula (Fin ap)) :
    canonicalResearchCheck f = true ↔
      HasTag (fun a => Pi2 a ∨ Sigma2 a) (Class.ofFormula f) := by
  rw [canonicalResearchCheck, hasTag_exact]
  simp only [HasTag, Bool.or_eq_true, pi2b_exact, sigma2b_exact]

theorem researchAdmitted_check (f : Formula (Fin ap)) (ha : researchAdmitted f = true) :
    canonicalResearchCheck f = true := by
  apply (canonicalResearchCheck_exact f).mpr
  rcases (researchAdmitted_exact f).mp ha with hp | hs
  · exact fun a ha => Or.inl (hp a ha)
  · exact fun a ha => Or.inr (hs a ha)

/-- The exact supported-top / low / high recursion of the C admission check.
The whole-class fast path above implies this same domain. -/
theorem canonicalResearchCheck_shannon {f low high : Formula (Fin ap)} {a : Formula (Fin ap)}
    (ha : Uses (Class.ofFormula f) a)
    (hl : ∀ σ, propEval σ low = propEval (setAtom σ a false) f)
    (hh : ∀ σ, propEval σ high = propEval (setAtom σ a true) f) :
    canonicalResearchCheck f = true ↔ (Pi2 a ∨ Sigma2 a) ∧
      canonicalResearchCheck low = true ∧ canonicalResearchCheck high = true := by
  simp only [canonicalResearchCheck_exact]
  exact tags_shannon_intersection ha hl hh

def compatibleGroups (op : Bool) (S C B T : List (Formula (Fin ap))) : List (Formula (Fin ap)) :=
  if equivalent (booleanFold op C) (booleanIdentity op) then
    booleanFold op (S++B) :: booleanFold op C :: T
  else booleanFold op S :: booleanFold op (C++B) :: T

theorem compatibleGroups_exact (op : Bool) (S C B T : List (Formula (Fin ap))) :
    compatibleGroups op S C B T = Dpa.compatibleGroups op S C B T := by
  classical
  simp only [compatibleGroups, equivalent_exact, Dpa.compatibleGroups]

theorem compatibleGroups_language (op : Bool) (S C B T : List (Formula (Fin ap)))
    (w : Word (Fin ap)) (n : Nat) :
    Sat none w (booleanFold op (compatibleGroups op S C B T)) n ↔
      Sat none w (booleanFold op (S++C++B++T)) n := by
  rw [compatibleGroups_exact]
  exact compatibleGroups_sat op S C B T w n

end Tlsf.Dpa.Impl
