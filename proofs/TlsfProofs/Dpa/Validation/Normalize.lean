import TlsfProofs.Dpa.Validation.Finite

/-! Pure Boolean simplification under modalities, with a language proof.
This extends the reference's usable syntax without imitating C admission,
tag caches or operand allocation. Every replacement is independently tested
by the proved propositional class equality. -/
namespace Tlsf.Dpa.Impl
variable {ap : Nat}

def booleanCandidates : Formula (Fin ap) → List (Formula (Fin ap))
  | .conj f g | .disj f g | .impl f g | .equiv f g => [.ff, .tt, f, g]
  | .neg _ => [.ff, .tt]
  | _ => []

def simplifyBoolean (f : Formula (Fin ap)) : Formula (Fin ap) :=
  ((booleanCandidates f).find? (equivalent f)).getD f

theorem simplifyBoolean_class (f : Formula (Fin ap)) :
    Class.ofFormula (simplifyBoolean f) = Class.ofFormula f := by
  unfold simplifyBoolean
  cases h : (booleanCandidates f).find? (equivalent f) with
  | none => rfl
  | some g => exact ((equivalent_exact f g).mp (List.find?_some h)).symm

def normalize (f : Formula (Fin ap)) : Formula (Fin ap) :=
  Rewrites.bottom_up simplifyBoolean f

theorem normalize_language (f : Formula (Fin ap)) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (normalize f) n ↔ Sat none w f n := by
  apply Rewrites.bottom_up_exact (fin := false) simplifyBoolean
    (fun g len hl w n _ => ?_) f none (Or.inr rfl) w n trivial
  have he : len = none := by simpa using hl
  subst len
  exact class_language (simplifyBoolean_class g) w n

theorem normalized_finite_construction_language (rank atomRank : Formula (Fin ap) → Nat)
    (f : Formula (Fin ap)) (ha : transportedResearchCheck rank (normalize f) = true)
    (r : Assembly ap) (hc : construct rank atomRank (normalize f) = some r) :
    (∀ fuel table, r.exportParity fuel = some table → ∀ w,
      (table.parity r.finiteParitySource r.paritySame).Accepts w ↔
        Sat none (fun n => decode (w n)) f 0) ∧
    (positiveb r.skeleton = true → ∀ fuel table, r.exportBuchi fuel = some table → ∀ w,
      (table.buchi r.finiteBuchiSource r.buchiSame).Accepts w ↔
        Sat none (fun n => decode (w n)) f 0) := by
  obtain ⟨hp, hb⟩ := uncached_finite_construction_language rank atomRank (normalize f) ha r hc
  exact ⟨fun fuel table ht w => (hp fuel table ht w).trans (normalize_language f _ 0),
    fun hpos fuel table ht w => (hb hpos fuel table ht w).trans (normalize_language f _ 0)⟩

end Tlsf.Dpa.Impl
