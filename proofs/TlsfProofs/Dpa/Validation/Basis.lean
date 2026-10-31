import TlsfProofs.Dpa.Impl.Assembly

/-! Compile a plan over a fixed global basis of distinct oriented components.
The basis is chosen before any component runs. This is a pure finite product
presentation, independent of C allocation, caches, traces and evaluation order. -/
namespace Tlsf.Dpa.Impl
variable {ap : Nat}

def AcceptancePlan.atoms : AcceptancePlan ap → List (Formula (Fin ap))
  | .constant _ => []
  | .whole f => [f]
  | .binary _ p q => p.atoms ++ q.atoms
  | .shannon a p q => a :: (p.atoms ++ q.atoms)

theorem AcceptancePlan.atoms_valid (p : AcceptancePlan ap) (hp : p.Valid) :
    ∀ f, f ∈ p.atoms → NNF f ∧ researchAdmitted f = true := by
  induction p with
  | constant _ => simp [atoms]
  | whole f =>
    intro g hg
    have he : g = f := by simpa [atoms] using hg
    subst g
    exact hp
  | binary _ p q ih ih' =>
    intro f hf
    exact (List.mem_append.mp hf).elim (ih hp.1 f) (ih' hp.2 f)
  | shannon a p q ih ih' =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hp.1
    · exact (List.mem_append.mp hf).elim (ih hp.2.1 f) (ih' hp.2.2 f)

def AcceptancePlan.basis (p : AcceptancePlan ap) : ComponentStore ap :=
  (p.atoms.map freshComponent).eraseDups

theorem AcceptancePlan.basis_covers (p : AcceptancePlan ap) (f : Formula (Fin ap))
    (hf : f ∈ p.atoms) : freshComponent f ∈ p.basis := by
  simp [basis, List.mem_map.mpr ⟨f, hf, rfl⟩]

theorem AcceptancePlan.basis_valid (p : AcceptancePlan ap) (hp : p.Valid) :
    StoreValid p.basis := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp he)
  exact freshComponent_valid f (p.atoms_valid hp f hf).1 (p.atoms_valid hp f hf).2

def basisLiteral (s : ComponentStore ap) (f : Formula (Fin ap)) : ColourLiteral :=
  ⟨s.idxOf (freshComponent f), complemented f⟩

theorem basisLiteral_represents (s : ComponentStore ap) (f : Formula (Fin ap))
    (hf : freshComponent f ∈ s) : LiteralRepresents s (basisLiteral s f) f := by
  refine ⟨freshComponent f, ?_, ?_⟩
  · have hi := List.idxOf_lt_length_of_mem hf
    simp only [basisLiteral]
    rw [List.getElem?_eq_getElem hi, List.getElem_idxOf hi]
  · cases hp : classTag .pi2 f <;>
      simp [basisLiteral, freshComponent, complemented, orientedFormula, hp]

theorem basisLiteral_bound (s : ComponentStore ap) (f : Formula (Fin ap))
    (hf : freshComponent f ∈ s) : (basisLiteral s f).index < s.length :=
  List.idxOf_lt_length_of_mem hf

def AcceptancePlan.compileInBasis (s : ComponentStore ap) : AcceptancePlan ap → ColourAcceptance
  | .constant b => .constant b
  | .whole f => .literal (basisLiteral s f)
  | .binary op p q => .binary op (p.compileInBasis s) (q.compileInBasis s)
  | .shannon a p q => .ite (basisLiteral s a) (p.compileInBasis s) (q.compileInBasis s)

theorem AcceptancePlan.compileInBasis_spec (p : AcceptancePlan ap) (s : ComponentStore ap)
    (hs : StoreValid s) (cover : ∀ f, f ∈ p.atoms → freshComponent f ∈ s) :
    (p.compileInBasis s).Bounded s.length ∧
      ∀ w, (p.compileInBasis s).eval (storeTruth s w) = true ↔ Sat none w p.source 0 := by
  induction p with
  | constant b =>
    refine ⟨trivial, ?_⟩
    intro w; cases b <;> simp [compileInBasis, ColourAcceptance.eval, source, Sat, InRange]
  | whole f =>
    have hf := cover f (by simp [atoms])
    exact ⟨basisLiteral_bound s f hf,
      fun w => literal_language s hs (basisLiteral s f) f (basisLiteral_represents s f hf) w⟩
  | binary op p q ih ih' =>
    obtain ⟨bp, lp⟩ := ih (fun f hf => cover f (by simp [atoms, hf]))
    obtain ⟨bq, lq⟩ := ih' (fun f hf => cover f (by simp [atoms, hf]))
    refine ⟨⟨bp, bq⟩, ?_⟩
    intro w
    cases op <;> simp only [compileInBasis, ColourAcceptance.eval, Bool.false_eq_true,
      ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, lp, lq, source, Sat, InRange, true_and]
  | shannon a p q ih ih' =>
    have ha := cover a (by simp [atoms])
    have lt := literal_language s hs (basisLiteral s a) a (basisLiteral_represents s a ha)
    obtain ⟨bp, lp⟩ := ih (fun f hf => cover f (by simp [atoms, hf]))
    obtain ⟨bq, lq⟩ := ih' (fun f hf => cover f (by simp [atoms, hf]))
    refine ⟨⟨basisLiteral_bound s a ha, bp, bq⟩, ?_⟩
    intro w
    simp only [compileInBasis, ColourAcceptance.eval]
    cases hc : (basisLiteral s a).eval (storeTruth s w) with
    | false =>
      have hn : ¬Sat none w a 0 := by
        intro hh
        have ht := (lt w).mpr hh
        rw [hc] at ht
        contradiction
      simp only [Bool.false_eq_true, ↓reduceIte, lq w, source, Sat, InRange,
        true_and, hn, false_and, false_or, not_false_eq_true]
    | true =>
      have ht := (lt w).mp hc
      simp only [↓reduceIte, lp w, source, Sat, InRange, true_and, ht,
        not_true_eq_false, false_and, or_false]

def compileBasis (p : AcceptancePlan ap) : Assembly ap := ⟨p.basis, p.compileInBasis p.basis⟩

theorem compileBasis_presentation (p : AcceptancePlan ap) (hp : p.Valid) :
    ProductPresentation p.source (storeClasses (compileBasis p).store) (compileBasis p).skeleton := by
  have hv := p.basis_valid hp
  obtain ⟨hb, hl⟩ := p.compileInBasis_spec p.basis hv p.basis_covers
  constructor
  · intro i w
    have hi : i.val < p.basis.length := i.isLt
    have he : p.basis[i.val]? = some p.basis[i.val] := List.getElem?_eq_getElem i.isLt
    have hc := storeColour_language p.basis hv i.val _ he w
    simpa only [compileBasis, storeClasses, marks_exact, storeColours, he] using
      hc.trans (ofFormula_holds _).symm
  · intro w
    have he := (p.compileInBasis p.basis).eval_local hb
      (finiteValuation _ (componentTruth (storeClasses p.basis) w)) (storeTruth p.basis w) (by
        intro i hi
        simp only [finiteValuation, hi, ↓reduceDIte]
        exact (storeTruth_componentTruth _ hv w ⟨i, hi⟩).symm)
    change (p.compileInBasis p.basis).eval
      (finiteValuation p.basis.length (componentTruth (storeClasses p.basis) w)) = true ↔ _
    rw [he]
    exact hl w

end Tlsf.Dpa.Impl
