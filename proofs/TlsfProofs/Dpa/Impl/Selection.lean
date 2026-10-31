import TlsfProofs.Dpa.Impl.Assembly
import TlsfProofs.Dpa.Impl.Transport

/-!
# Selecting the canonical acceptance plan

`src/lib/dpa_dela.c:117` first tests constants, then the acceptance cache,
then whole-class admission, and otherwise branches on the first supported
BDD variable. This module selects the resulting *uncached* plan, with
executable cofactors and a supplied atom-ID order. It proves validity and
source-class equality for the selected plan, and success on the exact
canonical research admission domain. It does not identify an uncached walk
with C's sequence of store calls: acceptance-cache hits, the unspecified
evaluation order of the two C child arguments, and the grouped syntax
selector are separate obligations.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

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

theorem cofactor_nnf (a f : Formula (Fin ap)) (value : Bool) (hf : NNF f) :
    NNF (cofactor a value f) := by
  induction f with
  | tt | ff => trivial
  | neg f _ =>
    cases f with
    | tt | ff => trivial
    | ap _ => simp only [cofactor]; split <;> cases value <;> trivial
    | _ => contradiction
  | conj _ _ ih ih' | disj _ _ ih ih' => exact ⟨ih hf.1, ih' hf.2⟩
  | impl _ _ _ _ | equiv _ _ _ _ | strongNext _ _ => contradiction
  | _ =>
    simp only [cofactor]
    split
    · cases value <;> trivial
    · exact hf

theorem modalAtom_eval (f a : Formula (Fin ap)) (ha : a ∈ modalAtoms f)
    (σ : Assignment ap) : propEval σ a = σ a := by
  induction f with
  | tt | ff => simp [modalAtoms] at ha
  | neg _ ih => exact ih ha
  | conj _ _ ih ih' | disj _ _ ih ih' | impl _ _ ih ih' | equiv _ _ ih ih' =>
    rcases List.mem_append.mp ha with h | h
    · exact ih h
    · exact ih' h
  | _ => simp only [modalAtoms, List.mem_singleton] at ha; subst a; rfl

theorem modalAtom_nnf (f a : Formula (Fin ap)) (hf : NNF f) (ha : a ∈ modalAtoms f) :
    NNF a := by
  induction f with
  | tt | ff => simp [modalAtoms] at ha
  | neg f _ => cases f <;> simp_all [NNF, modalAtoms]
  | conj _ _ ih ih' | disj _ _ ih ih' =>
    rcases List.mem_append.mp ha with h | h
    · exact ih hf.1 h
    · exact ih' hf.2 h
  | impl _ _ _ _ | equiv _ _ _ _ => contradiction
  | _ => simp only [modalAtoms, List.mem_singleton] at ha; subst a; exact hf

theorem modalAtom_uses (f a : Formula (Fin ap)) (ha : a ∈ modalAtoms f) :
    Uses (Class.ofFormula a) a := by
  refine ⟨fun _ => false, true, ?_⟩
  change propEval (setAtom (fun _ => false) a true) a ≠ propEval (fun _ => false) a
  rw [modalAtom_eval f a ha, modalAtom_eval f a ha]
  simp [setAtom]

theorem cofactor_shannon (f a : Formula (Fin ap)) (ha : a ∈ modalAtoms f) :
    Class.ofFormula (.disj (.conj a (cofactor a true f))
      (.conj (.neg a) (cofactor a false f))) = Class.ofFormula f := by
  apply Class.ext
  intro σ
  change (propEval σ a && propEval σ (cofactor a true f) ||
    !propEval σ a && propEval σ (cofactor a false f)) = propEval σ f
  rw [modalAtom_eval f a ha σ, cofactor_eval, cofactor_eval]
  have hw (b : Bool) (h : σ a = b) : setAtom σ a b = σ := by
    funext t
    by_cases he : t = a <;> simp_all [setAtom]
  cases h : σ a <;> simp [hw _ h]

/-- A supplied ordered alphabet is scanned only until its first essential
atom. Thus absorbed or previously cofactored variables never allocate a
component, just as a reduced BDD omits them. -/
def selectCanonicalPlan : List (Formula (Fin ap)) → Formula (Fin ap) → Option (AcceptancePlan ap)
  | atoms, f =>
    if equivalent f .ff then some (.constant false)
    else if equivalent f .tt then some (.constant true)
    else if researchAdmitted f then some (.whole f)
    else match atoms with
    | [] => none
    | a :: rest =>
      if uses f a then
        if researchAdmitted a then do
          let high ← selectCanonicalPlan rest (cofactor a true f)
          let low ← selectCanonicalPlan rest (cofactor a false f)
          pure (.shannon a high low)
        else none
      else selectCanonicalPlan rest f

theorem selectCanonicalPlan_spec (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (hf : NNF f) (p : AcceptancePlan ap)
    (hp : selectCanonicalPlan atoms f = some p) :
    p.Valid ∧ Class.ofFormula p.source = Class.ofFormula f := by
  induction atoms generalizing f p with
  | nil =>
    simp only [selectCanonicalPlan] at hp
    split at hp
    · rename_i h
      cases Option.some.inj hp
      exact ⟨trivial, ((equivalent_exact f .ff).mp h).symm⟩
    · split at hp
      · rename_i h
        cases Option.some.inj hp
        exact ⟨trivial, ((equivalent_exact f .tt).mp h).symm⟩
      · split at hp
        · rename_i h
          cases Option.some.inj hp
          exact ⟨⟨hf, h⟩, rfl⟩
        · simp at hp
  | cons a atoms ih =>
    simp only [selectCanonicalPlan] at hp
    split at hp
    · rename_i h
      cases Option.some.inj hp
      exact ⟨trivial, ((equivalent_exact f .ff).mp h).symm⟩
    · split at hp
      · rename_i h
        cases Option.some.inj hp
        exact ⟨trivial, ((equivalent_exact f .tt).mp h).symm⟩
      · split at hp
        · rename_i h
          cases Option.some.inj hp
          exact ⟨⟨hf, h⟩, rfl⟩
        · split at hp
          · rename_i hu
            have hm : a ∈ modalAtoms f := uses_in_bound
              (fun σ τ h => propEval_local f σ τ h) ((uses_exact f a).mp hu)
            split at hp
            · rename_i ha
              simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hp
              obtain ⟨high, hh, low, hl, rfl⟩ := hp
              obtain ⟨vh, eh⟩ := ih _ (cofactor_nnf a f true hf) high hh
              obtain ⟨vl, el⟩ := ih _ (cofactor_nnf a f false hf) low hl
              refine ⟨⟨⟨modalAtom_nnf f a hf hm, ha⟩, vh, vl⟩, ?_⟩
              apply Eq.trans _ (cofactor_shannon f a hm)
              apply Class.ext
              intro σ
              have eh' := congrArg (fun x : Class ap => x σ) eh
              have el' := congrArg (fun x : Class ap => x σ) el
              change propEval σ high.source = propEval σ (cofactor a true f) at eh'
              change propEval σ low.source = propEval σ (cofactor a false f) at el'
              simp only [AcceptancePlan.source, Class.ofFormula, propEval, eh', el']
            · simp at hp
          · exact ih f hf p hp

private theorem cofactor_dependsOn (a : Formula (Fin ap)) (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (value : Bool) (hd : (Class.ofFormula f).DependsOn (a :: atoms)) :
    (Class.ofFormula (cofactor a value f)).DependsOn atoms := by
  intro σ τ h
  change propEval σ (cofactor a value f) = propEval τ (cofactor a value f)
  rw [cofactor_eval, cofactor_eval]
  apply hd
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [setAtom]
  · by_cases he : b = a <;> simp [setAtom, he, h b hb]

private theorem skip_dependsOn (a : Formula (Fin ap)) (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (hd : (Class.ofFormula f).DependsOn (a :: atoms))
    (hu : uses f a = false) : (Class.ofFormula f).DependsOn atoms := by
  intro σ τ h
  apply support_locality
  intro b hb
  rcases List.mem_cons.mp (uses_in_bound hd hb) with rfl | hm
  · have he := (uses_exact f b).mpr hb
    simp [hu] at he
  · exact h b hm

private theorem admitted_supported_atom (f a : Formula (Fin ap))
    (hc : canonicalResearchCheck f = true) (hu : uses f a = true) :
    researchAdmitted a = true := by
  apply (researchAdmitted_exact a).mpr
  rcases (canonicalResearchCheck_exact f).mp hc a ((uses_exact f a).mp hu) with hp | hs
  · exact Or.inl (syntax_tag_lower a .pi2 hp)
  · exact Or.inr (syntax_tag_lower a .sigma2 hs)

theorem selectCanonicalPlan_success (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (hd : (Class.ofFormula f).DependsOn atoms)
    (hc : canonicalResearchCheck f = true) :
    ∃ p, selectCanonicalPlan atoms f = some p := by
  induction atoms generalizing f with
  | nil =>
    have he (σ : Assignment ap) : propEval σ f = propEval (fun _ => false) f :=
      hd σ (fun _ => false) (by simp)
    have constant : equivalent f .ff = true ∨ equivalent f .tt = true := by
      cases hv : propEval (fun _ => false) f
      · exact Or.inl ((equivalent_exact f .ff).mpr (Class.ext (fun σ => (he σ).trans hv)))
      · exact Or.inr ((equivalent_exact f .tt).mpr (Class.ext (fun σ => (he σ).trans hv)))
    rcases constant with h | h
    · exact ⟨.constant false, by simp [selectCanonicalPlan, h]⟩
    · by_cases hf : equivalent f .ff = true
      · exact ⟨.constant false, by simp [selectCanonicalPlan, hf]⟩
      · exact ⟨.constant true, by simp [selectCanonicalPlan, hf, h]⟩
  | cons a atoms ih =>
    by_cases hf : equivalent f .ff = true
    · exact ⟨.constant false, by simp [selectCanonicalPlan, hf]⟩
    by_cases ht : equivalent f .tt = true
    · exact ⟨.constant true, by simp [selectCanonicalPlan, hf, ht]⟩
    by_cases hw : researchAdmitted f = true
    · exact ⟨.whole f, by simp [selectCanonicalPlan, hf, ht, hw]⟩
    cases hu : uses f a
    · obtain ⟨p, hp⟩ := ih f (skip_dependsOn a atoms f hd hu) hc
      exact ⟨p, by simp [selectCanonicalPlan, hf, ht, hw, hu, hp]⟩
    · have ha := admitted_supported_atom f a hc hu
      have checks := (canonicalResearchCheck_shannon ((uses_exact f a).mp hu)
        (cofactor_eval a f false) (cofactor_eval a f true)).mp hc
      obtain ⟨high, hh⟩ := ih (cofactor a true f) (cofactor_dependsOn a atoms f true hd) checks.2.2
      obtain ⟨low, hl⟩ := ih (cofactor a false f) (cofactor_dependsOn a atoms f false hd) checks.2.1
      exact ⟨.shannon a high low, by simp [selectCanonicalPlan, hf, ht, hw, hu, ha, hh, hl]⟩

private theorem canonical_constant (f : Formula (Fin ap)) (b : Bool)
    (h : equivalent f (if b then .tt else .ff) = true) : canonicalResearchCheck f = true := by
  rw [canonicalResearchCheck_exact, (equivalent_exact _ _).mp h]
  cases b <;> exact (canonicalResearchCheck_exact _).mp rfl

theorem selectCanonicalPlan_admission (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (p : AcceptancePlan ap)
    (hp : selectCanonicalPlan atoms f = some p) : canonicalResearchCheck f = true := by
  induction atoms generalizing f p with
  | nil =>
    simp only [selectCanonicalPlan] at hp
    split at hp
    · exact canonical_constant f false (by assumption)
    · split at hp
      · exact canonical_constant f true (by assumption)
      · split at hp
        · exact researchAdmitted_check f (by assumption)
        · simp at hp
  | cons a atoms ih =>
    simp only [selectCanonicalPlan] at hp
    split at hp
    · exact canonical_constant f false (by assumption)
    · split at hp
      · exact canonical_constant f true (by assumption)
      · split at hp
        · exact researchAdmitted_check f (by assumption)
        · split at hp
          · rename_i hu
            split at hp
            · rename_i ha
              simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hp
              obtain ⟨high, hh, low, hl, _⟩ := hp
              have hm : a ∈ modalAtoms f := uses_in_bound
                (fun σ τ h => propEval_local f σ τ h) ((uses_exact f a).mp hu)
              have ht := (canonicalResearchCheck_exact a).mp (researchAdmitted_check a ha)
                a (modalAtom_uses f a hm)
              exact (canonicalResearchCheck_shannon ((uses_exact f a).mp hu)
                (cofactor_eval a f false) (cofactor_eval a f true)).mpr
                  ⟨ht, ih _ low hl, ih _ high hh⟩
            · simp at hp
          · exact ih f p hp

private def insertAtom (rank : Formula (Fin ap) → Nat) (a : Formula (Fin ap)) :
    List (Formula (Fin ap)) → List (Formula (Fin ap))
  | [] => [a]
  | b :: rest => if rank a ≤ rank b then a :: b :: rest else b :: insertAtom rank a rest

private theorem insertAtom_mem (rank : Formula (Fin ap) → Nat) (a b : Formula (Fin ap))
    (atoms : List (Formula (Fin ap))) :
    b ∈ insertAtom rank a atoms ↔ b = a ∨ b ∈ atoms := by
  induction atoms with
  | nil => simp [insertAtom]
  | cons c atoms ih =>
    simp only [insertAtom]
    split <;> simp [ih, or_left_comm]

/-- A structurally recursive stable insertion sort. Keeping the finite
reference structural also permits plain kernel reduction in diagnostics. -/
def orderAtoms (rank : Formula (Fin ap) → Nat) :
    List (Formula (Fin ap)) → List (Formula (Fin ap))
  | [] => []
  | a :: rest => insertAtom rank a (orderAtoms rank rest)

theorem orderAtoms_mem (rank : Formula (Fin ap) → Nat) (atoms : List (Formula (Fin ap)))
    (a : Formula (Fin ap)) : a ∈ orderAtoms rank atoms ↔ a ∈ atoms := by
  induction atoms with
  | nil => rfl
  | cons _ _ ih => simp only [orderAtoms, insertAtom_mem, ih, List.mem_cons]

private theorem insertAtom_sorted (rank : Formula (Fin ap) → Nat) (a : Formula (Fin ap))
    (atoms : List (Formula (Fin ap))) (hs : atoms.Pairwise (fun a b => rank a ≤ rank b)) :
    (insertAtom rank a atoms).Pairwise (fun a b => rank a ≤ rank b) := by
  induction atoms with
  | nil => simp [insertAtom]
  | cons b atoms ih =>
    obtain ⟨hb, ht⟩ := List.pairwise_cons.mp hs
    simp only [insertAtom]
    split
    · rename_i h
      apply List.pairwise_cons.mpr
      refine ⟨?_, hs⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h
      · exact Nat.le_trans h (hb c hc)
    · rename_i h
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih ht⟩
      intro c hc
      rcases (insertAtom_mem rank a c atoms).mp hc with rfl | hc
      · omega
      · exact hb c hc

theorem orderAtoms_sorted (rank : Formula (Fin ap) → Nat) (atoms : List (Formula (Fin ap))) :
    (orderAtoms rank atoms).Pairwise (fun a b => rank a ≤ rank b) := by
  induction atoms with
  | nil => simp [orderAtoms]
  | cons a _ ih => exact insertAtom_sorted rank a _ ih

/-- The alphabet has C's increasing variable-ID order. Allocation-order
refinement supplies `rank`; all correctness results are independent of it. -/
def canonicalPlan (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    Option (AcceptancePlan ap) :=
  selectCanonicalPlan (orderAtoms rank (modalAtoms f).eraseDups) f

theorem canonicalPlan_success (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (hc : canonicalResearchCheck f = true) : ∃ p, canonicalPlan rank f = some p := by
  apply selectCanonicalPlan_success _ f _ hc
  intro σ τ h
  apply propEval_local f σ τ
  intro a ha
  exact h a ((orderAtoms_mem rank _ a).mpr (by simpa using ha))

theorem canonicalPlan_spec (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (hf : NNF f) (p : AcceptancePlan ap) (hp : canonicalPlan rank f = some p) :
    p.Valid ∧ Class.ofFormula p.source = Class.ofFormula f :=
  selectCanonicalPlan_spec _ f hf p hp

theorem canonicalPlan_domain (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    (canonicalPlan rank f).isSome = true ↔ canonicalResearchCheck f = true := by
  rw [Option.isSome_iff_exists]
  exact ⟨fun ⟨p, hp⟩ => selectCanonicalPlan_admission _ f p hp,
    canonicalPlan_success rank f⟩

theorem transported_canonical_source (termRank atomRank : Formula (Fin ap) → Nat)
    (f t : Formula (Fin ap)) (ht : transport termRank f false 0 = some t)
    (p : AcceptancePlan ap) (hp : canonicalPlan atomRank t = some p) :
    p.Valid ∧ ∀ w j, Sat none w p.source j ↔ Sat none w f j := by
  obtain ⟨vp, ep⟩ := canonicalPlan_spec atomRank t (transport_nnf termRank f false 0 t ht) p hp
  refine ⟨vp, ?_⟩
  intro w j
  exact (class_language ep w j).trans
    (by simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
      transport_language termRank f false 0 t ht w j)

/-- Product semantics for the plan actually selected from the transported
input. This still compiles the explicit uncached plan with `assemble`; it
does not assert C's acceptance-cache/store-call trace is the same. -/
theorem transported_canonical_presentation (termRank atomRank : Formula (Fin ap) → Nat)
    (f t : Formula (Fin ap)) (ht : transport termRank f false 0 = some t)
    (p : AcceptancePlan ap) (hp : canonicalPlan atomRank t = some p)
    (buchi : Bool) (s : ComponentStore ap) (hs : StoreValid s) :
    let r := assemble buchi p s
    ProductPresentation f (storeClasses r.store) r.skeleton := by
  obtain ⟨vp, lp⟩ := transported_canonical_source termRank atomRank f t ht p hp
  exact assemble_presentation_of_language buchi p vp s hs f (fun w => lp w 0)

/-- No guessed plan or assumed validity: executable admission supplies a
successful result of the actual canonical selector, with its presentation. -/
theorem admitted_canonical_presentation (termRank atomRank : Formula (Fin ap) → Nat)
    (f t : Formula (Fin ap)) (ht : transport termRank f false 0 = some t)
    (hc : canonicalResearchCheck t = true) (buchi : Bool)
    (s : ComponentStore ap) (hs : StoreValid s) :
    ∃ p, canonicalPlan atomRank t = some p ∧ p.Valid ∧
      ProductPresentation f (storeClasses (assemble buchi p s).store)
        (assemble buchi p s).skeleton := by
  obtain ⟨p, hp⟩ := canonicalPlan_success atomRank t hc
  exact ⟨p, hp, (transported_canonical_source termRank atomRank f t ht p hp).1,
    transported_canonical_presentation termRank atomRank f t ht p hp buchi s hs⟩

end Tlsf.Dpa.Impl
