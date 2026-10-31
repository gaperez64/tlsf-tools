import TlsfProofs.Dpa.Impl.RefinedLanguage

/-!
# Protected extraction with a supplied tag classifier

The research extractor is recovered by supplying `classBits`. The contract
below also permits recursive canonical answers: every retained non-AP atom
must have a justified co-safety bit. DROP_X still uses the actual frozen
support and the existing protection loop, and retry tests the returned finite
bit and canonical equality. Instantiating this interface with the changing
C tag/cache trace is a further simulation obligation.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

abbrev TagClassifier (ap : Nat) := Formula (Fin ap) → FragmentBits

def TagClassifier.Sound (tags : TagClassifier ap) : Prop :=
  ∀ f t, tags f t = true → RefinedClass t f

theorem classBits_sound : TagClassifier.Sound (classBits : TagClassifier ap) :=
  refined_structural_lower

/-- REDUCE reads a co-safety answer for each frozen modal atom. -/
def reduceTagged (tags : TagClassifier ap) (f : Formula (Fin ap)) : Formula (Fin ap) :=
  replace (fun a => !isAPb a && !tags a .cosafety) f

def extractPassTagged (tags : TagClassifier ap) (f : Formula (Fin ap)) : Formula (Fin ap) :=
  unfoldSyntax (elide (reduceTagged tags f))

def rhoTagged (tags : TagClassifier ap) (f : Formula (Fin ap)) : Formula (Fin ap) :=
  let first := extractPassTagged tags f
  if tags first .finite && !equivalent f (unfoldSyntax f)
  then extractPassTagged tags (unfoldSyntax f) else first

/-- The syntactic support invariant makes a frozen variable essential in
its own atom class, even if other occurrences in the input are absorbed. -/
theorem usedAtom_self (ha : Uses (Class.ofFormula f) a) : Uses (Class.ofFormula a) a := by
  refine ⟨fun _ => false, true, ?_⟩
  change propEval (setAtom (fun _ => false) a true) a ≠ propEval (fun _ => false) a
  rw [propEval_used_atom ha, propEval_used_atom ha]
  simp [setAtom]

theorem reduceTagged_refined (tags : TagClassifier ap) (hs : tags.Sound) (f : Formula (Fin ap)) :
    RefinedClass .cosafety (reduceTagged tags f) := by
  rw [RefinedClass, reduceTagged, replace_exact]
  intro a ha
  obtain ⟨ha, hp⟩ := replaceTrue_uses ha
  by_cases hap : isAPb a = true
  · cases a <;> simp only [isAPb, Bool.false_eq_true] at hap
    exact .structural trivial
  · have ht : tags a .cosafety = true := by
      by_cases ht : tags a .cosafety = true
      · exact ht
      · exact False.elim (hp (by simp [hap, ht]))
    exact hs a .cosafety ht a (usedAtom_self ha)

theorem replace_nnf (p : Formula (Fin ap) → Bool) (hn : NNF f) : NNF (replace p f) := by
  induction f with
  | tt | ff => trivial
  | ap a => simp only [replace]; split <;> trivial
  | neg f ih =>
    cases f <;> simp_all [NNF, replace]
    split <;> trivial
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf hn.1, ihg hn.2⟩
  | impl f g | equiv f g | strongNext f => contradiction
  | next f | eventually f | globally f | «until» f g | release f g
  | weakUntil f g | strongRelease f g =>
    simp only [replace]; split
    · trivial
    · exact hn

theorem elideFuel_nnf (n : Nat) (hn : NNF f) : NNF (elideFuel n f) := by
  induction n generalizing f with
  | zero => exact hn
  | succ n ih =>
    simp only [elideFuel]
    split
    · exact hn
    · exact ih (replace_nnf _ hn)

theorem extractPassTagged_nnf (tags : TagClassifier ap) (hn : NNF f) :
    NNF (extractPassTagged tags f) :=
  unfold_nnf _ (elideFuel_nnf _ (replace_nnf _ hn))

theorem extractPassTagged_refined (tags : TagClassifier ap) (hs : tags.Sound) (f : Formula (Fin ap)) :
    RefinedClass .cosafety (extractPassTagged tags f) := by
  rw [RefinedClass, extractPassTagged, ← U_ofFormula, elide_exact]
  exact refined_U (by simp [LocalFragment])
    (elideFuel_tag _ (reduceTagged_refined tags hs f))

theorem extractPassTagged_weakens (tags : TagClassifier ap) (hn : NNF f) :
    U (Class.ofFormula f) ⇒ₚ Class.ofFormula (extractPassTagged tags f) := by
  rw [extractPassTagged, ← U_ofFormula, elide_exact, reduceTagged, replace_exact]
  apply U_monotone
  refine implies_trans (replaceTrue_weakens (nnf_positive _ hn) _ ?_)
    (elideFuel_weakens _ (replaceTrue_positive (nnf_positive _ hn) _))
  intro a ha hp
  have hb : isAPb a = true := (isAPb_exact a).mpr ha
  simp [hb] at hp

theorem extractPassTagged_unfolded (tags : TagClassifier ap) (f : Formula (Fin ap)) :
    U (Class.ofFormula (extractPassTagged tags f)) = Class.ofFormula (extractPassTagged tags f) := by
  rw [extractPassTagged, ← U_ofFormula, U_idempotent]

theorem rhoTagged_nnf (tags : TagClassifier ap) (hn : NNF f) : NNF (rhoTagged tags f) := by
  simp only [rhoTagged]
  split
  · exact extractPassTagged_nnf tags (unfold_nnf f hn)
  · exact extractPassTagged_nnf tags hn

theorem rhoTagged_refined (tags : TagClassifier ap) (hs : tags.Sound) (f : Formula (Fin ap)) :
    RefinedClass .cosafety (rhoTagged tags f) := by
  simp only [rhoTagged]
  split <;> exact extractPassTagged_refined tags hs _

theorem rhoTagged_weakens (tags : TagClassifier ap) (hn : NNF f) :
    U (Class.ofFormula f) ⇒ₚ Class.ofFormula (rhoTagged tags f) := by
  simp only [rhoTagged]
  split
  · have h := extractPassTagged_weakens tags (unfold_nnf f hn)
    rwa [← U_ofFormula, U_idempotent] at h
  · exact extractPassTagged_weakens tags hn

theorem rhoTagged_unfolded (tags : TagClassifier ap) (f : Formula (Fin ap)) :
    U (Class.ofFormula (rhoTagged tags f)) = Class.ofFormula (rhoTagged tags f) := by
  simp only [rhoTagged]
  split <;> exact extractPassTagged_unfolded tags _

/-- The result is an unfolded NNF co-safety obligation implied by the
all-field. This includes DROP_X protection and either finite-retry branch. -/
theorem rhoTagged_invariant (tags : TagClassifier ap) (hs : tags.Sound) (hn : NNF f) :
    NNF (rhoTagged tags f) ∧
    U (Class.ofFormula (rhoTagged tags f)) = Class.ofFormula (rhoTagged tags f) ∧
    RefinedClass .cosafety (rhoTagged tags f) ∧
    (U (Class.ofFormula f) ⇒ₚ Class.ofFormula (rhoTagged tags f)) :=
  ⟨rhoTagged_nnf tags hn, rhoTagged_unfolded tags f, rhoTagged_refined tags hs f,
    rhoTagged_weakens tags hn⟩

/-- The retained obligation on a satisfying suffix has a finite good
certificate in its actual derivative run. -/
theorem rhoTagged_satisfied_witness (tags : TagClassifier ap) (hs : tags.Sound) (hn : NNF f)
    (w : Word (Fin ap)) (j : Nat) (hw : Sat none w f j) :
    EventuallyTop w j (Class.ofFormula (rhoTagged tags f)) := by
  apply refined_cosafety_witness (rhoTagged_nnf tags hn) (rhoTagged_refined tags hs f)
  apply (ofFormula_holds _).mp
  apply implication_sound (rhoTagged_weakens tags hn)
  exact (U_holds _).mpr ((ofFormula_holds _).mpr hw)

theorem classTag_singleton (ha : modalAtoms a = [a]) (t : FragmentTag) :
    classTag t a = syntaxTag t a := by
  apply Bool.eq_iff_iff.mpr
  rw [classTag_exact, syntaxTag_exact]
  constructor
  · intro h
    apply h a
    refine ⟨fun _ => false, true, ?_⟩
    change propEval (setAtom (fun _ => false) a true) a ≠ propEval (fun _ => false) a
    rw [propEval_mem_atom a a (by simp [ha]), propEval_mem_atom a a (by simp [ha])]
    simp [setAtom]
  · intro h b hb
    have hm := uses_in_bound (fun σ τ hh => propEval_local _ σ τ hh) hb
    rw [ha] at hm
    exact List.mem_singleton.mp hm ▸ h

theorem frozen_reduce_guard (ha : modalAtoms a = [a]) :
    (if !isAPb a && !classBits a .cosafety then .tt else a) =
      (if !isAPb a && !cosafetyb a then .tt else a) := by
  apply congrArg (fun b : Bool => if b then .tt else a)
  simp only [classBits, classTag_singleton ha, syntaxTag]

theorem reduceTagged_research (f : Formula (Fin ap)) :
    reduceTagged classBits f = reduce f := by
  induction f with
  | tt | ff | ap _ => simp [reduceTagged, reduce, replace, isAPb]
  | neg f ih =>
    simp only [reduceTagged, reduce, replace] at *
    rw [ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [reduceTagged, reduce, replace] at *
    rw [ihf, ihg]
  | next f | strongNext f | eventually f | globally f | «until» f g
  | release f g | weakUntil f g | strongRelease f g =>
    exact frozen_reduce_guard (by rfl)

theorem extractPassTagged_research (f : Formula (Fin ap)) :
    extractPassTagged classBits f = extractPass f := by
  rw [extractPassTagged, reduceTagged_research]; rfl

theorem rhoTagged_research (f : Formula (Fin ap)) : rhoTagged classBits f = rho f := by
  simp only [rhoTagged, extractPassTagged_research, classBits, rho]

end Tlsf.Dpa.Impl
