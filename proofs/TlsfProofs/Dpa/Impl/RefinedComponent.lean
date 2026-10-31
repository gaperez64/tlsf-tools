import TlsfProofs.Dpa.Impl.RefinedExtractor

/-!
# Ordered component invariants for refined classifier answers

The transition table is `src/lib/dpa_dela.c:5`. A classifier is supplied to
each call, so the invariant does not assume the same answers across steps.
The per-call classifier/cache simulation and the accepting-run converse are
separate obligations; these results do not assert full language recognition.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

/-- All-field exactness and an unfolded, co-safety rejecting obligation.
The sentinel need not entail anything; every active obligation is implied. -/
def TaggedInvariant (s : State ap) : Prop :=
  NNF s.all ∧ U (Class.ofFormula s.all) = Class.ofFormula s.all ∧
  NNF s.rejecting ∧ U (Class.ofFormula s.rejecting) = Class.ofFormula s.rejecting ∧
  RefinedClass .cosafety s.rejecting ∧
  (Class.ofFormula s.rejecting ≠ Class.bot → Class.ofFormula s.all ⇒ₚ Class.ofFormula s.rejecting)

theorem tagged_suspended (hn : NNF a) (hu : U (Class.ofFormula a) = Class.ofFormula a) :
    TaggedInvariant (⟨a, .ff⟩ : State ap) :=
  ⟨hn, hu, trivial, rfl, refined_structural_lower .ff .cosafety rfl,
    fun h => False.elim (h rfl)⟩

theorem tagged_obligation (hn : NNF a) (hu : U (Class.ofFormula a) = Class.ofFormula a)
    (hr : NNF r) (hru : U (Class.ofFormula r) = Class.ofFormula r)
    (hco : RefinedClass .cosafety r) (hi : Class.ofFormula a ⇒ₚ Class.ofFormula r) :
    TaggedInvariant (⟨a, r⟩ : State ap) :=
  ⟨hn, hu, hr, hru, hco, fun _ => hi⟩

def initialTagged (tags : TagClassifier ap) (f : Formula (Fin ap)) : State ap :=
  let all := unfoldSyntax f
  if tags all .safety || tags all .cosafety then ⟨all, .ff⟩ else ⟨all, rhoTagged tags f⟩

/-- The row function receives the raw all-field and the already unfolded
raw rejecting field, in the same order as C's transition table. -/
def rowTagged (tags : TagClassifier ap) (a r : Formula (Fin ap)) : Edge ap :=
  let next := unfoldSyntax a
  if equivalent next .ff then ⟨⟨.ff, .ff⟩, false⟩
  else if equivalent next .tt then ⟨⟨.tt, .ff⟩, true⟩
  else if tags next .safety then ⟨⟨next, .ff⟩, true⟩
  else if tags next .cosafety then ⟨⟨next, .ff⟩, false⟩
  else if equivalent r .ff then ⟨⟨next, rhoTagged tags a⟩, false⟩
  else if tags r .finite then
    let q := Formula.conj r (rhoTagged tags a)
    if equivalent q .ff then ⟨⟨.ff, .ff⟩, false⟩ else ⟨⟨next, q⟩, true⟩
  else ⟨⟨next, r⟩, false⟩

def transitionTagged (tags : TagClassifier ap) (v : Letter (Fin ap)) (s : State ap) : Edge ap :=
  rowTagged tags (stepSyntax v s.all) (unfoldSyntax (stepSyntax v s.rejecting))

theorem initialTagged_spec (tags : TagClassifier ap) (hs : tags.Sound) (hn : NNF f) :
    TaggedInvariant (initialTagged tags f) ∧
      Class.ofFormula (initialTagged tags f).all = U (Class.ofFormula f) := by
  have hu : U (Class.ofFormula (unfoldSyntax f)) = Class.ofFormula (unfoldSyntax f) := by
    rw [← U_ofFormula, U_idempotent]
  simp only [initialTagged]
  split
  · exact ⟨tagged_suspended (unfold_nnf _ hn) hu, (U_ofFormula f).symm⟩
  · exact ⟨tagged_obligation (unfold_nnf _ hn) hu (rhoTagged_nnf tags hn)
      (rhoTagged_unfolded tags f) (rhoTagged_refined tags hs f)
      (by simpa only [U_ofFormula] using rhoTagged_weakens tags hn), (U_ofFormula f).symm⟩

theorem rowTagged_spec (tags : TagClassifier ap) (hs : tags.Sound) (hn : NNF a)
    (hr : NNF r) (hru : U (Class.ofFormula r) = Class.ofFormula r)
    (hco : RefinedClass .cosafety r)
    (hi : U (Class.ofFormula a) ≠ Class.bot → Class.ofFormula r ≠ Class.bot →
      U (Class.ofFormula a) ⇒ₚ Class.ofFormula r) :
    TaggedInvariant (rowTagged tags a r).target ∧
      Class.ofFormula (rowTagged tags a r).target.all = U (Class.ofFormula a) := by
  have hu : U (Class.ofFormula (unfoldSyntax a)) = Class.ofFormula (unfoldSyntax a) := by
    rw [← U_ofFormula, U_idempotent]
  have hseed := rhoTagged_invariant tags hs hn
  have hconj : Class.ofFormula (.conj r (rhoTagged tags a)) =
      meet (Class.ofFormula r) (Class.ofFormula (rhoTagged tags a)) := by
    apply Class.ext; intro σ; rfl
  simp only [rowTagged]
  split
  · rename_i hb
    exact ⟨tagged_suspended trivial rfl,
      ((equivalent_exact _ _).mp hb).symm.trans (U_ofFormula a).symm⟩
  · rename_i hb
    have hbot : U (Class.ofFormula a) ≠ Class.bot := by
      intro he; apply hb; exact (equivalent_exact _ _).mpr ((U_ofFormula a).symm.trans he)
    split
    · rename_i ht
      exact ⟨tagged_suspended trivial U_top,
        ((equivalent_exact _ _).mp ht).symm.trans (U_ofFormula a).symm⟩
    · split
      · exact ⟨tagged_suspended (unfold_nnf _ hn) hu, (U_ofFormula a).symm⟩
      · split
        · exact ⟨tagged_suspended (unfold_nnf _ hn) hu, (U_ofFormula a).symm⟩
        · split
          · exact ⟨tagged_obligation (unfold_nnf _ hn) hu hseed.1 hseed.2.1 hseed.2.2.1
              (by simpa only [U_ofFormula] using hseed.2.2.2), (U_ofFormula a).symm⟩
          · rename_i hrbot
            have hrne : Class.ofFormula r ≠ Class.bot := fun he => hrbot ((equivalent_exact _ _).mpr he)
            have hraw := hi hbot hrne
            split
            · have himp := meet_implied hraw hseed.2.2.2
              have hne : equivalent (.conj r (rhoTagged tags a)) .ff = false := by
                apply Bool.eq_false_iff.mpr
                intro he
                have heq := (equivalent_exact _ _).mp he
                rw [hconj] at heq
                rw [heq] at himp
                exact hbot (implies_bot himp)
              simp only [hne, Bool.false_eq_true, ↓reduceIte]
              refine ⟨tagged_obligation (unfold_nnf _ hn) hu ⟨hr, hseed.1⟩ ?_ ?_ ?_,
                (U_ofFormula a).symm⟩
              · rw [hconj, U_meet, hru, hseed.2.1]
              · exact meet_tag hco hseed.2.2.1
              · simpa only [hconj, U_ofFormula] using himp
            · exact ⟨tagged_obligation (unfold_nnf _ hn) hu hr hru hco
                (by simpa only [U_ofFormula] using hraw), (U_ofFormula a).symm⟩

theorem transitionTagged_spec (tags : TagClassifier ap) (hs : tags.Sound)
    (v : Letter (Fin ap)) (h : TaggedInvariant s) :
    TaggedInvariant (transitionTagged tags v s).target ∧
      Class.ofFormula (transitionTagged tags v s).target.all = U (D v (Class.ofFormula s.all)) := by
  have hn := step_nnf _ h.1 v
  have hr := unfold_nnf _ (step_nnf _ h.2.2.1 v)
  have hu : U (Class.ofFormula (unfoldSyntax (stepSyntax v s.rejecting))) =
      Class.ofFormula (unfoldSyntax (stepSyntax v s.rejecting)) := by
    rw [← U_ofFormula, U_idempotent]
  have hco : RefinedClass .cosafety (unfoldSyntax (stepSyntax v s.rejecting)) := by
    rw [RefinedClass, ← U_ofFormula, ← D_ofFormula]
    exact refined_U (by simp [LocalFragment])
      (refined_D (by simp [LocalFragment]) v h.2.2.2.2.1)
  have hi : U (Class.ofFormula (stepSyntax v s.all)) ≠ Class.bot →
      Class.ofFormula (unfoldSyntax (stepSyntax v s.rejecting)) ≠ Class.bot →
      U (Class.ofFormula (stepSyntax v s.all)) ⇒ₚ
        Class.ofFormula (unfoldSyntax (stepSyntax v s.rejecting)) := by
    intro _ hrne
    have hprev : Class.ofFormula s.rejecting ≠ Class.bot := by
      intro he
      apply hrne
      rw [← U_ofFormula, ← D_ofFormula, he]
      rfl
    simpa only [U_ofFormula, D_ofFormula] using U_monotone (D_monotone v (h.2.2.2.2.2 hprev))
  simpa only [transitionTagged, D_ofFormula] using rowTagged_spec tags hs hn hr hu hco hi

/-- Classifiers may change at every letter; positive-answer soundness is
the only assumption of the local invariant and all-field simulation. -/
def runTagged (tags : Nat → TagClassifier ap) (f : Formula (Fin ap)) (w : Word (Fin ap)) : Nat → State ap
  | 0 => initialTagged (tags 0) f
  | n+1 => (transitionTagged (tags (n+1)) (w n) (runTagged tags f w n)).target

theorem runTagged_spec (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap)) (n : Nat) :
    TaggedInvariant (runTagged tags f w n) ∧
      Class.ofFormula (runTagged tags f w n).all = derivatives w 0 n (Class.ofFormula f) := by
  induction n with
  | zero => exact initialTagged_spec (tags 0) (hs 0) hn
  | succ n ih =>
    have ht := transitionTagged_spec (tags (n+1)) (hs (n+1)) (w n) ih.1
    refine ⟨ht.1, ?_⟩
    change Class.ofFormula (transitionTagged (tags (n+1)) (w n) (runTagged tags f w n)).target.all = _
    rw [ht.2, ih.2, derivatives_snoc, Nat.zero_add]

theorem runTagged_all_language (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (runTagged tags f w n).all n ↔ Sat none w f 0 := by
  rw [← ofFormula_holds, (runTagged_spec tags hs hn w n).2]
  simpa only [Nat.zero_add] using (derivatives_holds w 0 n _).trans (ofFormula_holds f)

theorem runTagged_after (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap)) (n k : Nat) :
    Class.ofFormula (runTagged tags f w (n+k)).all =
      derivatives w n k (Class.ofFormula (runTagged tags f w n).all) := by
  rw [(runTagged_spec tags hs hn w (n+k)).2, (runTagged_spec tags hs hn w n).2,
    derivatives_add, Nat.zero_add]

/-- An active rejecting field on a satisfying word is a genuine co-safety
obligation, so it has a finite good certificate. -/
theorem runTagged_satisfied_obligation (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap)) (n : Nat) (hw : Sat none w f 0)
    (ha : Class.ofFormula (runTagged tags f w n).rejecting ≠ Class.bot) :
    EventuallyTop w n (Class.ofFormula (runTagged tags f w n).rejecting) := by
  have h := (runTagged_spec tags hs hn w n).1
  apply refined_cosafety_witness h.2.2.1 h.2.2.2.2.1
  apply (ofFormula_holds _).mp
  apply implication_sound (h.2.2.2.2.2 ha)
  exact (ofFormula_holds _).mpr ((runTagged_all_language tags hs hn w n).mpr hw)

/-- A retained finite obligation cannot be false on a run whose all-field
never becomes false. The finite test is the recursive canonical predicate. -/
theorem runTagged_finite_obligation (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap))
    (hnever : ∀ n, Class.ofFormula (runTagged tags f w n).all ≠ Class.bot)
    (n : Nat) (hf : RefinedClass .finite E)
    (hi : Class.ofFormula (runTagged tags f w n).all ⇒ₚ Class.ofFormula E) :
    Sat none w E n := by
  apply Classical.byContradiction
  intro hfalse
  have hd := refined_finite_class_constant hf w n (horizon E+1) (by omega)
  rw [ite_eq_right hfalse] at hd
  have himp := derivatives_monotone w n (horizon E+1) hi
  rw [hd, ← runTagged_after tags hs hn w n (horizon E+1)] at himp
  exact hnever _ (implies_bot himp)

theorem initialTagged_research (f : Formula (Fin ap)) : initialTagged classBits f = initial f := by
  simp only [initialTagged, classBits, rhoTagged_research, initial]

theorem transitionTagged_research (v : Letter (Fin ap)) (s : State ap) :
    transitionTagged classBits v s = transition v s := by
  simp only [transitionTagged, rowTagged, classBits, rhoTagged_research, transition]

theorem runTagged_research (f : Formula (Fin ap)) (w : Word (Fin ap)) (n : Nat) :
    runTagged (fun _ => classBits) f w n = run f w n := by
  induction n with
  | zero => exact initialTagged_research f
  | succ n ih => simp only [runTagged, run, transitionTagged_research, ih]

end Tlsf.Dpa.Impl
