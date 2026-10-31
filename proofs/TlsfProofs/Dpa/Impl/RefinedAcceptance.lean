import TlsfProofs.Dpa.Impl.TagTrace

/-!
# Acceptance progress for refined components

The table is `src/lib/dpa_dela.c:5`. Classifiers can change between letters;
sound positive answers and structural lower bounds suffice for the forward
language direction. The protected-constraint results concern the structural
Π₂ input domain and the actual tagged extractor, including its DROP_X loop.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

def TagClassifier.Lower (tags : TagClassifier ap) : Prop :=
  ∀ f, BitsBelow (classBits f) (tags f)

theorem cacheClassifier_has_lower (s : TagCache ap) (hs : s.Valid) :
    (cacheClassifier s).Lower := cacheClassifier_lower s hs

theorem classBits_has_lower : TagClassifier.Lower (classBits : TagClassifier ap) := fun _ _ h => h

theorem D_class_top (v : Letter (Fin ap)) : D v Class.top = Class.top := by
  apply Class.ext; intro σ; rfl

theorem D_class_bot (v : Letter (Fin ap)) : D v Class.bot = Class.bot := by
  apply Class.ext; intro σ; rfl

def marksTagged (tags : Nat → TagClassifier ap) (f : Formula (Fin ap))
    (w : Word (Fin ap)) (n : Nat) : Bool :=
  (transitionTagged (tags (n+1)) (w n) (runTagged tags f w n)).mark

theorem tagged_top_mark (tags : TagClassifier ap) (v : Letter (Fin ap)) (s : State ap)
    (ht : Class.ofFormula s.all = Class.top) : (transitionTagged tags v s).mark = true := by
  have he : Class.ofFormula (unfoldSyntax (stepSyntax v s.all)) = Class.top := by
    rw [← U_ofFormula, ← D_ofFormula, ht, D_class_top, U_top]
  have hff : equivalent (unfoldSyntax (stepSyntax v s.all)) .ff = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    have hh := (equivalent_exact _ _).mp hb
    rw [he] at hh
    exact Bool.noConfusion (congrArg (fun x : Class ap => x (fun _ => false)) hh)
  have htt := (equivalent_exact (unfoldSyntax (stepSyntax v s.all)) .tt).mpr he
  simp only [transitionTagged, rowTagged, hff, htt, Bool.false_eq_true, ↓reduceIte]

/-- Once the co-safety suspension row is excluded, an unmarked step has
an active obligation. Existing active obligations progress exactly, and
the actual finite query must have returned false. -/
theorem rowTagged_unmarked (tags : TagClassifier ap) (hn : NNF a)
    (hb : U (Class.ofFormula a) ≠ Class.bot)
    (hi : Class.ofFormula r ≠ Class.bot → U (Class.ofFormula a) ⇒ₚ Class.ofFormula r)
    (hc : tags (unfoldSyntax a) .cosafety = false)
    (hm : (rowTagged tags a r).mark = false) :
    Class.ofFormula (rowTagged tags a r).target.rejecting ≠ Class.bot ∧
      (Class.ofFormula r ≠ Class.bot →
        (rowTagged tags a r).target.rejecting = r ∧ tags r .finite = false) := by
  have hseed := rhoTagged_weakens tags hn
  have hseedne : Class.ofFormula (rhoTagged tags a) ≠ Class.bot := by
    intro he; rw [he] at hseed; exact hb (implies_bot hseed)
  have hff : equivalent (unfoldSyntax a) .ff = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    exact hb ((U_ofFormula a).trans ((equivalent_exact _ _).mp he))
  by_cases ht : equivalent (unfoldSyntax a) .tt = true
  · simp only [rowTagged, hff, ht, Bool.false_eq_true, ↓reduceIte] at hm
    contradiction
  by_cases hsa : tags (unfoldSyntax a) .safety = true
  · simp only [rowTagged, hff, ht, hsa, Bool.false_eq_true, ↓reduceIte] at hm
    contradiction
  simp only [rowTagged, hff, ht, hsa, hc, Bool.false_eq_true, ↓reduceIte] at hm ⊢
  by_cases hr : equivalent r .ff = true
  · simp only [hr, ↓reduceIte]
    exact ⟨hseedne, fun h => False.elim (h ((equivalent_exact _ _).mp hr))⟩
  simp only [hr] at hm ⊢
  have hrne : Class.ofFormula r ≠ Class.bot := fun he => hr ((equivalent_exact _ _).mpr he)
  have hconj : equivalent (.conj r (rhoTagged tags a)) .ff = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hh := meet_implied (hi hrne) hseed
    have hc : Class.ofFormula (.conj r (rhoTagged tags a)) =
        meet (Class.ofFormula r) (Class.ofFormula (rhoTagged tags a)) := by
      apply Class.ext; intro σ; rfl
    rw [← hc, (equivalent_exact _ _).mp he] at hh
    exact hb (implies_bot hh)
  by_cases hf : tags r .finite = true
  · simp only [hf, hconj, Bool.false_eq_true, ↓reduceIte] at hm
    contradiction
  · simp only [hf]
    exact ⟨hrne, fun _ => ⟨rfl, trivial⟩⟩

/-- Every satisfying word produces infinitely many marks, for changing
refined classifiers. This direction needs no Π₂ admission hypothesis. -/
theorem runTagged_satisfying_accepts (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (w : Word (Fin ap)) (hw : Sat none w f 0) :
    Inf (marksTagged tags f w) := by
  apply Classical.byContradiction
  intro hfalse
  obtain ⟨N, hN⟩ := (not_inf_iff_fin _).mp hfalse
  have hnever (n : Nat) : Class.ofFormula (runTagged tags f w n).all ≠ Class.bot :=
    holds_not_bot ((ofFormula_holds _).mpr ((runTagged_all_language tags hs hn w n).mpr hw))
  have hco (n : Nat) (hge : N ≤ n) :
      tags (n+1) (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).all)) .cosafety = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hstep := transitionTagged_spec (tags (n+1)) (hs (n+1)) (w n)
      (runTagged_spec tags hs hn w n).1
    have htag : RefinedClass .cosafety (runTagged tags f w (n+1)).all := by
      have hp := hs (n+1) _ _ ht
      change HasTag (RefinedAtom .cosafety) _ at hp ⊢
      have he : Class.ofFormula (runTagged tags f w (n+1)).all =
          Class.ofFormula (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).all)) :=
        hstep.2.trans (by rw [D_ofFormula, U_ofFormula])
      rwa [he]
    obtain ⟨k, hk⟩ := refined_cosafety_witness (runTagged_spec tags hs hn w (n+1)).1.1
      htag w (n+1) ((runTagged_all_language tags hs hn w (n+1)).mpr hw)
    have htop : Class.ofFormula (runTagged tags f w (n+1+k)).all = Class.top := by
      rw [runTagged_after tags hs hn w (n+1) k, hk]
    have hm := tagged_top_mark (tags (n+1+k+1)) (w (n+1+k))
      (runTagged tags f w (n+1+k)) htop
    exact Bool.noConfusion ((hN (n+1+k) (by omega)).symm.trans hm)
  have hrow (n : Nat) (hge : N ≤ n) :=
    rowTagged_unmarked (tags (n+1)) (step_nnf _ (runTagged_spec tags hs hn w n).1.1 (w n))
      (by
        have he := (transitionTagged_spec (tags (n+1)) (hs (n+1)) (w n)
          (runTagged_spec tags hs hn w n).1).2
        exact fun hb => hnever (n+1) (he.trans (by simpa only [D_ofFormula] using hb)))
      (by
        intro hr
        have hi := (runTagged_spec tags hs hn w n).1.2.2.2.2.2
        have hprev : Class.ofFormula (runTagged tags f w n).rejecting ≠ Class.bot := by
          intro hb
          apply hr
          rw [← U_ofFormula, ← D_ofFormula, hb, D_class_bot]
          rfl
        simpa only [U_ofFormula, D_ofFormula] using U_monotone (D_monotone (w n) (hi hprev)))
      (hco n hge) (hN n hge)
  have hactive : ∀ n, N+1 ≤ n → Class.ofFormula (runTagged tags f w n).rejecting ≠ Class.bot := by
    intro n hge
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact (hrow j (by omega)).1
  have hprogress (n : Nat) (hge : N+1 ≤ n) :
      (runTagged tags f w (n+1)).rejecting =
        unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).rejecting) ∧
      tags (n+1) (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).rejecting)) .finite = false := by
    apply (hrow n (by omega)).2
    intro he
    have hbot : U (D (w n) (Class.ofFormula (runTagged tags f w n).all)) = Class.bot := by
      apply implies_bot
      have hi := U_monotone (D_monotone (w n)
        ((runTagged_spec tags hs hn w n).1.2.2.2.2.2 (hactive n hge)))
      simpa only [U_ofFormula, D_ofFormula, he] using hi
    have hstep := (transitionTagged_spec (tags (n+1)) (hs (n+1)) (w n)
      (runTagged_spec tags hs hn w n).1).2
    exact hnever (n+1) (hstep.trans hbot)
  let m := N+1
  obtain ⟨k, hk⟩ := runTagged_satisfied_obligation tags hs hn w m hw (hactive m (by omega))
  have hderiv (j : Nat) : Class.ofFormula (runTagged tags f w (m+j)).rejecting =
      derivatives w m j (Class.ofFormula (runTagged tags f w m).rejecting) := by
    induction j with
    | zero => simpa only [Nat.add_zero, derivatives] using
        (runTagged_spec tags hs hn w m).1.2.2.2.1.symm
    | succ j ih =>
      have he : m+(j+1) = (m+j)+1 := by omega
      rw [he, (hprogress (m+j) (by omega)).1, ← U_ofFormula, ← D_ofFormula, ih, derivatives_snoc]
  have htop : Class.ofFormula (unfoldSyntax
      (stepSyntax (w (m+k)) (runTagged tags f w (m+k)).rejecting)) = Class.top := by
    rw [← U_ofFormula, ← D_ofFormula, hderiv k, hk, D_class_top, U_top]
  have hfinite : classBits (unfoldSyntax
      (stepSyntax (w (m+k)) (runTagged tags f w (m+k)).rejecting)) .finite = true := by
    apply (classTag_exact _ _).mpr
    rw [htop]
    exact top_hasTag _
  have ht := hl (m+k+1) _ .finite hfinite
  exact Bool.noConfusion ((hprogress (m+k) (by omega)).2.symm.trans ht)

theorem defaultTrace_satisfying_accepts (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) (hv : s.Valid) (hn : NNF f) (w : Word (Fin ap))
    (hw : Sat none w f 0) :
    Inf (marksTagged (defaultTraceClassifier rank highFirst fuel before programs s) f w) :=
  runTagged_satisfying_accepts _
    (fun n => (defaultTraceClassifier_spec rank highFirst fuel before programs s hv n).1)
    (fun n => (defaultTraceClassifier_spec rank highFirst fuel before programs s hv n).2)
    hn w hw

theorem tagged_bot_mark (tags : TagClassifier ap) (v : Letter (Fin ap)) (s : State ap)
    (hb : Class.ofFormula s.all = Class.bot) : (transitionTagged tags v s).mark = false := by
  have he : Class.ofFormula (unfoldSyntax (stepSyntax v s.all)) = Class.bot := by
    rw [← U_ofFormula, ← D_ofFormula, hb, D_class_bot]
    rfl
  have hff := (equivalent_exact (unfoldSyntax (stepSyntax v s.all)) .ff).mpr he
  simp only [transitionTagged, rowTagged, hff, ↓reduceIte]

theorem runTagged_accepting_never_bot (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hn : NNF f) (w : Word (Fin ap))
    (hi : Inf (marksTagged tags f w)) (n : Nat) :
    Class.ofFormula (runTagged tags f w n).all ≠ Class.bot := by
  intro hb
  obtain ⟨k, hk, hm⟩ := hi n
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have he : Class.ofFormula (runTagged tags f w (n+j)).all = Class.bot := by
    rw [runTagged_after tags hs hn w n j, hb, derivatives_bot]
  exact Bool.noConfusion ((tagged_bot_mark (tags (n+j+1)) (w (n+j))
    (runTagged tags f w (n+j)) he).symm.trans hm)

theorem runTagged_accepting_safety (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hn : NNF f) (w : Word (Fin ap))
    (hi : Inf (marksTagged tags f w)) (n : Nat)
    (hsa : RefinedClass .safety (runTagged tags f w n).all) : Sat none w f 0 := by
  apply Classical.byContradiction
  intro hf
  have hfalse : ¬Sat none w (runTagged tags f w n).all n :=
    fun h => hf ((runTagged_all_language tags hs hn w n).mp h)
  obtain ⟨k, hk⟩ := refined_safety_bad_prefix (runTagged_spec tags hs hn w n).1.1 hsa w n hfalse
  have he : Class.ofFormula (runTagged tags f w (n+k)).all = Class.bot := by
    rw [runTagged_after tags hs hn w n k, hk]
  exact runTagged_accepting_never_bot tags hs hn w hi (n+k) he

theorem runTagged_safety_language (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hsa : RefinedClass .safety f) (w : Word (Fin ap)) :
    Inf (marksTagged tags f w) ↔ Sat none w f 0 := by
  refine ⟨?_, runTagged_satisfying_accepts tags hs hl hn w⟩
  intro hi
  apply runTagged_accepting_safety tags hs hn w hi 0
  change HasTag (RefinedAtom .safety) _
  rw [(runTagged_spec tags hs hn w 0).2]
  exact refined_U (by simp [LocalFragment]) hsa

theorem runTagged_finite_language (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hfin : RefinedClass .finite f) (w : Word (Fin ap)) :
    Inf (marksTagged tags f w) ↔ Sat none w f 0 := by
  refine ⟨?_, runTagged_satisfying_accepts tags hs hl hn w⟩
  intro hi
  apply Classical.byContradiction
  intro hf
  have he := refined_finite_class_constant hfin w 0 (horizon f+1) (by omega)
  rw [ite_eq_right hf, ← (runTagged_spec tags hs hn w (horizon f+1)).2] at he
  exact runTagged_accepting_never_bot tags hs hn w hi (horizon f+1) he

theorem rowTagged_marked_cosafety (tags : TagClassifier ap)
    (hc : tags (unfoldSyntax a) .cosafety = true)
    (hm : (rowTagged tags a r).mark = true) :
    Class.ofFormula (unfoldSyntax a) = Class.top ∨ tags (unfoldSyntax a) .safety = true := by
  by_cases hf : equivalent (unfoldSyntax a) .ff = true
  · simp only [rowTagged, hf, ↓reduceIte] at hm
    contradiction
  by_cases ht : equivalent (unfoldSyntax a) .tt = true
  · exact Or.inl ((equivalent_exact _ _).mp ht)
  by_cases hsa : tags (unfoldSyntax a) .safety = true
  · exact Or.inr hsa
  simp only [rowTagged, hf, ht, hsa, hc, ↓reduceIte] at hm
  contradiction

/-- Structural co-safety is preserved in the all-field, so its structural
lower bit excludes active renewal rows. Recursively refined safety answers
are permitted on the eventual marked step. -/
theorem runTagged_cosafety_language (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hco : classBits f .cosafety = true) (w : Word (Fin ap)) :
    Inf (marksTagged tags f w) ↔ Sat none w f 0 := by
  refine ⟨?_, runTagged_satisfying_accepts tags hs hl hn w⟩
  intro hi
  obtain ⟨n, _, hm⟩ := hi 0
  have hnext : classBits (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).all)) .cosafety = true := by
    apply (classTag_exact _ _).mpr
    rw [← U_ofFormula, ← D_ofFormula, (runTagged_spec tags hs hn w n).2]
    exact U_cosafety (D_cosafety _ (derivatives_cosafety w 0 n ((classTag_exact _ _).mp hco)))
  have hcases := rowTagged_marked_cosafety (tags (n+1)) (hl (n+1) _ .cosafety hnext) hm
  have he := (transitionTagged_spec (tags (n+1)) (hs (n+1)) (w n)
    (runTagged_spec tags hs hn w n).1).2
  have he' : Class.ofFormula (runTagged tags f w (n+1)).all =
      Class.ofFormula (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).all)) := by
    simpa only [D_ofFormula, U_ofFormula, runTagged] using he
  rcases hcases with ht | hsa
  · apply (runTagged_all_language tags hs hn w (n+1)).mp
    apply (ofFormula_holds _).mp
    rw [he', ht]
    rfl
  · apply runTagged_accepting_safety tags hs hn w hi (n+1)
    change HasTag (RefinedAtom .safety) _
    rw [he']
    exact hs (n+1) _ .safety hsa

theorem defaultTrace_finite_language (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) (hv : s.Valid) (hn : NNF f) (hfin : RefinedClass .finite f)
    (w : Word (Fin ap)) :
    Inf (marksTagged (defaultTraceClassifier rank highFirst fuel before programs s) f w) ↔
      Sat none w f 0 :=
  runTagged_finite_language _
    (fun n => (defaultTraceClassifier_spec rank highFirst fuel before programs s hv n).1)
    (fun n => (defaultTraceClassifier_spec rank highFirst fuel before programs s hv n).2)
    hn hfin w

/-- Every structural co-safety protected constraint survives the actual
tagged REDUCE and every protected DROP_X pass. Extra recursively refined
co-safety atoms may be retained; they need not equal structural atoms. -/
theorem extractPassTagged_protected_constraint (tags : TagClassifier ap) (hl : tags.Lower)
    (hn : NNF f) (hC : ProtectedConstraint (Class.ofFormula f) C) :
    Class.ofFormula (extractPassTagged tags f) ⇒ₚ U C := by
  let p := fun a : Formula (Fin ap) => (!isAPb a && !tags a .cosafety) = true
  have hr : replaceTrue p (Class.ofFormula f) ⇒ₚ C := by
    apply elision_preserves_constraint hC.2.1
    intro a ha hp
    have hbits : classBits a .cosafety = true :=
      (classTag_exact _ _).mpr (syntax_tag_lower a .cosafety (hC.1 a ha))
    have ht := hl a .cosafety hbits
    simp only [p, ht, Bool.not_true, Bool.and_false, Bool.false_eq_true] at hp
  have hw : Class.ofFormula f ⇒ₚ replaceTrue p (Class.ofFormula f) := by
    apply replaceTrue_weakens (nnf_positive f hn) p
    intro a ha hp
    have he : isAPb a = true := (isAPb_exact a).mpr ha
    simp only [p, he, Bool.not_true, Bool.false_and, Bool.false_eq_true] at hp
  have loop : ∀ n y, NNFClass y → (Class.ofFormula f ⇒ₚ y) →
      (y ⇒ₚ C) → Dpa.elideFuel n y ⇒ₚ C := by
    intro n
    induction n with
    | zero => intro y _ _ hy; exact hy
    | succ n ih =>
      intro y hyn hxy hy
      have hd : Dpa.dropX y ⇒ₚ C := by
        apply elision_preserves_constraint hy
        intro a ha hp
        exact hp.2 (hC.2.2 y hyn hxy hy a ha hp.1)
      have hw : y ⇒ₚ Dpa.dropX y := replaceTrue_weakens (nnfClass_positive hyn) _ (by
        intro a ha hp; cases a <;> simp_all [isAP, isX])
      simp only [Dpa.elideFuel]
      split
      · exact hy
      · exact ih _ (replaceTrue_nnfClass _ hyn) (implies_trans hxy hw) hd
  rw [extractPassTagged, ← U_ofFormula, elide_exact, reduceTagged, replace_exact]
  exact U_monotone (loop _ _ (replaceTrue_nnfClass p ⟨f, hn, rfl⟩) hw hr)

/-- The raw all-field used by the tagged extractor, before unfolding. -/
def rawTagged (tags : Nat → TagClassifier ap) (f : Formula (Fin ap))
    (w : Word (Fin ap)) : Nat → Formula (Fin ap)
  | 0 => f
  | n+1 => stepSyntax (w n) (runTagged tags f w n).all

theorem rawTagged_nnf (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap)) (n : Nat) : NNF (rawTagged tags f w n) := by
  cases n with
  | zero => exact hn
  | succ n => exact step_nnf _ (runTagged_spec tags hs hn w n).1.1 (w n)

theorem rawTagged_class (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap)) (n : Nat) :
    Class.ofFormula (rawTagged tags f w n) = rawAll (Class.ofFormula f) w n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [rawTagged, rawAll, ← D_ofFormula, (runTagged_spec tags hs hn w n).2,
      all_field_derivative _ ⟨f, hn, rfl⟩ w n]

theorem rawTagged_unfold (tags : Nat → TagClassifier ap) (hs : ∀ n, (tags n).Sound)
    (hn : NNF f) (w : Word (Fin ap)) (n : Nat) :
    U (Class.ofFormula (rawTagged tags f w n)) = Class.ofFormula (runTagged tags f w n).all := by
  cases n with
  | zero => exact (initialTagged_spec (tags 0) (hs 0) hn).2.symm
  | succ n => simpa only [rawTagged, D_ofFormula, runTagged] using
      (transitionTagged_spec (tags (n+1)) (hs (n+1)) (w n)
        (runTagged_spec tags hs hn w n).1).2.symm

/-- GeneralConverse's closed-alphabet descent now applies to the actual
tagged first passes, uniformly over changing lower-bound classifiers.
The input domain here is structural Π₂, not the larger refined Π₂ predicate. -/
theorem runTagged_eventually_false_passes (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hpi : classBits f .pi2 = true) (w : Word (Fin ap))
    (hf : ¬Sat none w f 0) :
    ∃ N, ∀ n, N ≤ n → ¬Sat none w
      (extractPassTagged (tags n) (rawTagged tags f w n)) n := by
  obtain ⟨N, hN⟩ := general_eventually_false_protected_constraints
    (x := Class.ofFormula f) (w := w) ⟨f, hn, rfl⟩ ((classTag_exact _ _).mp hpi)
    (fun h => hf ((ofFormula_holds f).mp h))
  refine ⟨N, fun n hge ht => ?_⟩
  obtain ⟨C, hC, hc⟩ := hN n hge
  rw [← rawTagged_class tags hs hn w n] at hC
  have hi := extractPassTagged_protected_constraint (tags n) (hl n)
    (rawTagged_nnf tags hs hn w n) hC
  exact hc ((U_holds C).mp (implication_sound hi ((ofFormula_holds _).mpr ht)))

/-- A false first pass cannot answer finite on a never-false run: the
refined finite-window theorem would force the all-field to become false.
This proves exclusion of the actual finite-retry branch, not a replacement
of the input by an existential structural grammar witness. -/
theorem runTagged_false_pass_disables_retry (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hn : NNF f) (w : Word (Fin ap))
    (hnever : ∀ n, Class.ofFormula (runTagged tags f w n).all ≠ Class.bot)
    (n : Nat) (hf : ¬Sat none w (extractPassTagged (tags n) (rawTagged tags f w n)) n) :
    rhoTagged (tags n) (rawTagged tags f w n) =
      extractPassTagged (tags n) (rawTagged tags f w n) := by
  have hnot : tags n (extractPassTagged (tags n) (rawTagged tags f w n)) .finite = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    apply hf
    apply runTagged_finite_obligation tags hs hn w hnever n (hs n _ .finite ht)
    rw [← rawTagged_unfold tags hs hn w n]
    exact extractPassTagged_weakens (tags n) (rawTagged_nnf tags hs hn w n)
  simp only [rhoTagged, hnot, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem runTagged_eventually_false_seeds (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hpi : classBits f .pi2 = true) (w : Word (Fin ap))
    (hf : ¬Sat none w f 0)
    (hnever : ∀ n, Class.ofFormula (runTagged tags f w n).all ≠ Class.bot) :
    ∃ N, ∀ n, N ≤ n → ¬Sat none w (rhoTagged (tags n) (rawTagged tags f w n)) n := by
  obtain ⟨N, hN⟩ := runTagged_eventually_false_passes tags hs hl hn hpi w hf
  refine ⟨N, fun n hge => ?_⟩
  rw [runTagged_false_pass_disables_retry tags hs hn w hnever n (hN n hge)]
  exact hN n hge

end Tlsf.Dpa.Impl
