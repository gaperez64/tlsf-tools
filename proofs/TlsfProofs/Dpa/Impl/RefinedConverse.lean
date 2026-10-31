import TlsfProofs.Dpa.Impl.RefinedAcceptance

/-!
# The false-seed converse with refined, changing classifiers

The ordered table is `src/lib/dpa_dela.c:5`. Co-safety suspensions may
discard an active field. The invariant used here therefore permits both
the false sentinel and false active obligations: once every new seed is
false, neither a suspension nor a resumption can enable another renewal.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

/-- Outside the true/safety rows, a marked renewal installs the new seed
as a conjunct. An already false field also stays false through suspension,
resumption, renewal and ordinary progress. -/
theorem rowTagged_false_seed (tags : TagClassifier ap) (w : Word (Fin ap)) (j : Nat)
    (ht : equivalent (unfoldSyntax a) .tt = false)
    (hsa : tags (unfoldSyntax a) .safety = false)
    (hseed : ¬Sat none w (rhoTagged tags a) j)
    (hr : (rowTagged tags a r).mark = true ∨ ¬Sat none w r j) :
    ¬Sat none w (rowTagged tags a r).target.rejecting j := by
  simp only [rowTagged, ht, hsa, Bool.false_eq_true, ↓reduceIte] at hr ⊢
  split
  · simp [Sat]
  · split
    · simp [Sat]
    · split
      · exact hseed
      · split
        · split
          · simp [Sat]
          · exact fun h => hseed h.2.2
        · simp_all

/-- A false incoming active field cannot renew if a positive finite answer
would certify its satisfaction. The sentinel branch remains unmarked. -/
theorem rowTagged_false_unmarked (tags : TagClassifier ap) (w : Word (Fin ap)) (j : Nat)
    (ht : equivalent (unfoldSyntax a) .tt = false)
    (hsa : tags (unfoldSyntax a) .safety = false)
    (hf : Class.ofFormula r ≠ Class.bot → tags r .finite = true → Sat none w r j)
    (hr : ¬Sat none w r j) : (rowTagged tags a r).mark = false := by
  simp only [rowTagged, ht, hsa, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i hb
        have hne : Class.ofFormula r ≠ Class.bot := fun he => hb ((equivalent_exact _ _).mpr he)
        have hn : tags r .finite = false := Bool.eq_false_iff.mpr (fun h => hr (hf hne h))
        simp only [hn, Bool.false_eq_true, ↓reduceIte]

/-- A false-seed suffix suffices for the converse without any Π₂ premise.
This formulation handles refined co-safety suspensions directly; it does
not need those positive answers to persist at later calls. -/
theorem runTagged_converse_of_false_seeds (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hn : NNF f) (w : Word (Fin ap))
    (hseeds : ¬Sat none w f 0 →
      (∀ n, Class.ofFormula (runTagged tags f w n).all ≠ Class.bot) →
      ∃ N, ∀ n, N ≤ n → ¬Sat none w (rhoTagged (tags n) (rawTagged tags f w n)) n) :
    Inf (marksTagged tags f w) → Sat none w f 0 := by
  intro hi
  apply Classical.byContradiction
  intro hw
  have hnever := runTagged_accepting_never_bot tags hs hn w hi
  obtain ⟨N, hN⟩ := hseeds hw hnever
  have htop (n : Nat) :
      equivalent (unfoldSyntax (rawTagged tags f w n)) .tt = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    apply hw
    apply (runTagged_all_language tags hs hn w n).mp
    apply (ofFormula_holds _).mp
    rw [← rawTagged_unfold tags hs hn w n, U_ofFormula, (equivalent_exact _ _).mp ht]
    rfl
  have hsa (n : Nat) : tags n (unfoldSyntax (rawTagged tags f w n)) .safety = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    apply hw
    apply runTagged_accepting_safety tags hs hn w hi n
    change HasTag (RefinedAtom .safety) _
    rw [← rawTagged_unfold tags hs hn w n, U_ofFormula]
    exact hs n _ .safety ht
  have hfinite (n : Nat)
      (hne : Class.ofFormula (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).rejecting)) ≠
        Class.bot)
      (ht : tags (n+1) (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).rejecting))
        .finite = true) :
      Sat none w (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).rejecting)) (n+1) := by
    apply runTagged_finite_obligation tags hs hn w hnever (n+1) (hs (n+1) _ .finite ht)
    have hprev : Class.ofFormula (runTagged tags f w n).rejecting ≠ Class.bot := by
      intro hb
      apply hne
      rw [← U_ofFormula, ← D_ofFormula, hb, D_class_bot]
      rfl
    have himp := U_monotone (D_monotone (w n)
      ((runTagged_spec tags hs hn w n).1.2.2.2.2.2 hprev))
    rw [← (transitionTagged_spec (tags (n+1)) (hs (n+1)) (w n)
      (runTagged_spec tags hs hn w n).1).2] at himp
    simpa only [runTagged, U_ofFormula, D_ofFormula] using himp
  have hprogress (n : Nat)
      (hr : ¬Sat none w (runTagged tags f w n).rejecting n) :
      ¬Sat none w (unfoldSyntax (stepSyntax (w n) (runTagged tags f w n).rejecting)) (n+1) := by
    intro ht
    apply hr
    have he := (derivatives_holds w n 1 (Class.ofFormula (runTagged tags f w n).rejecting)).mp
    apply (ofFormula_holds _).mp
    apply he
    rw [derivatives, derivatives, U_holds, delta,
      (runTagged_spec tags hs hn w n).1.2.2.2.1,
      D_ofFormula, U_ofFormula, ofFormula_holds]
    exact ht
  obtain ⟨m, hNm, hm⟩ := hi N
  have hfalse : ¬Sat none w (runTagged tags f w (m+1)).rejecting (m+1) := by
    exact rowTagged_false_seed (tags (m+1)) w (m+1) (htop (m+1)) (hsa (m+1))
      (hN (m+1) (by omega)) (Or.inl hm)
  have htail (k : Nat) : ¬Sat none w (runTagged tags f w (m+1+k)).rejecting (m+1+k) := by
    induction k with
    | zero => exact hfalse
    | succ k ih =>
      have he : m+1+(k+1) = (m+1+k)+1 := by omega
      rw [he]
      exact rowTagged_false_seed (tags ((m+1+k)+1)) w ((m+1+k)+1)
        (htop ((m+1+k)+1)) (hsa ((m+1+k)+1))
        (hN ((m+1+k)+1) (by omega)) (Or.inr (hprogress _ ih))
  obtain ⟨n, hnge, hm⟩ := hi (m+1)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnge
  have hu := rowTagged_false_unmarked (tags ((m+1+k)+1)) w ((m+1+k)+1)
    (htop ((m+1+k)+1)) (hsa ((m+1+k)+1)) (hfinite _) (hprogress _ (htail k))
  exact Bool.noConfusion (hu.symm.trans hm)

/-- Structural Π₂ inputs, but fully refined and changing classifiers in
every executable extraction and transition. -/
theorem runTagged_pi2_language (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hpi : classBits f .pi2 = true) (w : Word (Fin ap)) :
    Inf (marksTagged tags f w) ↔ Sat none w f 0 :=
  ⟨runTagged_converse_of_false_seeds tags hs hn w
    (runTagged_eventually_false_seeds tags hs hl hn hpi w),
    runTagged_satisfying_accepts tags hs hl hn w⟩

theorem defaultTrace_pi2_language (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) (hv : s.Valid) (hn : NNF f) (hpi : classBits f .pi2 = true)
    (w : Word (Fin ap)) :
    Inf (marksTagged (defaultTraceClassifier rank highFirst fuel before programs s) f w) ↔
      Sat none w f 0 :=
  runTagged_pi2_language _
    (fun n => (defaultTraceClassifier_spec rank highFirst fuel before programs s hv n).1)
    (fun n => (defaultTraceClassifier_spec rank highFirst fuel before programs s hv n).2)
    hn hpi w

/-- Both one-colour parity orientations for the same refined run. -/
theorem runTagged_pi2_parity (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hpi : classBits f .pi2 = true) (w : Word (Fin ap)) :
    (MinEven (oneSetMin false (marksTagged tags f w)) ↔ Sat none w f 0) ∧
      (MaxOdd (oneSetExport false (marksTagged tags f w)) ↔ Sat none w f 0) :=
  ⟨(oneSet_min_inf _).trans (runTagged_pi2_language tags hs hl hn hpi w),
    (oneSet_max_inf _).trans (runTagged_pi2_language tags hs hl hn hpi w)⟩

/-- Acceptance discharges every active obligation, even one later discarded
by a refined co-safety suspension. The input hypothesis is structural Π₂. -/
theorem runTagged_pi2_active_obligation (tags : Nat → TagClassifier ap)
    (hs : ∀ n, (tags n).Sound) (hl : ∀ n, (tags n).Lower)
    (hn : NNF f) (hpi : classBits f .pi2 = true) (w : Word (Fin ap))
    (hi : Inf (marksTagged tags f w)) (n : Nat)
    (ha : Class.ofFormula (runTagged tags f w n).rejecting ≠ Class.bot) :
    Sat none w (runTagged tags f w n).rejecting n := by
  apply (ofFormula_holds _).mp
  apply implication_sound ((runTagged_spec tags hs hn w n).1.2.2.2.2.2 ha)
  exact (ofFormula_holds _).mpr ((runTagged_all_language tags hs hn w n).mpr
    ((runTagged_pi2_language tags hs hl hn hpi w).mp hi))

end Tlsf.Dpa.Impl
