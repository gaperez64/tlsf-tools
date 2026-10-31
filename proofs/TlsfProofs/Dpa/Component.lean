import TlsfProofs.Dpa.Stage1

/-! # STAGE2 §§2–3: local invariant and all-field exactness.
The transition function is shared with Stage1, so its ordered rows and mark 0
have a single definition. These results impose no Π₂ converse assumption.
-/
namespace Tlsf.Dpa
open Class
variable {ap : Nat}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem implies_bot {x : Class ap} (h : x ⇒ₚ Class.bot) : x = Class.bot := by
  apply Class.ext; intro σ
  change x σ = false
  exact Bool.eq_false_iff.mpr (fun ht => Bool.noConfusion (h σ ht))

theorem bot_hasTag (tag : Formula (Fin ap) → Prop) : HasTag tag Class.bot := by
  intro a ha; obtain ⟨σ, b, hb⟩ := ha
  exact False.elim (hb rfl)

theorem meet_implied {a r q : Class ap} (hr : a ⇒ₚ r) (hq : a ⇒ₚ q) : a ⇒ₚ meet r q := by
  intro σ ha
  change (r σ && q σ) = true
  simp [hr σ ha, hq σ ha]

/-- STAGE2 §3: an active component cannot resume before the false row. -/
theorem no_active_resume (v : Letter (Fin ap)) (s : Pair ap) (h : s.all ⇒ₚ s.rejecting)
    (hn : U (D v s.all) ≠ Class.bot) : U (D v s.rejecting) ≠ Class.bot := by
  intro he
  have hi := U_monotone (D_monotone v h)
  rw [he] at hi
  exact hn (implies_bot hi)

/-- STAGE2 §3: the explicit false-renewal target is unreachable from an
active invariant state. This uses the seed extracted from raw `Dᵥ A`. -/
theorem no_false_renewal (v : Letter (Fin ap)) (s : Pair ap) (h : s.all ⇒ₚ s.rejecting)
    (hx : NNFClass s.all) (hn : U (D v s.all) ≠ Class.bot) :
    meet (U (D v s.rejecting)) (rho (D v s.all)) ≠ Class.bot := by
  intro he
  have hi := meet_implied (U_monotone (D_monotone v h)) (rho_weakens (D_nnfClass v hx))
  rw [he] at hi
  exact hn (implies_bot hi)

/-- The all-field is unfolded NNF. Suspension can only have been caused by
one of the permanent safety/co-safety rows. Active fields satisfy (2). -/
def ComponentInvariant (s : Pair ap) : Prop :=
  NNFClass s.all ∧ U s.all = s.all ∧
  (s.rejecting = Class.bot → Simple s.all) ∧
  (s.rejecting ≠ Class.bot → s.all ⇒ₚ s.rejecting)

theorem initial_invariant (x : Class ap) (hx : NNFClass x) : ComponentInvariant (initial x) := by
  have hnn := U_nnfClass hx
  have hu := U_idempotent x
  unfold initial ComponentInvariant
  split
  · rename_i hs
    exact ⟨hnn, hu, fun _ => hs, fun h => False.elim (h rfl)⟩
  · rename_i hs
    exact ⟨hnn, hu, fun hr => by
      have hi := rho_weakens hx
      change rho x = Class.bot at hr
      rw [hr] at hi
      have he := implies_bot hi
      change Simple (U x)
      rw [he]
      exact Or.inl (bot_hasTag safety), fun _ => rho_weakens hx⟩

theorem transition_all_exact (v : Letter (Fin ap)) (s : Pair ap) (h : ComponentInvariant s) :
    (transition v s).target.all = U (D v s.all) := by
  by_cases hs : Simple s.all
  · exact (simple_transition v s hs).1
  · have hrne : s.rejecting ≠ Class.bot := fun he => hs (h.2.2.1 he)
    have hi := h.2.2.2 hrne
    simp only [transition]
    split
    · rename_i he; exact he.symm
    · split
      · rename_i he; exact he.symm
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · have hq := no_false_renewal v s hi h.1 (by assumption)
                simp only [hq, ↓reduceIte]
              · rfl

theorem suspended_invariant (a : Class ap) (hnn : NNFClass a) (hu : U a = a) (hs : Simple a) :
    ComponentInvariant ⟨a, Class.bot⟩ :=
  ⟨hnn, hu, fun _ => hs, fun h => False.elim (h rfl)⟩

theorem active_invariant (a r : Class ap) (hnn : NNFClass a) (hu : U a = a)
    (hr : r ≠ Class.bot) (hi : a ⇒ₚ r) : ComponentInvariant ⟨a, r⟩ :=
  ⟨hnn, hu, fun h => False.elim (hr h), fun _ => hi⟩

/-- STAGE2 §3 (2), including every transition-table row. -/
theorem transition_invariant (v : Letter (Fin ap)) (s : Pair ap) (h : ComponentInvariant s) :
    ComponentInvariant (transition v s).target := by
  have hnn := U_nnfClass (D_nnfClass v h.1)
  have hu := U_idempotent (D v s.all)
  by_cases hb : U (D v s.all) = Class.bot
  · have he : (transition v s).target = ⟨Class.bot, Class.bot⟩ := by simp [transition, hb]
    rw [he]
    exact suspended_invariant _ ⟨.ff, trivial, rfl⟩ rfl (Or.inl (bot_hasTag _))
  · by_cases ht : U (D v s.all) = Class.top
    · have hne : (Class.top : Class ap) ≠ Class.bot := fun he => hb (ht.trans he)
      have he : (transition v s).target = ⟨Class.top, Class.bot⟩ := by simp [transition, ht, hne]
      rw [he]
      exact suspended_invariant _ ⟨.tt, trivial, rfl⟩ U_top (Or.inl (top_hasTag _))
    · by_cases hsa : HasTag safety (U (D v s.all))
      · have he : (transition v s).target = ⟨U (D v s.all), Class.bot⟩ := by
          simp [transition, hb, ht, hsa]
        rw [he]; exact suspended_invariant _ hnn hu (Or.inl hsa)
      · by_cases hco : HasTag cosafety (U (D v s.all))
        · have he : (transition v s).target = ⟨U (D v s.all), Class.bot⟩ := by
            simp [transition, hb, ht, hsa, hco]
          rw [he]; exact suspended_invariant _ hnn hu (Or.inr hco)
        · have hr : s.rejecting ≠ Class.bot := by
            intro he
            exact (simple_step v (h.2.2.1 he)).elim hsa hco
          have hi := h.2.2.2 hr
          have hrnext := no_active_resume v s hi hb
          have hstep := U_monotone (D_monotone v hi)
          by_cases hf : HasTag finite (U (D v s.rejecting))
          · have hq := no_false_renewal v s hi h.1 hb
            have he : (transition v s).target =
                ⟨U (D v s.all), meet (U (D v s.rejecting)) (rho (D v s.all))⟩ := by
              simp [transition, hb, ht, hsa, hco, hrnext, hf, hq]
            rw [he]
            exact active_invariant _ _ hnn hu hq
              (meet_implied hstep (rho_weakens (D_nnfClass v h.1)))
          · have he : (transition v s).target = ⟨U (D v s.all), U (D v s.rejecting)⟩ := by
              simp [transition, hb, ht, hsa, hco, hrnext, hf]
            rw [he]; exact active_invariant _ _ hnn hu hrnext hstep

theorem run_invariant (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap)) (n : Nat) :
    ComponentInvariant (run x w n) := by
  induction n with
  | zero => exact initial_invariant x hx
  | succ n ih => exact transition_invariant (w n) (run x w n) ih

/-- STAGE2 §3: no reachable resumption in the conservative baseline. -/
theorem resume_unreachable (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap)) (n : Nat)
    (ha : ¬Simple (U (D (w n) (run x w n).all)))
    (hne : U (D (w n) (run x w n).all) ≠ Class.bot) :
    U (D (w n) (run x w n).rejecting) ≠ Class.bot := by
  have hi := run_invariant x hx w n
  have hr : (run x w n).rejecting ≠ Class.bot := by
    intro hr
    exact ha (simple_step _ (hi.2.2.1 hr))
  exact no_active_resume _ _ (hi.2.2.2 hr) hne

theorem all_field_derivative (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap)) (n : Nat) :
    (run x w n).all = derivatives w 0 n x := by
  induction n with
  | zero => exact initial_all x
  | succ n ih =>
    change (transition (w n) (run x w n)).target.all = _
    rw [transition_all_exact _ _ (run_invariant x hx w n), ih, derivatives_snoc, Nat.zero_add]

/-- STAGE2 §3 (3), including the false sink and every breakpoint round. -/
theorem all_field_exactness (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap)) (n : Nat) :
    Holds w n (run x w n).all ↔ Holds w 0 x := by
  rw [all_field_derivative x hx w n]
  simpa only [Nat.zero_add] using derivatives_holds w 0 n x

/-- Every rejecting field, including the sentinel, remains unfolded NNF
and passes the co-safety support test. -/
def RemainderInvariant (r : Class ap) : Prop :=
  NNFClass r ∧ U r = r ∧ HasTag cosafety r

theorem bot_remainder : RemainderInvariant (Class.bot : Class ap) :=
  ⟨⟨.ff, trivial, rfl⟩, rfl, bot_hasTag _⟩

theorem rho_remainder (hx : NNFClass x) : RemainderInvariant (rho x) :=
  ⟨rho_nnfClass hx, rho_unfolded x, rho_cosafety x⟩

theorem step_remainder (v : Letter (Fin ap)) (h : RemainderInvariant r) :
    RemainderInvariant (U (D v r)) :=
  ⟨U_nnfClass (D_nnfClass v h.1), U_idempotent _, U_cosafety (D_cosafety v h.2.2)⟩

theorem meet_remainder (h : RemainderInvariant r) (h' : RemainderInvariant q) :
    RemainderInvariant (meet r q) :=
  ⟨meet_nnfClass h.1 h'.1, by rw [U_meet, h.2.1, h'.2.1], meet_tag h.2.2 h'.2.2⟩

theorem transition_remainder (v : Letter (Fin ap)) (s : Pair ap)
    (ha : NNFClass s.all) (hr : RemainderInvariant s.rejecting) :
    RemainderInvariant (transition v s).target.rejecting := by
  have hs := step_remainder v hr
  have hseed := rho_remainder (D_nnfClass v ha)
  have hq := meet_remainder hs hseed
  simp only [transition]
  split
  · exact bot_remainder
  · split
    · exact bot_remainder
    · split
      · exact bot_remainder
      · split
        · exact bot_remainder
        · split
          · exact hseed
          · split
            · split
              · exact bot_remainder
              · exact hq
            · exact hs

theorem run_remainder (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap)) (n : Nat) :
    RemainderInvariant (run x w n).rejecting := by
  induction n with
  | zero =>
    change RemainderInvariant (initial x).rejecting
    unfold initial; split
    · exact bot_remainder
    · exact rho_remainder hx
  | succ n ih => exact transition_remainder _ _ (run_invariant x hx w n).1 ih

theorem run_after (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap)) (t k : Nat) :
    (run x w (t+k)).all = derivatives w t k (run x w t).all := by
  rw [all_field_derivative x hx w (t+k), all_field_derivative x hx w t,
    derivatives_add w 0 t k x, Nat.zero_add]

/-- A satisfied safety/co-safety suffix has a later marked transition. -/
theorem simple_suffix_mark (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hw : Holds w 0 x) (t : Nat) (hs : Simple (run x w t).all) :
    ∃ n, t ≤ n ∧ marks x w n = true := by
  rcases hs with hsa | hco
  · refine ⟨t, Nat.le_refl _, safety_marks _ _ hsa ?_⟩
    rw [← transition_all_exact _ _ (run_invariant x hx w t)]
    change (run x w (t+1)).all ≠ Class.bot
    exact holds_not_bot ((all_field_exactness x hx w (t+1)).mpr hw)
  · have hi := run_invariant x hx w t
    have ht := (all_field_exactness x hx w t).mpr hw
    obtain ⟨k, hk⟩ := class_cosafety_witness _ (nnfClass_positive hi.1) hco ht
    refine ⟨t+k, by omega, ?_⟩
    apply (true_transition _ _ ?_).2
    rw [run_after x hx w t k, hk]

/-- An unmarked transition to a non-simple all-field is exact progression
of R. Its unfolded raw remainder cannot be finite. -/
theorem unmarked_active_progress (v : Letter (Fin ap)) (s : Pair ap)
    (h : ComponentInvariant s) (hs : ¬Simple (U (D v s.all)))
    (hm : (transition v s).mark = false) :
    (transition v s).target.rejecting = U (D v s.rejecting) ∧
      ¬HasTag finite (U (D v s.rejecting)) := by
  have hb : U (D v s.all) ≠ Class.bot := by
    intro he; apply hs; rw [he]; exact Or.inl (bot_hasTag _)
  have ht : U (D v s.all) ≠ Class.top := by
    intro he; apply hs; rw [he]; exact Or.inl (top_hasTag _)
  have hsa : ¬HasTag safety (U (D v s.all)) := fun h => hs (Or.inl h)
  have hco : ¬HasTag cosafety (U (D v s.all)) := fun h => hs (Or.inr h)
  have hr : s.rejecting ≠ Class.bot := fun he => hs (simple_step v (h.2.2.1 he))
  have hi := h.2.2.2 hr
  have hrnext := no_active_resume v s hi hb
  have hq := no_false_renewal v s hi h.1 hb
  have hf : ¬HasTag finite (U (D v s.rejecting)) := by
    intro hf
    have he : (transition v s).mark = true := by
      simp [transition, hb, ht, hsa, hco, hrnext, hf, hq]
    exact Bool.noConfusion (hm.symm.trans he)
  exact ⟨by simp [transition, hb, ht, hsa, hco, hrnext, hf], hf⟩

/-- STAGE2 §3 (4). A satisfying word accepts; no Π₂ converse or
cohort correspondence is needed for this direction. -/
theorem satisfying_accepts (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hw : Holds w 0 x) : Inf (marks x w) := by
  apply Classical.byContradiction; intro hn
  obtain ⟨N, hN⟩ := (not_inf_iff_fin _).mp hn
  have hsimple : ∀ n, N ≤ n → ¬Simple (run x w n).all := by
    intro n hn hs
    obtain ⟨k, hnk, hk⟩ := simple_suffix_mark x hx w hw n hs
    exact Bool.noConfusion ((hN k (by omega)).symm.trans hk)
  have hprogress : ∀ n, N ≤ n →
      (run x w (n+1)).rejecting = U (D (w n) (run x w n).rejecting) ∧
        ¬HasTag finite (U (D (w n) (run x w n).rejecting)) := by
    intro n hn
    apply unmarked_active_progress _ _ (run_invariant x hx w n) _ (hN n hn)
    rw [← transition_all_exact _ _ (run_invariant x hx w n)]
    exact hsimple (n+1) (by omega)
  have hi := run_invariant x hx w N
  have hractive : (run x w N).rejecting ≠ Class.bot := fun he => hsimple N (Nat.le_refl _) (hi.2.2.1 he)
  have hrsat : Holds w N (run x w N).rejecting :=
    implication_sound (hi.2.2.2 hractive) ((all_field_exactness x hx w N).mpr hw)
  have hri := run_remainder x hx w N
  obtain ⟨k, hk⟩ := class_cosafety_witness _ (nnfClass_positive hri.1) hri.2.2 hrsat
  have hrderiv : ∀ k, (run x w (N+k)).rejecting =
      derivatives w N k (run x w N).rejecting := by
    intro k; induction k with
    | zero => simpa only [Nat.add_zero, derivatives] using hri.2.1.symm
    | succ k ih =>
      have he : N+(k+1) = (N+k)+1 := by omega
      rw [he, (hprogress (N+k) (by omega)).1, ih, derivatives_snoc]
  have htop : (run x w (N+k)).rejecting = Class.top := by rw [hrderiv k, hk]
  have hnotfinite := (hprogress (N+k) (by omega)).2
  have hd : D (w (N+k)) Class.top = Class.top := by apply Class.ext; intro σ; rfl
  rw [htop, hd, U_top] at hnotfinite
  exact hnotfinite (top_hasTag _)

theorem accepting_never_bot (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hi : Inf (marks x w)) (n : Nat) : (run x w n).all ≠ Class.bot := by
  intro hb
  have hfin : FinMarks (marks x w) := by
    refine ⟨n, fun k hk => ?_⟩
    apply (false_transition _ _ ?_).2
    rw [all_field_derivative x hx w k]
    apply derivatives_bot_persists _ hk
    rwa [← all_field_derivative x hx w n]
  exact (complete_complement _).mp hfin hi

/-- The all-field entails every earlier active obligation, even after
suspension. This is the all-field form of STAGE2 §3 (5). -/
theorem all_preserves_obligation (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (t : Nat) (ha : (run x w t).rejecting ≠ Class.bot) (k : Nat) :
    (run x w (t+k)).all ⇒ₚ derivatives w t k (run x w t).rejecting := by
  have hi := (run_invariant x hx w t).2.2.2 ha
  rw [run_after x hx w t k]
  exact derivatives_monotone w t k hi

theorem finite_implies_safety (f : Formula α) (h : finite f) : safety f := by
  induction f with
  | tt | ff | ap _ => trivial
  | neg f ih => cases f <;> simp_all [finite, safety]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf h.1, ihg h.2⟩
  | next f ih => exact ih h
  | _ => contradiction

/-- Any finite obligation implied by A is satisfied on an accepting run.
It can be carried through arbitrarily many later renewals. -/
theorem accepting_finite_obligation (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hi : Inf (marks x w)) (t : Nat) (E : Class ap) (hE : NNFClass E)
    (hf : HasTag finite E) (himp : (run x w t).all ⇒ₚ E) : Holds w t E := by
  apply Classical.byContradiction; intro hn
  have hsafe : HasTag safety E := fun a ha => finite_implies_safety a (hf a ha)
  obtain ⟨k, hk⟩ := class_safety_bad_prefix E (nnfClass_positive hE) hsafe hn
  have ha := derivatives_monotone w t k himp
  rw [hk, ← run_after x hx w t k] at ha
  exact accepting_never_bot x hx w hi (t+k) (implies_bot ha)

theorem accepting_safety_suffix (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hi : Inf (marks x w)) (t : Nat) (hs : HasTag safety (run x w t).all) :
    Holds w t (run x w t).all := by
  apply Classical.byContradiction; intro hn
  have hiNNF := (run_invariant x hx w t).1
  obtain ⟨k, hk⟩ := class_safety_bad_prefix _ (nnfClass_positive hiNNF) hs hn
  have hb : (run x w (t+k)).all = Class.bot := by rw [run_after x hx w t k, hk]
  exact accepting_never_bot x hx w hi (t+k) hb

theorem derivatives_cosafety (w : Word (Fin ap)) (j k : Nat) (hc : HasTag cosafety y) :
    HasTag cosafety (derivatives w j k y) := by
  induction k generalizing j y with
  | zero => exact U_cosafety hc
  | succ k ih => exact ih _ (U_cosafety (D_cosafety _ (U_cosafety hc)))

/-- An accepting permanently suspended suffix satisfies its all-field. -/
theorem accepting_simple_suffix (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hi : Inf (marks x w)) (t : Nat) (hs : Simple (run x w t).all) :
    Holds w t (run x w t).all := by
  rcases hs with hsa | hco
  · exact accepting_safety_suffix x hx w hi t hsa
  · obtain ⟨n, htn, hn⟩ := hi t
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htn
    have hconow : HasTag cosafety (run x w (t+k)).all := by
      rw [run_after x hx w t k]
      exact derivatives_cosafety w t k hco
    have hsanext : HasTag safety (run x w ((t+k)+1)).all :=
      cosafety_mark_safety _ _ hconow hn
    have hsat := accepting_safety_suffix x hx w hi ((t+k)+1) hsanext
    exact (all_field_exactness x hx w t).mpr ((all_field_exactness x hx w ((t+k)+1)).mp hsat)

/-- A marked active transition is a genuine finite-remainder renewal. -/
theorem marked_active_renewal (v : Letter (Fin ap)) (s : Pair ap) (h : ComponentInvariant s)
    (hs : ¬Simple (U (D v s.all))) (hm : (transition v s).mark = true) :
    HasTag finite (U (D v s.rejecting)) ∧
      (transition v s).target.rejecting = meet (U (D v s.rejecting)) (rho (D v s.all)) := by
  have hb : U (D v s.all) ≠ Class.bot := by
    intro he; apply hs; rw [he]; exact Or.inl (bot_hasTag _)
  have ht : U (D v s.all) ≠ Class.top := by
    intro he; apply hs; rw [he]; exact Or.inl (top_hasTag _)
  have hsa : ¬HasTag safety (U (D v s.all)) := fun h => hs (Or.inl h)
  have hco : ¬HasTag cosafety (U (D v s.all)) := fun h => hs (Or.inr h)
  have hr : s.rejecting ≠ Class.bot := fun he => hs (simple_step v (h.2.2.1 he))
  have hi := h.2.2.2 hr
  have hrnext := no_active_resume v s hi hb
  have hq := no_false_renewal v s hi h.1 hb
  by_cases hf : HasTag finite (U (D v s.rejecting))
  · exact ⟨hf, by simp [transition, hb, ht, hsa, hco, hrnext, hf, hq]⟩
  · have he : (transition v s).mark = false := by
      simp [transition, hb, ht, hsa, hco, hrnext, hf]
    exact False.elim (Bool.noConfusion (he.symm.trans hm))

/-- STAGE2 §3: accepting runs satisfy every active rejecting field. The
first later renewal finishes a finite derivative; (2) preserves its check. -/
theorem accepting_active_obligation (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hi : Inf (marks x w)) (t : Nat) (ha : (run x w t).rejecting ≠ Class.bot) :
    Holds w t (run x w t).rejecting := by
  by_cases hs : ∃ k, Simple (run x w (t+k)).all
  · obtain ⟨k, hk⟩ := hs
    have hsat := accepting_simple_suffix x hx w hi (t+k) hk
    have hob := implication_sound (all_preserves_obligation x hx w t ha k) hsat
    exact (derivatives_holds w t k _).mp hob
  · have hns : ∀ k, ¬Simple (run x w (t+k)).all := fun k hk => hs ⟨k, hk⟩
    have hex : ∃ k, marks x w (t+k) = true := by
      obtain ⟨n, hn, hm⟩ := hi t
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact ⟨k, hm⟩
    obtain ⟨k, hk, hmin⟩ := exists_least_nat hex
    have hR : ∀ j, j ≤ k → (run x w (t+j)).rejecting =
        derivatives w t j (run x w t).rejecting := by
      intro j; induction j with
      | zero =>
        intro _
        simpa only [Nat.add_zero, derivatives] using (run_remainder x hx w t).2.1.symm
      | succ j ih =>
        intro hj
        have hmark : marks x w (t+j) = false :=
          Bool.eq_false_iff.mpr (hmin j (by omega))
        have hsimple : ¬Simple (U (D (w (t+j)) (run x w (t+j)).all)) := by
          rw [← transition_all_exact _ _ (run_invariant x hx w (t+j))]
          have he : (t+j)+1 = t+(j+1) := by omega
          change ¬Simple (run x w ((t+j)+1)).all
          rw [he]
          exact hns (j+1)
        have hp := (unmarked_active_progress _ _ (run_invariant x hx w (t+j)) hsimple hmark).1
        have he : t+(j+1) = (t+j)+1 := by omega
        rw [he]
        change (transition (w (t+j)) (run x w (t+j))).target.rejecting = _
        rw [hp, ih (by omega), derivatives_snoc]
    have hsimple : ¬Simple (U (D (w (t+k)) (run x w (t+k)).all)) := by
      rw [← transition_all_exact _ _ (run_invariant x hx w (t+k))]
      have he : (t+k)+1 = t+(k+1) := by omega
      change ¬Simple (run x w ((t+k)+1)).all
      rw [he]
      exact hns (k+1)
    have hrenew := marked_active_renewal _ _ (run_invariant x hx w (t+k)) hsimple hk
    let E := U (D (w (t+k)) (run x w (t+k)).rejecting)
    have hE : RemainderInvariant E := step_remainder _ (run_remainder x hx w (t+k))
    have hraw : (run x w (t+k)).all ⇒ₚ (run x w (t+k)).rejecting := by
      apply (run_invariant x hx w (t+k)).2.2.2
      intro he
      exact hns k ((run_invariant x hx w (t+k)).2.2.1 he)
    have hAE : (run x w ((t+k)+1)).all ⇒ₚ E := by
      change (transition (w (t+k)) (run x w (t+k))).target.all ⇒ₚ E
      rw [transition_all_exact _ _ (run_invariant x hx w (t+k))]
      exact U_monotone (D_monotone _ hraw)
    have hsat := accepting_finite_obligation x hx w hi ((t+k)+1) E hE.1 hrenew.1 hAE
    have hED : E = derivatives w t (k+1) (run x w t).rejecting := by
      dsimp only [E]
      rw [hR k (Nat.le_refl _), derivatives_snoc]
    rw [hED] at hsat
    have he : (t+k)+1 = t+(k+1) := by omega
    rw [he] at hsat
    exact (derivatives_holds w t (k+1) _).mp hsat

/-- Every seed actually extracted at an active marked renewal is satisfied
at the target position, even when the retained remainder is nonconstant. -/
theorem accepting_renewal_seed (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hi : Inf (marks x w)) (n : Nat) (hm : marks x w n = true)
    (hs : ¬Simple (run x w (n+1)).all) :
    Holds w (n+1) (rho (D (w n) (run x w n).all)) := by
  have hsimple : ¬Simple (U (D (w n) (run x w n).all)) := by
    rw [← transition_all_exact _ _ (run_invariant x hx w n)]
    exact hs
  have hr := (marked_active_renewal _ _ (run_invariant x hx w n) hsimple hm).2
  have hactive : (run x w (n+1)).rejecting ≠ Class.bot :=
    fun he => hs ((run_invariant x hx w (n+1)).2.2.1 he)
  have hsat := accepting_active_obligation x hx w hi (n+1) hactive
  change Holds w (n+1) (transition (w n) (run x w n)).target.rejecting at hsat
  rw [hr] at hsat
  exact (Bool.and_eq_true_iff.mp hsat).2

theorem rejecting_step_preserves (v : Letter (Fin ap)) (s : Pair ap)
    (h : ComponentInvariant s) (hn : (transition v s).target.rejecting ≠ Class.bot) :
    (transition v s).target.rejecting ⇒ₚ U (D v s.rejecting) := by
  by_cases hb : U (D v s.all) = Class.bot
  · simp [transition, hb] at hn
  · by_cases ht : U (D v s.all) = Class.top
    · have hne : (Class.top : Class ap) ≠ Class.bot := fun he => hb (ht.trans he)
      simp [transition, ht, hne] at hn
    · by_cases hsa : HasTag safety (U (D v s.all))
      · simp [transition, hb, ht, hsa] at hn
      · by_cases hco : HasTag cosafety (U (D v s.all))
        · simp [transition, hb, ht, hsa, hco] at hn
        · have hr : s.rejecting ≠ Class.bot := by
            intro he; exact (simple_step v (h.2.2.1 he)).elim hsa hco
          have hi := h.2.2.2 hr
          have hrnext := no_active_resume v s hi hb
          have hq := no_false_renewal v s hi h.1 hb
          by_cases hf : HasTag finite (U (D v s.rejecting))
          · have he : (transition v s).target.rejecting =
                meet (U (D v s.rejecting)) (rho (D v s.all)) := by
              simp [transition, hb, ht, hsa, hco, hrnext, hf, hq]
            rw [he]
            intro σ hs
            exact (Bool.and_eq_true_iff.mp hs).1
          · have he : (transition v s).target.rejecting = U (D v s.rejecting) := by
              simp [transition, hb, ht, hsa, hco, hrnext, hf]
            rw [he]; exact implies_refl _

/-- STAGE2 §3 (5), the rejecting-field form, until suspension. Retaining
U(r) at renewal is exactly the premise used in `rejecting_step_preserves`. -/
theorem rejecting_preserves_obligation (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (t k : Nat) (hactive : ∀ j, j ≤ k → (run x w (t+j)).rejecting ≠ Class.bot) :
    (run x w (t+k)).rejecting ⇒ₚ derivatives w t k (run x w t).rejecting := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, derivatives, (run_remainder x hx w t).2.1]
    exact implies_refl _
  | succ k ih =>
    have hprev := ih (fun j hj => hactive j (by omega))
    have he : t+(k+1) = (t+k)+1 := by omega
    rw [he, derivatives_snoc]
    apply implies_trans (rejecting_step_preserves _ _ (run_invariant x hx w (t+k)) ?_)
      (U_monotone (D_monotone _ hprev))
    change (run x w ((t+k)+1)).rejecting ≠ Class.bot
    rw [← he]
    exact hactive (k+1) (Nat.le_refl _)

/-- Accepting active obligations have genuine finite good certificates. -/
theorem accepting_active_finite_witness (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hi : Inf (marks x w)) (t : Nat) (ha : (run x w t).rejecting ≠ Class.bot) :
    EventuallyTop w t (run x w t).rejecting :=
  class_cosafety_witness _ (nnfClass_positive (run_remainder x hx w t).1)
    (run_remainder x hx w t).2.2 (accepting_active_obligation x hx w hi t ha)

end
end Tlsf.Dpa
