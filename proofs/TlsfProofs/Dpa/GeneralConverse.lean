import TlsfProofs.Dpa.Converse

/-! # General Π₂ converse: finite alphabet and protected constraints
Π₂ induction exposes a false co-safety consequence. Minimal closed-alphabet
descent protects such a consequence at every sufficiently late raw position.
This proves `general_eventually_false_passes` and `general_pi2_converse`.
-/
namespace Tlsf.Dpa
open Class Formula
variable {ap : Nat}
noncomputable section
local instance generalConverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite prefix exposes a semantically false co-safety consequence.
This does not claim that extraction preserves the consequence. -/
def CosafetyFailure (w : Word (Fin ap)) (j : Nat) (x : Class ap) : Prop :=
  ∃ k C, RemainderInvariant C ∧ (derivatives w j k x ⇒ₚ C) ∧ ¬Holds w (j+k) C

theorem derivatives_remainder (h : RemainderInvariant C) (w : Word (Fin ap)) (j n : Nat) :
    RemainderInvariant (derivatives w j n C) := by
  induction n with
  | zero => simpa only [derivatives,h.2.1] using h
  | succ n ih => rw [derivatives_snoc]; exact step_remainder _ ih

/-- A false co-safety consequence persists semantically at every later
derivative, even when it never becomes propositionally false. -/
theorem CosafetyFailure.late (h : CosafetyFailure w j x) :
    ∃ N, ∀ n, N ≤ n → ∃ C, RemainderInvariant C ∧
      (derivatives w j n x ⇒ₚ C) ∧ ¬Holds w (j+n) C := by
  obtain ⟨k,C,hC,hi,hf⟩ := h
  refine ⟨k,fun n hn => ?_⟩
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨derivatives w (j+k) d C,derivatives_remainder hC _ _ _,?_,?_⟩
  · rw [derivatives_add]
    exact derivatives_monotone _ _ _ hi
  · rw [← Nat.add_assoc]
    exact fun hs => hf ((derivatives_holds _ _ _ _).mp hs)

theorem CosafetyFailure.antimono (h : CosafetyFailure w j y) (hi : x ⇒ₚ y) :
    CosafetyFailure w j x := by
  obtain ⟨k,C,hC,himp,hfalse⟩ := h
  exact ⟨k,C,hC,implies_trans (derivatives_monotone _ _ _ hi) himp,hfalse⟩

theorem CosafetyFailure.of_U (h : CosafetyFailure w j (U x)) : CosafetyFailure w j x := by
  simpa only [CosafetyFailure,derivatives_U] using h

theorem CosafetyFailure.to_U (h : CosafetyFailure w j x) : CosafetyFailure w j (U x) := by
  simpa only [CosafetyFailure,derivatives_U] using h

theorem CosafetyFailure.step :
    CosafetyFailure w j x ↔ CosafetyFailure w (j+1) (delta (w j) x) := by
  constructor
  · rintro ⟨k,C,hC,hi,hf⟩
    cases k with
    | zero =>
      refine ⟨0,U (D (w j) C),step_remainder _ hC,?_,?_⟩
      · simpa only [derivatives,delta,U_idempotent] using U_monotone (D_monotone (w j) hi)
      · simp only [Nat.add_zero] at hf ⊢
        intro hs
        apply hf
        apply (derivative C w j).mpr
        simpa only [delta,hC.2.1] using hs
    | succ k =>
      refine ⟨k,C,hC,hi,?_⟩
      simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hf
  · rintro ⟨k,C,hC,hi,hf⟩
    refine ⟨k+1,C,hC,hi,?_⟩
    simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hf

theorem CosafetyFailure.meet_left (h : CosafetyFailure w j x) :
    CosafetyFailure w j (meet x y) :=
  h.antimono (fun _ hs => (Bool.and_eq_true_iff.mp hs).1)

theorem CosafetyFailure.meet_right (h : CosafetyFailure w j y) :
    CosafetyFailure w j (meet x y) :=
  h.antimono (fun _ hs => (Bool.and_eq_true_iff.mp hs).2)

theorem derivatives_join (w : Word (Fin ap)) (j n : Nat) (x y : Class ap) :
    derivatives w j n (join x y) = join (derivatives w j n x) (derivatives w j n y) := by
  induction n generalizing j x y with
  | zero => exact U_join x y
  | succ n ih => simp only [derivatives,delta_join]; exact ih _ _ _

theorem CosafetyFailure.join (hx : CosafetyFailure w j x) (hy : CosafetyFailure w j y) :
    CosafetyFailure w j (join x y) := by
  obtain ⟨N,hN⟩ := hx.late
  obtain ⟨M,hM⟩ := hy.late
  obtain ⟨C,hC,hi,hf⟩ := hN (N+M) (by omega)
  obtain ⟨E,hE,hi',hf'⟩ := hM (N+M) (by omega)
  refine ⟨N+M,Class.join C E,⟨join_nnf hC.1 hE.1,?_,join_tag hC.2.2 hE.2.2⟩,?_,join_false hf hf'⟩
  · rw [U_join,hC.2.1,hE.2.1]
  · rw [derivatives_join]
    intro σ hs
    change (C σ || E σ) = true
    rcases Bool.or_eq_true_iff.mp hs with hs | hs
    · simp [hi σ hs]
    · simp [hi' σ hs]

/-- The failed-clause induction extends to the full Π₂ nesting structure
when its conclusion is semantic co-safety failure, rather than a flush. -/
theorem pi2_cosafety_failure (hpi : Pi2 f) (w : Word (Fin ap)) (j : Nat)
    (hf : ¬Sat none w f j) : CosafetyFailure w j (Class.ofFormula f) := by
  induction hpi generalizing j with
  | @base c hc =>
    refine ⟨0,U (Class.ofFormula c),
      ⟨U_nnfClass ⟨c,cosafety_nnf hc,rfl⟩,U_idempotent _,U_cosafety (formula_cosafety_tag _ hc)⟩,
      implies_refl _,?_⟩
    simpa only [Nat.add_zero,U_holds,ofFormula_holds] using hf
  | @conj f g _ _ ihf ihg =>
    by_cases h : Sat none w f j
    · exact (ihg j (fun hg => hf ⟨trivial,h,hg⟩)).meet_right (x := Class.ofFormula f)
    · exact (ihf j h).meet_left (y := Class.ofFormula g)
  | @disj f g _ _ ihf ihg =>
    exact (ihf j (fun h => hf ⟨trivial,Or.inl h⟩)).join
      (ihg j (fun h => hf ⟨trivial,Or.inr h⟩))
  | @next f _ ih =>
    apply CosafetyFailure.step.mpr
    have he : delta (w j) (Class.ofFormula (.next f)) = U (Class.ofFormula f) := by
      apply Class.ext; intro σ; rfl
    rw [he]
    exact (ih (j+1) (fun h => hf ⟨trivial,Or.inr h⟩)).to_U
  | @global f _ ih =>
    have hex : ∃ k, j ≤ k ∧ ¬Sat none w f k := by
      apply Classical.byContradiction; intro hn
      apply hf; refine ⟨trivial,?_⟩
      intro k hk _
      exact Classical.byContradiction (fun h => hn ⟨k,hk,h⟩)
    obtain ⟨k,hjk,hk⟩ := hex
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hjk
    have hk' : ¬Sat none w f (j+d) := hd ▸ hk
    clear hf hjk hk hd k
    induction d generalizing j with
    | zero =>
      apply CosafetyFailure.of_U
      rw [U_globally]
      exact (ih j hk').to_U.meet_left
    | succ d ihd =>
      apply CosafetyFailure.step.mpr
      rw [delta_globally]
      have ht := ihd (j+1) (by simpa only [Nat.add_assoc,Nat.add_comm 1 d] using hk')
      exact ht.to_U.meet_right
  | @release f g _ _ ihf ihg =>
    have hu : UntilAt none j (fun k => ¬Sat none w f k) (fun k => ¬Sat none w g k) :=
      Classical.byContradiction (fun hn => hf ⟨trivial,hn⟩)
    obtain ⟨k,hjk,hrange,hg,hall⟩ := hu
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hjk
    have hg' : ¬Sat none w g (j+d) := hd ▸ hg
    have hall' : ∀ i, j ≤ i → i < j+d → ¬Sat none w f i := by simpa only [← hd] using hall
    clear hf hjk hg hall hd hrange k
    induction d generalizing j with
    | zero =>
      apply CosafetyFailure.of_U
      rw [U_release]
      exact (ihg j hg').to_U.meet_left
    | succ d ihd =>
      apply CosafetyFailure.step.mpr
      rw [delta_release]
      have ht := ihd (j+1)
        (by simpa only [Nat.add_assoc,Nat.add_comm 1 d] using hg')
        (fun i hi hik => hall' i (by omega) (by omega))
      have hfirst := CosafetyFailure.step.mp (ihf j (hall' j (Nat.le_refl _) (by omega)))
      exact (hfirst.join ht.to_U).meet_right
  | @weakUntil f g _ _ ihf ihg =>
    have hn : ¬(UntilAt none j (Sat none w f) (Sat none w g) ∨ AllFuture none j (Sat none w f)) :=
      fun h => hf ⟨trivial,h⟩
    have hu := (Tlsf.Rewrites.not_weakUntil_dual (len := none) (j := j)
      (p := fun k => ¬Sat none w f k) (q := fun k => ¬Sat none w g k)).mp
      (by simpa only [Classical.not_not] using hn)
    obtain ⟨k,hjk,hrange,hfg,hall⟩ := hu
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hjk
    have hfg' : ¬Sat none w f (j+d) ∧ ¬Sat none w g (j+d) := hd ▸ hfg
    have hall' : ∀ i, j ≤ i → i < j+d → ¬Sat none w g i := by simpa only [← hd] using hall
    clear hf hn hjk hfg hall hd hrange k
    induction d generalizing j with
    | zero =>
      apply CosafetyFailure.of_U
      rw [U_weakUntil]
      exact (ihg j hfg'.2).to_U.join (ihf j hfg'.1).to_U.meet_left
    | succ d ihd =>
      apply CosafetyFailure.step.mpr
      rw [delta_weakUntil]
      have ht := ihd (j+1)
        (by simpa only [Nat.add_assoc,Nat.add_comm 1 d] using hfg')
        (fun i hi hik => hall' i (by omega) (by omega))
      have hg := CosafetyFailure.step.mp (ihg j (hall' j (Nat.le_refl _) (by omega)))
      exact hg.join ht.to_U.meet_right

theorem CosafetyFailure.of_cosafety (hx : NNFClass x) (hc : HasTag cosafety x)
    (hf : ¬Holds w j x) : CosafetyFailure w j x := by
  refine ⟨0,U x,⟨U_nnfClass hx,U_idempotent _,U_cosafety hc⟩,implies_refl _,?_⟩
  simpa only [Nat.add_zero,U_holds] using hf

theorem allJoin_cosafety_failure (xs : List (Class ap))
    (h : ∀ x, x ∈ xs → CosafetyFailure w j x) : CosafetyFailure w j (allJoin xs) := by
  induction xs with
  | nil =>
    exact CosafetyFailure.of_cosafety ⟨.ff,trivial,rfl⟩ (bot_hasTag _)
      (by intro hf; exact Bool.noConfusion hf)
  | cons x xs ih => exact (h x (by simp)).join (ih (fun y hy => h y (by simp [hy])))

/-- Π₂ failure exposes a false co-safety consequence for an arbitrary NNF
Boolean class, not only for a selected syntax representative. -/
theorem class_pi2_cosafety_failure (hx : NNFClass x) (hpi : HasTag Pi2 x)
    (hf : ¬Holds w j x) : CosafetyFailure w j x := by
  apply (allJoin_cosafety_failure ((supportList x).map (badFactor (truthAssignment w j))) ?_).antimono
    (implies_badClause x (nnfClass_positive hx) _ (Bool.eq_false_iff.mpr hf))
  intro y hy
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
  have hu := (mem_supportList x a).mp ha
  have hapi := hpi a hu
  unfold badFactor
  split
  · rename_i hap
    cases a <;> simp only [isAP] at hap
    case ap p =>
      split
      · rename_i hs
        have hfalse : ¬Sat none w (.neg (.ap p)) j := by
          intro hn
          apply hn.2
          simpa only [truthAssignment,decide_eq_true_eq] using hs
        exact pi2_cosafety_failure (.base (by trivial)) w j hfalse
      · rename_i hs
        apply pi2_cosafety_failure hapi w j
        simpa only [truthAssignment,decide_eq_true_eq] using hs
  · split
    · exact CosafetyFailure.of_cosafety ⟨.ff,trivial,rfl⟩ (bot_hasTag _)
        (by intro hf; exact Bool.noConfusion hf)
    · rename_i hs
      apply pi2_cosafety_failure hapi w j
      simpa only [truthAssignment,decide_eq_true_eq] using hs

/-- Every sufficiently late raw position has a false co-safety consequence.
The protection argument is supplied separately by closed-alphabet descent.
No never-false assumption is needed. -/
theorem general_eventually_false_cosafety_constraints
    (hx : NNFClass x) (hpi : HasTag Pi2 x) (hf : ¬Holds w 0 x) :
    ∃ N, ∀ n, N ≤ n → ∃ C, NNFClass C ∧ HasTag cosafety C ∧
      (rawAll x w n ⇒ₚ C) ∧ ¬Holds w n C := by
  obtain ⟨N,hN⟩ := (class_pi2_cosafety_failure hx hpi hf).late
  refine ⟨N+1,fun n hn => ?_⟩
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨C,hC,hi,hfalse⟩ := hN m (by omega)
  refine ⟨D (w m) C,D_nnfClass _ hC.1,D_cosafety _ hC.2.2,?_,?_⟩
  · change D (w m) (run x w m).all ⇒ₚ D (w m) C
    rw [all_field_derivative x hx w m]
    exact D_monotone _ hi
  · intro hs
    apply hfalse
    simp only [Nat.zero_add]
    apply (derivative C w m).mpr
    simpa only [Nat.zero_add,delta,hC.2.1,U_holds] using hs

/-- The full Π₂ failed-clause induction proves eventual falsity before
the X-removal loop. Protection is not needed for this intermediate result. -/
theorem general_eventually_false_reductions
    (hx : NNFClass x) (hpi : HasTag Pi2 x) (hf : ¬Holds w 0 x) :
    ∃ N, ∀ n, N ≤ n → ¬Holds w n (reduce (rawAll x w n)) := by
  obtain ⟨N,hN⟩ := general_eventually_false_cosafety_constraints hx hpi hf
  refine ⟨N,fun n hn hs => ?_⟩
  obtain ⟨C,_,hco,hi,hfalse⟩ := hN n hn
  apply hfalse
  apply implication_sound (elision_preserves_constraint hi _ ?_) hs
  intro a ha hp
  exact hp.2 (hco a ha)

/-- Unfolding exposes only subformulas, including the frozen continuation. -/
theorem unfold_modal_subformula (f : Formula (Fin ap)) (a : Formula (Fin ap))
    (ha : a ∈ modalAtoms (unfoldSyntax f)) : a ∈ subformulas f := by
  induction f with
  | tt | ff => contradiction
  | ap p | next f | strongNext f =>
    exact modalAtom_subformula _ _ ha
  | neg f ih => exact List.mem_cons_of_mem _ (ih ha)
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihf ha))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihg ha))
  | eventually f ih | globally f ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_cons_of_mem _ (ih ha)
    · have he := List.mem_singleton.mp ha; subst a; simp [subformulas]
  | «until» f g ihf ihg | weakUntil f g ihf ihg =>
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihg ha))
    · rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihf ha))
      · have he := List.mem_singleton.mp ha; subst a; simp [subformulas]
  | release f g ihf ihg | strongRelease f g ihf ihg =>
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihg ha))
    · rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihf ha))
      · have he := List.mem_singleton.mp ha; subst a; simp [subformulas]

/-- A raw step either keeps a modal atom or exposes a subformula of X. -/
theorem step_modal_subformula (f : Formula (Fin ap)) (v : Letter (Fin ap))
    (a : Formula (Fin ap)) (ha : a ∈ modalAtoms (stepSyntax v f)) :
    a ∈ subformulas f := by
  induction f with
  | tt | ff => contradiction
  | ap p => cases hv : v p <;> simp_all [stepSyntax, modalAtoms]
  | neg f ih => exact List.mem_cons_of_mem _ (ih ha)
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihf ha))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihg ha))
  | next f | strongNext f =>
    exact List.mem_cons_of_mem _ (modalAtom_subformula f a ha)
  | eventually f | globally f | «until» f g | weakUntil f g | release f g | strongRelease f g =>
    exact modalAtom_subformula _ _ ha

/-- Both fields use one subformula alphabet fixed at the input. -/
def SubformulaBound (f : Formula (Fin ap)) (x : Class ap) : Prop :=
  ∀ a, Uses x a → a ∈ subformulas f

theorem ofFormula_subformulaBound (f : Formula (Fin ap)) :
    SubformulaBound f (Class.ofFormula f) := by
  intro a ha
  apply modalAtom_subformula f a
  exact uses_in_bound (fun σ τ h => propEval_local f σ τ h) ha

theorem U_subformulaBound (h : SubformulaBound f x) : SubformulaBound f (U x) := by
  intro a ha
  obtain ⟨b,hb,hab⟩ := U_uses ha
  have hd : (Class.ofFormula (unfoldSyntax b)).DependsOn (modalAtoms (unfoldSyntax b)) :=
    fun σ τ hh => propEval_local _ _ _ hh
  exact subformula_trans (unfold_modal_subformula b a (uses_in_bound hd hab)) (h b hb)

theorem D_subformulaBound (h : SubformulaBound f x) (v : Letter (Fin ap)) :
    SubformulaBound f (D v x) := by
  intro a ha
  obtain ⟨b,hb,hab⟩ := D_uses v ha
  have hd : (Class.ofFormula (stepSyntax v b)).DependsOn (modalAtoms (stepSyntax v b)) :=
    fun σ τ hh => propEval_local _ _ _ hh
  exact subformula_trans (step_modal_subformula b v a (uses_in_bound hd hab)) (h b hb)

/-- A finite alphabet closed under syntactic subformulas. -/
def ClosedAlphabet (B : List (Formula (Fin ap))) : Prop :=
  ∀ a, a ∈ B → ∀ b, b ∈ subformulas a → b ∈ B

def AlphabetBound (B : List (Formula (Fin ap))) (C : Class ap) : Prop :=
  ∀ a, Uses C a → a ∈ B

def MaximalAtom (B : List (Formula (Fin ap))) (H : Formula (Fin ap)) : Prop :=
  H ∈ B ∧ ∀ a, a ∈ B → H ∈ subformulas a → a = H

def removeAtom (B : List (Formula (Fin ap))) (H : Formula (Fin ap)) :=
  B.filter (fun a => decide (a ≠ H))

theorem removeAtom_shorter (h : H ∈ B) : (removeAtom B H).length < B.length :=
  removeBody_shorter h

theorem removeAtom_closed (h : ClosedAlphabet B) (hm : MaximalAtom B H) :
    ClosedAlphabet (removeAtom B H) := by
  intro a ha b hb
  have ha' := List.mem_filter.mp ha
  apply List.mem_filter.mpr
  refine ⟨h a ha'.1 b hb,decide_eq_true ?_⟩
  intro he
  subst b
  have he' := hm.2 a ha'.1 hb
  exact (of_decide_eq_true ha'.2) he'

theorem subformula_size {a f : Formula (Fin ap)} (h : a ∈ subformulas f) :
    a = f ∨ sizeOf a < sizeOf f := by
  induction f with
  | tt | ff | ap _ => exact Or.inl (List.mem_singleton.mp h)
  | neg f ih | next f ih | strongNext f ih | eventually f ih | globally f ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · right
      rcases ih h with rfl | hs <;> simp_all <;> omega
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg
  | «until» f g ihf ihg | release f g ihf ihg | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · right
      rcases List.mem_append.mp h with h | h
      · rcases ihf h with rfl | hs <;> simp_all <;> omega
      · rcases ihg h with rfl | hs <;> simp_all <;> omega

theorem list_maximum_witness (xs : List α) (p : α → Prop) (rank : α → Nat)
    (hex : ∃ a, a ∈ xs ∧ p a) :
    ∃ a, a ∈ xs ∧ p a ∧ ∀ b, b ∈ xs → p b → rank b ≤ rank a := by
  induction xs with
  | nil => obtain ⟨a,ha,_⟩ := hex; contradiction
  | cons a xs ih =>
    by_cases ht : ∃ b, b ∈ xs ∧ p b
    · obtain ⟨b,hb,hp,hmax⟩ := ih ht
      by_cases ha : p a ∧ rank b ≤ rank a
      · refine ⟨a,by simp,ha.1,?_⟩
        intro c hc hpc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax c hc hpc) ha.2
      · refine ⟨b,by simp [hb],hp,?_⟩
        intro c hc hpc
        rcases List.mem_cons.mp hc with rfl | hc
        · have hh : ¬rank b ≤ rank c := fun h => ha ⟨hpc,h⟩
          omega
        · exact hmax c hc hpc
    · obtain ⟨b,hb,hp⟩ := hex
      have he : b = a := by
        rcases List.mem_cons.mp hb with he | hb
        · exact he
        · exact False.elim (ht ⟨b,hb,hp⟩)
      subst b
      refine ⟨a,by simp,hp,?_⟩
      intro b hb hpb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Nat.le_refl _
      · exact False.elim (ht ⟨b,hb,hpb⟩)

theorem maximal_superformula (ha : a ∈ B) :
    ∃ H, MaximalAtom B H ∧ a ∈ subformulas H := by
  have hrefl : a ∈ subformulas a := by cases a <;> simp [subformulas]
  obtain ⟨H,hH,haH,hmax⟩ := list_maximum_witness B (fun f => a ∈ subformulas f) sizeOf ⟨a,ha,hrefl⟩
  refine ⟨H,⟨hH,?_⟩,haH⟩
  intro f hf hHf
  have hle := hmax f hf (subformula_trans haH hHf)
  rcases subformula_size hHf with he | hlt
  · exact he.symm
  · omega

theorem U_alphabetBound (hB : ClosedAlphabet B) (h : AlphabetBound B C) :
    AlphabetBound B (U C) := by
  intro a ha
  obtain ⟨b,hb,hab⟩ := U_uses ha
  exact hB b (h b hb) a (unfold_modal_subformula b a
    (uses_in_bound (fun σ τ hh => propEval_local _ σ τ hh) hab))

theorem D_alphabetBound (hB : ClosedAlphabet B) (h : AlphabetBound B C) (v : Letter (Fin ap)) :
    AlphabetBound B (D v C) := by
  intro a ha
  obtain ⟨b,hb,hab⟩ := D_uses v ha
  exact hB b (h b hb) a (step_modal_subformula b v a
    (uses_in_bound (fun σ τ hh => propEval_local _ σ τ hh) hab))

theorem falseCofactor_uses (h : Uses (falseCofactor C H) a) : Uses C a ∧ a ≠ H := by
  obtain ⟨σ,b,hb⟩ := h
  have hne : a ≠ H := by
    intro he; subst a
    apply hb
    apply congrArg C
    funext t
    by_cases ht : t = H <;> simp [setAtom,ht]
  refine ⟨⟨setAtom σ H false,b,?_⟩,hne⟩
  have he : setAtom (setAtom σ a b) H false = setAtom (setAtom σ H false) a b := by
    funext t
    by_cases ht : t = H <;> by_cases ht' : t = a <;> simp_all [setAtom]
  change C (setAtom (setAtom σ a b) H false) ≠ C (setAtom σ H false) at hb
  rwa [he] at hb

theorem falseCofactor_nnf (H f : Formula (Fin ap)) (hf : NNF f) :
    NNF (falseCofactorSyntax H f) := by
  induction f with
  | tt | ff => trivial
  | ap a => simp only [falseCofactorSyntax]; split <;> trivial
  | neg f ih =>
    cases f <;> simp only [NNF] at hf
    case tt => trivial
    case ff => trivial
    case ap a => simp only [falseCofactorSyntax]; split <;> trivial
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf hf.1,ihg hf.2⟩
  | next f | eventually f | globally f | «until» f g | release f g
  | weakUntil f g | strongRelease f g =>
    simp only [falseCofactorSyntax]; split
    · trivial
    · exact hf
  | _ => contradiction

theorem falseCofactor_nnfClass (h : NNFClass C) (H : Formula (Fin ap)) :
    NNFClass (falseCofactor C H) := by
  obtain ⟨f,hf,rfl⟩ := h
  refine ⟨falseCofactorSyntax H f,falseCofactor_nnf H f hf,?_⟩
  apply Class.ext; intro σ
  exact falseCofactor_eval H f σ

theorem falseCofactor_implies (h : NNFClass C) (hH : ¬isAP H) : falseCofactor C H ⇒ₚ C := by
  intro σ hs
  apply nnfClass_positive h (setAtom σ H false) σ _ _ hs
  · intro a ha
    have hne : a ≠ H := fun he => hH (he ▸ ha)
    simp [setAtom,hne]
  · intro a _ ha
    by_cases he : a = H
    · subst a; simp [setAtom] at ha
    · simpa [setAtom,he] using ha

/-- A false co-safety consequence together with a finite, closed alphabet.
The alphabet, rather than a finite time window, is the descent measure. -/
structure BadCosafetyConstraint (x : Class ap) (w : Word (Fin ap))
    (B : List (Formula (Fin ap))) (n : Nat) (C : Class ap) : Prop where
  closed : ClosedAlphabet B
  nnf : NNFClass C
  cosafe : HasTag cosafety C
  bound : AlphabetBound B C
  consequence : rawAll x w n ⇒ₚ C
  falsity : ¬Holds w n C

theorem BadCosafetyConstraint.step (hx : NNFClass x) (h : BadCosafetyConstraint x w B n C) :
    BadCosafetyConstraint x w B (n+1) (D (w n) (U C)) := by
  refine ⟨h.closed,D_nnfClass _ (U_nnfClass h.nnf),D_cosafety _ (U_cosafety h.cosafe),
    D_alphabetBound h.closed (U_alphabetBound h.closed h.bound) _,?_,?_⟩
  · change D (w n) (run x w n).all ⇒ₚ _
    rw [← U_rawAll hx w n]
    exact D_monotone _ (U_monotone h.consequence)
  · intro hs
    apply h.falsity
    apply (derivative C w n).mpr
    exact (U_holds _).mpr hs

/-- A raw derivative stays below an original supported atom, and stepping
a top-level X strictly descends below that X. -/
theorem DU_uses_origin (v : Letter (Fin ap)) (h : Uses (D v (U C)) t) :
    ∃ a, Uses C a ∧ t ∈ subformulas a ∧ (isX a → t ≠ a) := by
  obtain ⟨b,hb,htb⟩ := D_uses v h
  obtain ⟨a,ha,hba⟩ := U_uses hb
  have hmem₁ : b ∈ modalAtoms (unfoldSyntax a) :=
    uses_in_bound (fun σ τ hh => propEval_local _ σ τ hh) hba
  have hmem₂ : t ∈ modalAtoms (stepSyntax v b) :=
    uses_in_bound (fun σ τ hh => propEval_local _ σ τ hh) htb
  refine ⟨a,ha,subformula_trans (step_modal_subformula b v t hmem₂)
    (unfold_modal_subformula a b hmem₁),?_⟩
  intro hx
  cases a <;> simp only [isX] at hx
  case next f =>
    have he : b = .next f := List.mem_singleton.mp hmem₁
    subst b
    have ht : t ∈ subformulas f := modalAtom_subformula f t hmem₂
    have hle : sizeOf t ≤ sizeOf f := (subformula_size ht).elim
      (fun he => Nat.le_of_eq (congrArg sizeOf he)) Nat.le_of_lt
    intro he
    subst t
    simp at hle
    omega

theorem BadCosafetyConstraint.step_remove_maximal_X (hx : NNFClass x)
    (h : BadCosafetyConstraint x w B n C) (hm : MaximalAtom B H) (hX : isX H) :
    BadCosafetyConstraint x w (removeAtom B H) (n+1) (D (w n) (U C)) := by
  have hs := h.step hx
  refine { hs with closed := removeAtom_closed h.closed hm, bound := ?_ }
  intro t ht
  apply List.mem_filter.mpr
  refine ⟨hs.bound t ht,decide_eq_true ?_⟩
  intro he
  subst t
  obtain ⟨a,ha,hHa,hstrict⟩ := DU_uses_origin (w n) ht
  have he := hm.2 a (h.bound a ha) hHa
  subst a
  exact hstrict hX rfl

/-- Minimality ranges over all times and all false co-safety consequences.
It therefore rules out an unprotected maximal X by one exact raw step. -/
theorem minimal_alphabet_no_maximal_X (hx : NNFClass x)
    (h : BadCosafetyConstraint x w B n C)
    (hmin : ∀ B' j E, BadCosafetyConstraint x w B' j E → B.length ≤ B'.length)
    (hm : MaximalAtom B H) : ¬isX H := by
  intro hX
  have hle := hmin _ _ _ (h.step_remove_maximal_X hx hm hX)
  have hlt := removeAtom_shorter hm.1
  omega

/-- A missing maximal non-AP atom could be removed from the finite closed
alphabet by the false-cofactor argument, contradicting minimality. -/
theorem minimal_alphabet_protector (h : BadCosafetyConstraint x w B n C)
    (hmin : ∀ B' j E, BadCosafetyConstraint x w B' j E → B.length ≤ B'.length)
    (hm : MaximalAtom B H) (hH : ¬isAP H)
    (hxy : rawAll x w n ⇒ₚ y) (hyC : y ⇒ₚ C) : Uses y H := by
  apply Classical.byContradiction
  intro habs
  have hsmall : BadCosafetyConstraint x w (removeAtom B H) n (falseCofactor C H) := by
    refine ⟨removeAtom_closed h.closed hm,falseCofactor_nnfClass h.nnf H,
      fun a ha => h.cosafe a (falseCofactor_uses ha).1,?_,
      losing_protector hxy hyC habs,?_⟩
    · intro a ha
      have hh := falseCofactor_uses ha
      exact List.mem_filter.mpr ⟨h.bound a hh.1,decide_eq_true hh.2⟩
    · exact fun hs => h.falsity (implication_sound (falseCofactor_implies h.nnf hH) hs)
  have hle := hmin _ _ _ hsmall
  have hlt := removeAtom_shorter hm.1
  omega

theorem minimal_alphabet_maximal_used (h : BadCosafetyConstraint x w B n C)
    (hmin : ∀ B' j E, BadCosafetyConstraint x w B' j E → B.length ≤ B'.length)
    (hm : MaximalAtom B H) : Uses C H := by
  apply Classical.byContradiction
  intro habs
  have hsmall : BadCosafetyConstraint x w (removeAtom B H) n C := by
    refine { h with closed := removeAtom_closed h.closed hm, bound := ?_ }
    intro a ha
    apply List.mem_filter.mpr
    refine ⟨h.bound a ha,decide_eq_true ?_⟩
    intro he; subst a; exact habs ha
  have hle := hmin _ _ _ hsmall
  have hlt := removeAtom_shorter hm.1
  omega

theorem cosafety_supported_shape (hc : HasTag cosafety C) (hu : Uses C a) :
    isAP a ∨ isX a ∨ nonXModal a := by
  have ha : a ∈ modalAtoms C.repr := uses_in_bound (fun σ τ hh => by
    rw [← repr_eval C σ,← repr_eval C τ]
    exact propEval_local _ σ τ hh) hu
  have hco := hc a hu
  generalize C.repr = f at ha
  clear hu hc C
  induction f with
  | tt | ff => contradiction
  | ap p | next f | strongNext f | eventually f | globally f
  | «until» f g | release f g | weakUntil f g | strongRelease f g =>
    have he := List.mem_singleton.mp ha
    subst a
    simp_all [isAP,isX,nonXModal,cosafety]
  | neg f ih => exact ih ha
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    exact (List.mem_append.mp ha).elim ihf ihg

theorem replaceTrue_subformulaBound (h : SubformulaBound f x) (p : Formula (Fin ap) → Prop) :
    SubformulaBound f (replaceTrue p x) := fun a ha => h a (replaceTrue_uses ha).1

theorem elideFuel_subformulaBound (h : SubformulaBound f x) (n : Nat) :
    SubformulaBound f (elideFuel n x) := by
  induction n generalizing x with
  | zero => exact h
  | succ n ih =>
    simp only [elideFuel]
    split
    · exact h
    · exact ih (replaceTrue_subformulaBound h _)

theorem extractPass_subformulaBound (h : SubformulaBound f x) :
    SubformulaBound f (extractPass x) :=
  U_subformulaBound (elideFuel_subformulaBound (replaceTrue_subformulaBound h _) _)

theorem rho_subformulaBound (h : SubformulaBound f x) : SubformulaBound f (rho x) := by
  unfold rho
  split
  · exact extractPass_subformulaBound (U_subformulaBound h)
  · exact extractPass_subformulaBound h

theorem bot_subformulaBound (f : Formula (Fin ap)) : SubformulaBound f Class.bot := by
  intro a ha
  obtain ⟨σ,b,hb⟩ := ha
  exact False.elim (hb rfl)

theorem meet_subformulaBound (hx : SubformulaBound f x) (hy : SubformulaBound f y) :
    SubformulaBound f (meet x y) := fun a ha => (meet_uses ha).elim (hx a) (hy a)

theorem initial_subformulaBound (h : SubformulaBound f x) :
    SubformulaBound f (initial x).all ∧ SubformulaBound f (initial x).rejecting := by
  unfold initial
  split
  · exact ⟨U_subformulaBound h,bot_subformulaBound f⟩
  · exact ⟨U_subformulaBound h,rho_subformulaBound h⟩

/-- Covers the false renewal row too; no reachability invariant is required. -/
theorem transition_subformulaBound (v : Letter (Fin ap)) (s : Pair ap)
    (ha : SubformulaBound f s.all) (hr : SubformulaBound f s.rejecting) :
    SubformulaBound f (transition v s).target.all ∧
      SubformulaBound f (transition v s).target.rejecting := by
  have hn := U_subformulaBound (D_subformulaBound ha v)
  have hR := U_subformulaBound (D_subformulaBound hr v)
  have hseed := rho_subformulaBound (D_subformulaBound ha v)
  have hb := bot_subformulaBound f
  have ht : SubformulaBound f Class.top := by
    intro a ha; obtain ⟨σ,b,hb⟩ := ha; exact False.elim (hb rfl)
  simp only [transition]
  split
  · exact ⟨hb,hb⟩
  · split
    · exact ⟨ht,hb⟩
    · split
      · exact ⟨hn,hb⟩
      · split
        · exact ⟨hn,hb⟩
        · split
          · exact ⟨hn,hseed⟩
          · split
            · split
              · exact ⟨hb,hb⟩
              · exact ⟨hn,meet_subformulaBound hR hseed⟩
            · exact ⟨hn,hR⟩

/-- A single finite alphabet contains every supported atom of both fields,
including every retained finite remainder and every extraction retry. -/
theorem run_subformulaBound (f : Formula (Fin ap)) (w : Word (Fin ap)) (n : Nat) :
    SubformulaBound f (run (Class.ofFormula f) w n).all ∧
      SubformulaBound f (run (Class.ofFormula f) w n).rejecting := by
  induction n with
  | zero => exact initial_subformulaBound (ofFormula_subformulaBound f)
  | succ n ih => exact transition_subformulaBound (w n) _ ih.1 ih.2

/-- A co-safety consequence whose X atoms remain protected at every possible
NNF weakening between the raw class and this consequence. -/
def ProtectedConstraint (x C : Class ap) : Prop :=
  HasTag cosafety C ∧ (x ⇒ₚ C) ∧
    ∀ y, NNFClass y → (x ⇒ₚ y) → (y ⇒ₚ C) →
      ∀ a, Uses C a → isX a → Protected y a

/-- In a smallest closed alphabet every X lies below a maximal non-X modal
atom, and that atom survives every intermediate weakening. -/
theorem minimal_alphabet_protected_constraint (hx : NNFClass x)
    (h : BadCosafetyConstraint x w B n C)
    (hmin : ∀ B' j E, BadCosafetyConstraint x w B' j E → B.length ≤ B'.length) :
    ProtectedConstraint (rawAll x w n) C := by
  refine ⟨h.cosafe,h.consequence,?_⟩
  intro y _ hxy hyC a ha hX
  obtain ⟨H,hm,haH⟩ := maximal_superformula (h.bound a ha)
  have hu := minimal_alphabet_maximal_used h hmin hm
  rcases cosafety_supported_shape h.cosafe hu with hap | hXX | hmodal
  · cases H <;> simp only [isAP] at hap
    case ap p =>
      have he := List.mem_singleton.mp haH
      subst a
      exact False.elim hX
  · exact False.elim (minimal_alphabet_no_maximal_X hx h hmin hm hXX)
  · have hnAP : ¬isAP H := by cases H <;> simp_all [nonXModal,isAP]
    exact ⟨H,minimal_alphabet_protector h hmin hm hnAP hxy hyC,hmodal,haH⟩

theorem BadCosafetyConstraint.later (hx : NNFClass x)
    (h : BadCosafetyConstraint x w B n C) (hnm : n ≤ m) :
    ∃ E, BadCosafetyConstraint x w B m E := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => exact ⟨C,h⟩
  | succ k ih =>
    obtain ⟨E,hE⟩ := ih
    exact ⟨_,hE.step hx⟩

/-- Minimal closed-alphabet descent upgrades any false co-safety raw
consequence to false protected consequences at all sufficiently late times.
No propositional flushing, recurrence assumption or acceptance is used. -/
theorem eventually_protected_of_cosafety_constraint (hx : NNFClass x)
    (hC : NNFClass C) (hc : HasTag cosafety C)
    (hi : rawAll x w t ⇒ₚ C) (hf : ¬Holds w t C) :
    ∃ N, ∀ n, N ≤ n → ∃ E,
      ProtectedConstraint (rawAll x w n) E ∧ ¬Holds w n E := by
  have hB : BadCosafetyConstraint x w (subformulas C.repr) t C := by
    refine ⟨fun a ha b hb => subformula_trans hb ha,hC,hc,?_,hi,hf⟩
    intro a ha
    apply modalAtom_subformula C.repr a
    apply uses_in_bound _ ha
    intro σ τ hh
    rw [← repr_eval C σ,← repr_eval C τ]
    exact propEval_local _ _ _ hh
  have hex : ∃ k, ∃ B n E, B.length = k ∧ BadCosafetyConstraint x w B n E :=
    ⟨(subformulas C.repr).length,_,t,C,rfl,hB⟩
  obtain ⟨k,⟨B,N,E,hk,h⟩,hmin⟩ := exists_least_nat hex
  have minimal : ∀ B' j F, BadCosafetyConstraint x w B' j F → B.length ≤ B'.length := by
    intro B' j F hF
    apply Nat.le_of_not_gt
    intro hlt
    exact hmin B'.length (by omega) ⟨B',j,F,rfl,hF⟩
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨F,hF⟩ := h.later hx hn
  exact ⟨F,minimal_alphabet_protected_constraint hx hF minimal,hF.falsity⟩

/-- The full Π₂ induction and finite alphabet descent supply the previously
missing false protected constraints, including all late raw positions. -/
theorem general_eventually_false_protected_constraints
    (hx : NNFClass x) (hpi : HasTag Pi2 x) (hf : ¬Holds w 0 x) :
    ∃ N, ∀ n, N ≤ n → ∃ C,
      ProtectedConstraint (rawAll x w n) C ∧ ¬Holds w n C := by
  obtain ⟨N,hN⟩ := general_eventually_false_cosafety_constraints hx hpi hf
  obtain ⟨C,hC,hco,hi,hfalse⟩ := hN N (Nat.le_refl _)
  exact eventually_protected_of_cosafety_constraint hx hC hco hi hfalse

/-- The flat proof's elision argument does not require finite bodies once
protection of the constraint has been established. -/
theorem extractPass_protected_constraint (hx : NNFClass x)
    (hC : ProtectedConstraint x C) : extractPass x ⇒ₚ U C := by
  have hr : reduce x ⇒ₚ C := by
    apply elision_preserves_constraint hC.2.1
    intro a ha hp
    exact hp.2 (hC.1 a ha)
  have hw : x ⇒ₚ reduce x := replaceTrue_weakens (nnfClass_positive hx) _ (by
    intro a ha hp; exact hp.1 ha)
  have loop : ∀ n y, NNFClass y → (x ⇒ₚ y) → (y ⇒ₚ C) → elideFuel n y ⇒ₚ C := by
    intro n; induction n with
    | zero => intro y _ _ hy; exact hy
    | succ n ih =>
      intro y hyn hxy hy
      have hd : dropX y ⇒ₚ C := by
        apply elision_preserves_constraint hy
        intro a ha hp
        exact hp.2 (hC.2.2 y hyn hxy hy a ha hp.1)
      have hw : y ⇒ₚ dropX y := replaceTrue_weakens (nnfClass_positive hyn) _ (by
        intro a ha hp; cases a <;> simp_all [isAP,isX])
      simp only [elideFuel]
      split
      · exact hy
      · exact ih _ (replaceTrue_nnfClass _ hyn) (implies_trans hxy hw) hd
  exact U_monotone (loop _ _ (replaceTrue_nnfClass _ hx) hw hr)

/-- A false first pass cannot be finite if the all-field never reaches false.
Thus retry is irrelevant at every position supplied by the first-pass lemma. -/
theorem false_pass_disables_retry (hx : NNFClass x)
    (hnever : ∀ n, (run x w n).all ≠ Class.bot)
    (hp : ¬Holds w n (extractPass (rawAll x w n))) :
    rho (rawAll x w n) = extractPass (rawAll x w n) := by
  have hn : ¬HasTag finite (extractPass (rawAll x w n)) := by
    intro hf
    apply hp
    apply neverBot_finite_obligation hx hnever (extractPass_nnf (rawAll_nnf hx w n)) hf
    rw [← U_rawAll hx w n]
    exact extractPass_weakens (rawAll_nnf hx w n)
  simp only [rho,hn,false_and,↓reduceIte]

/-- A converse reduction that concerns the first extraction pass only;
finite retention and the actual retry are handled by the existing invariants. -/
theorem converse_of_eventually_false_passes (hx : NNFClass x)
    (hpasses : ¬Holds w 0 x → (∀ n, (run x w n).all ≠ Class.bot) →
      ∃ N, ∀ n, N ≤ n → ¬Holds w n (extractPass (rawAll x w n))) :
    Inf (marks x w) → Holds w 0 x := by
  apply converse_of_eventually_false_seeds x hx w
  intro hf hn
  obtain ⟨N,hN⟩ := hpasses hf hn
  refine ⟨N,fun n hge => ?_⟩
  rw [false_pass_disables_retry hx hn (hN n hge)]
  exact hN n hge

/-- The general converse follows from the first-pass lemma, with retry
and finite retention handled by the existing component invariants. -/
theorem generalPi2Converse_of_false_passes
    (h : ∀ ap (x : Class ap), NNFClass x → HasTag Pi2 x →
      ∀ w : Word (Fin ap), ¬Holds w 0 x →
        (∀ n, (run x w n).all ≠ Class.bot) →
        ∃ N, ∀ n, N ≤ n → ¬Holds w n (extractPass (rawAll x w n))) :
    GeneralPi2Converse := by
  intro ap x hx hpi w
  exact converse_of_eventually_false_passes hx (h ap x hx hpi w)

/-- False protected constraints imply false first extraction passes. -/
theorem false_passes_of_protected_constraints (hx : NNFClass x)
    (hconstraints : ∃ N, ∀ n, N ≤ n → ∃ C,
      ProtectedConstraint (rawAll x w n) C ∧ ¬Holds w n C) :
    ∃ N, ∀ n, N ≤ n → ¬Holds w n (extractPass (rawAll x w n)) := by
  obtain ⟨N,hN⟩ := hconstraints
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨C,hC,hfalse⟩ := hN n hn
  intro ht
  have hh := implication_sound (extractPass_protected_constraint (rawAll_nnf hx w n) hC) ht
  exact hfalse ((U_holds C).mp hh)

/-- The first extraction pass is eventually false for every violated Π₂
class. This stronger statement does not require a never-false all-field. -/
theorem general_eventually_false_passes (x : Class ap) (hx : NNFClass x)
    (hpi : HasTag Pi2 x) (w : Word (Fin ap)) (hfalse : ¬Holds w 0 x) :
    ∃ N, ∀ n, N ≤ n → ¬Holds w n (extractPass (rawAll x w n)) :=
  false_passes_of_protected_constraints hx
    (general_eventually_false_protected_constraints hx hpi hfalse)

/-- General Π₂ converse for the semantic component model, including its
actual retry and retained finite remainders. -/
theorem general_pi2_converse : GeneralPi2Converse := by
  apply generalPi2Converse_of_false_passes
  intro ap x hx hpi w hf _
  exact general_eventually_false_passes x hx hpi w hf

theorem general_pi2_language (x : Class ap) (hx : NNFClass x) (hpi : HasTag Pi2 x)
    (w : Word (Fin ap)) : Inf (marks x w) ↔ Holds w 0 x :=
  ⟨general_pi2_converse ap x hx hpi w,satisfying_accepts x hx w⟩

/-- All assignments to a finite alphabet, with a fixed value elsewhere. -/
def alphabetAssignments : List (Formula (Fin ap)) → List (Assignment ap)
  | [] => [fun _ => false]
  | a :: atoms => (alphabetAssignments atoms).flatMap
      (fun σ => [setAtom σ a false, setAtom σ a true])

theorem alphabetAssignments_complete (atoms : List (Formula (Fin ap))) (σ : Assignment ap) :
    ∃ τ, τ ∈ alphabetAssignments atoms ∧ ∀ a, a ∈ atoms → τ a = σ a := by
  induction atoms with
  | nil => exact ⟨fun _ => false,by simp [alphabetAssignments],by simp⟩
  | cons a atoms ih =>
    obtain ⟨τ,hτ,he⟩ := ih
    refine ⟨setAtom τ a (σ a), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨τ,hτ,?_⟩
      cases h : σ a <;> simp
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [setAtom]
      · by_cases hba : b = a
        · subst b; simp [setAtom]
        · simp [setAtom,hba,he b hb]

def classSignature (atoms : List (Formula (Fin ap))) (x : Class ap) : List Bool :=
  (alphabetAssignments atoms).map (fun σ => x σ)

theorem map_values_eq (xs : List α) (f g : α → Bool) (h : xs.map f = xs.map g) :
    ∀ a, a ∈ xs → f a = g a := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    have he := List.cons.inj h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he.1
    · exact ih he.2 a ha

/-- A finite truth table determines a supported semantic class exactly. -/
theorem subformula_signature_injective (hx : SubformulaBound f x) (hy : SubformulaBound f y)
    (he : classSignature (subformulas f) x = classSignature (subformulas f) y) : x = y := by
  apply Class.ext
  intro σ
  obtain ⟨τ,hτ,heval⟩ := alphabetAssignments_complete (subformulas f) σ
  have hxy := map_values_eq _ _ _ he τ hτ
  have hxτ : x σ = x τ := support_locality x σ τ (fun a ha => (heval a (hx a ha)).symm)
  have hyτ : y σ = y τ := support_locality y σ τ (fun a ha => (heval a (hy a ha)).symm)
  exact hxτ.trans (hxy.trans hyτ.symm)

def booleanLists : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (booleanLists n).flatMap (fun bs => [false :: bs, true :: bs])

theorem mem_booleanLists (bs : List Bool) : bs ∈ booleanLists bs.length := by
  induction bs with
  | nil => simp [booleanLists]
  | cons b bs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨bs,ih,?_⟩
    cases b <;> simp

/-- One finite list contains every class supported on the input alphabet.
This is a semantic existence theorem, not an allocation bound for C. -/
theorem finite_subformula_classes (f : Formula (Fin ap)) :
    ∃ classes : List (Class ap), ∀ x, SubformulaBound f x → x ∈ classes := by
  let representative (bs : List Bool) : Class ap :=
    if h : ∃ x, SubformulaBound f x ∧ classSignature (subformulas f) x = bs
    then Classical.choose h else Class.bot
  refine ⟨(booleanLists (alphabetAssignments (subformulas f)).length).map representative, ?_⟩
  intro x hx
  let bs := classSignature (subformulas f) x
  have hb : bs ∈ booleanLists (alphabetAssignments (subformulas f)).length := by
    have hh := mem_booleanLists bs
    simpa only [bs,classSignature,List.length_map] using hh
  have hrep : representative bs = x := by
    have hex : ∃ y, SubformulaBound f y ∧ classSignature (subformulas f) y = bs := ⟨x,hx,rfl⟩
    have hs := Classical.choose_spec hex
    have he : representative bs = Classical.choose hex := by simp only [representative,dite_eq_left hex]
    rw [he]
    exact subformula_signature_injective hs.1 hx hs.2
  exact List.mem_map.mpr ⟨bs,hb,hrep⟩

/-- All words and all times share one finite set of reachable component
pairs. Retained obligations and repeated elision create no new alphabet. -/
theorem finite_reachable_pairs (f : Formula (Fin ap)) :
    ∃ states : List (Pair ap), ∀ w n, run (Class.ofFormula f) w n ∈ states := by
  obtain ⟨classes,hclasses⟩ := finite_subformula_classes f
  refine ⟨classes.flatMap (fun a => classes.map (fun r => Pair.mk a r)), ?_⟩
  intro w n
  have h := run_subformulaBound f w n
  apply List.mem_flatMap.mpr
  refine ⟨(run (Class.ofFormula f) w n).all,hclasses _ h.1,?_⟩
  exact List.mem_map.mpr ⟨(run (Class.ofFormula f) w n).rejecting,hclasses _ h.2,rfl⟩

/-- The finite-state result also applies to an arbitrary initial class,
independently of its chosen finite representative. -/
theorem finite_component_states (x : Class ap) :
    ∃ states : List (Pair ap), ∀ w n, run x w n ∈ states := by
  have he : Class.ofFormula x.repr = x := Class.ext (repr_eval x)
  obtain ⟨states,hstates⟩ := finite_reachable_pairs x.repr
  refine ⟨states,fun w n => ?_⟩
  simpa only [he] using hstates w n

/-- The flat finite-window flush cannot be extended to all false co-safety
candidates: F a on the empty word remains a nonconstant class forever.
This is an obstruction to that proof step, not a component counterexample. -/
theorem false_cosafety_need_not_flush :
    ∃ (f : Formula (Fin 1)) (w : Word (Fin 1)),
      cosafety f ∧ ¬Sat none w f 0 ∧
        ∀ n, derivatives w 0 n (Class.ofFormula f) ≠ Class.bot := by
  let w : Word (Fin 1) := fun _ _ => false
  let c : Class 1 := Class.ofFormula (.eventually (.ap 0))
  have hstep (j : Nat) : U (D (w j) (U c)) = U c := by
    apply Class.ext
    intro σ
    change (false || (propEval σ (.ap 0) || σ (.eventually (.ap 0)))) =
      (propEval σ (.ap 0) || σ (.eventually (.ap 0)))
    simp
  have hd (n : Nat) : derivatives w 0 n c = U c := by
    induction n with
    | zero => rfl
    | succ n ih => rw [derivatives_snoc,ih,hstep n]
  refine ⟨.eventually (.ap 0),w,by trivial,?_,?_⟩
  · simp [Sat,w]
  · intro n he
    change derivatives w 0 n c = Class.bot at he
    rw [hd] at he
    have hh := congrArg (fun x : Class 1 => x (fun _ => true)) he
    change (true || true) = false at hh
    contradiction

end
end Tlsf.Dpa
