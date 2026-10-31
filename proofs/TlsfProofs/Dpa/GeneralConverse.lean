import TlsfProofs.Dpa.Converse

/-! # General Π₂ converse: finite alphabet and protected constraints
These are partial bridge lemmas, not a proof of `GeneralPi2Converse`.
The missing eventual protected-constraint lemma is stated in proofs/README.md.
-/
namespace Tlsf.Dpa
open Class Formula
variable {ap : Nat}
noncomputable section
local instance generalConverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

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
Thus retry is irrelevant at every position supplied by the missing lemma. -/
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

/-- The remaining semantic lemma can concern the first extraction pass only;
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

/-- The open general converse follows from exactly the first-pass lemma
recorded in the README. The premise is not asserted here. -/
theorem generalPi2Converse_of_false_passes
    (h : ∀ ap (x : Class ap), NNFClass x → HasTag Pi2 x →
      ∀ w : Word (Fin ap), ¬Holds w 0 x →
        (∀ n, (run x w n).all ≠ Class.bot) →
        ∃ N, ∀ n, N ≤ n → ¬Holds w n (extractPass (rawAll x w n))) :
    GeneralPi2Converse := by
  intro ap x hx hpi w
  exact converse_of_eventually_false_passes hx (h ap x hx hpi w)

/-- A sufficient failed-constraint route to the missing first-pass lemma.
This theorem establishes the reduction, not existence of the constraints. -/
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
