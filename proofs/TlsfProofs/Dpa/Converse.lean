import TlsfProofs.Dpa.Zielonka

/-! # STAGE2 §§1,6,8–9: grammars and the failed-clause argument.
The failed-clause lemma below is §6.1. It does not assert §6.4's eventual
false-seed result or the targeted component converse.
-/
namespace Tlsf.Dpa
open Class Formula
variable {ap : Nat}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

inductive FlatQ : Formula α → Prop where
  | window (h : finite b) : FlatQ b
  | eventual (h : finite b) : FlatQ (.eventually b)
  | conj (h : FlatQ q) (h' : FlatQ r) : FlatQ (.conj q r)
  | disj (h : FlatQ q) (h' : FlatQ r) : FlatQ (.disj q r)

inductive FlatR : Formula α → Prop where
  | window (h : finite b) : FlatR b
  | global (h : finite b) : FlatR (.globally b)
  | conj (h : FlatR q) (h' : FlatR r) : FlatR (.conj q r)
  | disj (h : FlatR q) (h' : FlatR r) : FlatR (.disj q r)

/-- The syntactic grammar in STAGE2 §8, rather than an admission theorem. -/
inductive Admitted : Formula α → Prop where
  | safety (h : Tlsf.Dpa.safety s) : Admitted s
  | cosafety (h : Tlsf.Dpa.cosafety c) : Admitted c
  | global (h : FlatQ q) : Admitted (.globally q)
  | eventual (h : FlatR r) : Admitted (.eventually r)
  | conj (h : Admitted f) (h' : Admitted g) : Admitted (.conj f g)
  | disj (h : Admitted f) (h' : Admitted g) : Admitted (.disj f g)

inductive Pi2 : Formula α → Prop where
  | base (h : cosafety c) : Pi2 c
  | conj (h : Pi2 f) (h' : Pi2 g) : Pi2 (.conj f g)
  | disj (h : Pi2 f) (h' : Pi2 g) : Pi2 (.disj f g)
  | next (h : Pi2 f) : Pi2 (.next f)
  | global (h : Pi2 f) : Pi2 (.globally f)
  | release (h : Pi2 f) (h' : Pi2 g) : Pi2 (.release f g)
  | weakUntil (h : Pi2 f) (h' : Pi2 g) : Pi2 (.weakUntil f g)

/-- The open core of issue #80 for the DESIGN §1 variant: the converse
inclusion for every syntactic Π₂ component, with no support resets, external
suspension or lookahead. This proposition is not used as a proved theorem. -/
def GeneralPi2Converse : Prop :=
  ∀ ap (x : Class ap), NNFClass x → HasTag Pi2 x →
    ∀ w : Word (Fin ap), Inf (marks x w) → Holds w 0 x

def ClauseLeaf (f : Formula α) : Prop := finite f ∨ ∃ b, finite b ∧ f = .eventually b

theorem allJoin_append (xs ys : List (Class ap)) : allJoin (xs ++ ys) = join (allJoin xs) (allJoin ys) := by
  induction xs with
  | nil => apply Class.ext; intro σ; rfl
  | cons x xs ih =>
    simp only [List.cons_append, allJoin, ih]
    apply Class.ext; intro σ
    exact (Bool.or_assoc ..).symm

/-- STAGE2 §6.1: a false positive Boolean formula has one false clause
consequence. No CNF rewrite is performed by the automaton. -/
theorem failed_clause (q : Formula (Fin ap)) (hq : FlatQ q) (w : Word (Fin ap)) (t : Nat)
    (hfalse : ¬Sat none w q t) :
    ∃ leaves : List (Formula (Fin ap)),
      (∀ f, f ∈ leaves → ClauseLeaf f) ∧
      (Class.ofFormula q ⇒ₚ allJoin (leaves.map Class.ofFormula)) ∧
      (∀ f, f ∈ leaves → ¬Sat none w f t) := by
  induction hq with
  | @window b hb =>
    refine ⟨[b], ?_, ?_, ?_⟩
    · intro f hf; have he := List.mem_singleton.mp hf; subst f; exact Or.inl hb
    · intro σ h
      change (propEval σ b || false) = true
      change propEval σ b = true at h
      simpa using h
    · intro f hf; have he := List.mem_singleton.mp hf; subst f; exact hfalse
  | @eventual b hb =>
    refine ⟨[.eventually b], ?_, ?_, ?_⟩
    · intro f hf; have he := List.mem_singleton.mp hf; subst f; exact Or.inr ⟨b, hb, rfl⟩
    · intro σ h
      change (σ (.eventually b) || false) = true
      change σ (.eventually b) = true at h
      simpa using h
    · intro f hf; have he := List.mem_singleton.mp hf; subst f; exact hfalse
  | @conj q r hq hr ihq ihr =>
    by_cases hqtrue : Sat none w q t
    · have hrfalse : ¬Sat none w r t := fun h => hfalse ⟨trivial, hqtrue, h⟩
      obtain ⟨ls, hl, hi, hf⟩ := ihr hrfalse
      refine ⟨ls, hl, ?_, hf⟩
      intro σ h
      change (propEval σ q && propEval σ r) = true at h
      simp only [Bool.and_eq_true] at h
      exact hi σ h.2
    · obtain ⟨ls, hl, hi, hf⟩ := ihq hqtrue
      refine ⟨ls, hl, ?_, hf⟩
      intro σ h
      change (propEval σ q && propEval σ r) = true at h
      simp only [Bool.and_eq_true] at h
      exact hi σ h.1
  | @disj q r hq hr ihq ihr =>
    have hqfalse : ¬Sat none w q t := fun h => hfalse ⟨trivial, Or.inl h⟩
    have hrfalse : ¬Sat none w r t := fun h => hfalse ⟨trivial, Or.inr h⟩
    obtain ⟨ls, hl, hi, hf⟩ := ihq hqfalse
    obtain ⟨rs, hl', hi', hf'⟩ := ihr hrfalse
    refine ⟨ls ++ rs, ?_, ?_, ?_⟩
    · intro f h; exact (List.mem_append.mp h).elim (hl f) (hl' f)
    · intro σ h
      rw [List.map_append, allJoin_append]
      change (allJoin (ls.map Class.ofFormula) σ || allJoin (rs.map Class.ofFormula) σ) = true
      change (propEval σ q || propEval σ r) = true at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · simp [hi σ h]
      · simp [hi' σ h]
    · intro f h; exact (List.mem_append.mp h).elim (hf f) (hf' f)

/-- STAGE2 §9.2: semantic distribution, with infinite-word semantics. -/
theorem distribute_G_conj (a b : Formula (Fin ap)) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (.globally (.conj a b)) n ↔ Sat none w (.conj (.globally a) (.globally b)) n :=
  Tlsf.Rewrites.route_push_g_in trivial

theorem distribute_F_disj (a b : Formula (Fin ap)) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (.eventually (.disj a b)) n ↔ Sat none w (.disj (.eventually a) (.eventually b)) n :=
  Tlsf.Rewrites.push_f_in trivial

/-- STAGE2 §9.5: lower/upper membership bounds with exact fallback give
exactly the original Boolean test. -/
theorem fragment_bounds_exact (lo exact hi : Bool)
    (hlo : lo = true → exact = true) (hhi : exact = true → hi = true) :
    (if lo then true else if hi then exact else false) = exact := by
  cases lo <;> cases exact <;> cases hi <;> simp_all

theorem join_uses (h : Uses (join x y) a) : Uses x a ∨ Uses y a := by
  apply Classical.byContradiction; intro hn
  have hx : ¬Uses x a := fun ha => hn (Or.inl ha)
  have hy : ¬Uses y a := fun ha => hn (Or.inr ha)
  obtain ⟨σ, b, hb⟩ := h
  apply hb
  change (x (setAtom σ a b) || y (setAtom σ a b)) = (x σ || y σ)
  rw [not_uses hx, not_uses hy]

theorem join_tag (hx : HasTag tag x) (hy : HasTag tag y) : HasTag tag (join x y) :=
  fun a ha => (join_uses ha).elim (hx a) (hy a)

theorem formula_cosafety_tag (f : Formula (Fin ap)) (hc : cosafety f) : HasTag cosafety (Class.ofFormula f) := by
  intro a ha
  have hd : (Class.ofFormula f).DependsOn (modalAtoms f) := fun σ τ hh => propEval_local _ _ _ hh
  exact cosafety_atoms f hc a (uses_in_bound hd ha)

theorem reduce_cosafety_fixed (h : HasTag cosafety x) : reduce x = x := by
  apply replaceTrue_eq
  intro a ha hp
  exact hp.2 (h a ha)

theorem reduce_meet (x y : Class ap) : reduce (meet x y) = meet (reduce x) (reduce y) := by
  apply Class.ext; intro σ; rfl

theorem elide_fixed (x : Class ap) (h : dropX x = x) : elide x = x := by
  have hh : ∀ n, elideFuel n x = x := by
    intro n; cases n <;> simp [elideFuel, h]
  exact hh _

theorem modalAtom_subformula (f : Formula (Fin ap)) (a : Formula (Fin ap))
    (h : a ∈ modalAtoms f) : a ∈ subformulas f := by
  induction f with
  | tt | ff => contradiction
  | ap p | next f | strongNext f | eventually f | globally f
  | «until» f g | release f g | weakUntil f g | strongRelease f g =>
    have he := List.mem_singleton.mp h; subst a; simp [subformulas]
  | neg f ih => exact List.mem_cons_of_mem _ (ih h)
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    rcases List.mem_append.mp h with h | h
    · simp [subformulas, ihf h]
    · simp [subformulas, ihg h]

theorem step_X_subformula (b : Formula (Fin ap)) (hb : finite b) (v : Letter (Fin ap))
    (a : Formula (Fin ap)) (ha : a ∈ modalAtoms (stepSyntax v b)) (_hX : isX a) :
    a ∈ subformulas b := by
  induction b with
  | tt | ff => contradiction
  | ap p => cases hv : v p <;> simp_all [stepSyntax, modalAtoms]
  | neg f ih =>
    cases f <;> simp only [finite] at hb
    case ap p => cases hv : v p <;> simp_all [stepSyntax, modalAtoms]
  | conj f g ihf ihg | disj f g ihf ihg =>
    rcases List.mem_append.mp ha with ha | ha
    · simp [subformulas, ihf hb.1 ha]
    · simp [subformulas, ihg hb.2 ha]
  | next f => exact List.mem_cons_of_mem _ (modalAtom_subformula f a ha)
  | _ => contradiction

/-- The search atom H protects every remaining finite X tail. If H loses
support in H∨E, that class is already propositionally true. -/
theorem search_dropX_fixed (b : Formula (Fin ap)) (E : Class ap)
    (hE : ∀ a, Uses E a → isX a → a ∈ subformulas b) :
    dropX (join (Class.ofFormula (.eventually b)) E) = join (Class.ofFormula (.eventually b)) E := by
  let H := Formula.eventually b
  let Y := join (Class.ofFormula H) E
  apply replaceTrue_eq
  intro a ha hp
  have hH : Uses Y H := by
    apply Classical.byContradiction; intro hn
    have he : Y = Class.top := by
      apply Class.ext; intro σ
      have hh := not_uses hn σ true
      have ht : Y (setAtom σ H true) = true := by
        change (setAtom σ H true H || E (setAtom σ H true)) = true
        simp [setAtom]
      exact hh.symm.trans ht
    change Uses Y a at ha
    rw [he] at ha
    obtain ⟨σ, v, hv⟩ := ha
    exact hv rfl
  have hsub : a ∈ subformulas b := by
    rcases join_uses ha with hh | he
    · have hd : (Class.ofFormula H).DependsOn [H] := by
        intro σ τ h; exact h H (by simp)
      have haa := List.mem_singleton.mp (uses_in_bound hd hh)
      subst a
      exact False.elim hp.1
    · exact hE a he hp.1
  exact hp.2 ⟨H, hH, trivial, List.mem_cons_of_mem _ hsub⟩

theorem finite_nnf (f : Formula α) (hf : finite f) : NNF f := by
  induction f with
  | tt | ff | ap _ => trivial
  | neg f ih => cases f <;> simp_all [finite, NNF]
  | conj f g ihf ihg | disj f g ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | next f ih => exact ih hf
  | _ => contradiction

/-- STAGE1 §4 (2): the GF all-field is fixed, propositionally. -/
theorem gf_derivative_fixed (b : Formula (Fin ap)) (v : Letter (Fin ap)) :
    delta v (Class.ofFormula (.globally (.eventually b))) =
      U (Class.ofFormula (.globally (.eventually b))) := by
  rw [delta_globally, delta_eventually, U_globally]
  apply Class.ext; intro σ
  change ((_ || _) && (_ && _)) = (_ && _)
  cases delta v (Class.ofFormula b) σ <;> cases U (Class.ofFormula (.eventually b)) σ <;>
    cases Class.ofFormula (.globally (.eventually b)) σ <;> rfl

/-- K stays supported because H can be true independently of K. -/
theorem gf_not_simple (b : Formula (Fin ap)) (hb : finite b) :
    ¬Simple (U (Class.ofFormula (.globally (.eventually b)))) := by
  let H := Formula.eventually b
  let K := Formula.globally H
  let S := U (Class.ofFormula H)
  have hco : HasTag cosafety S := U_cosafety (formula_cosafety_tag H (finite_implies_cosafety b hb))
  have hK : ¬Uses S K := by
    intro h
    exact hco K h
  let σ : Assignment ap := fun _ => true
  let τ := setAtom σ K false
  have hS : S σ = true := by
    change (propEval σ (unfoldSyntax b) || true) = true
    simp
  have hSτ : S τ = true := (not_uses hK σ false).trans hS
  have hsupport : Uses (U (Class.ofFormula K)) K := by
    rw [U_globally]
    refine ⟨τ, true, ?_⟩
    change (S (setAtom τ K true) && setAtom τ K true K) ≠ (S τ && τ K)
    rw [not_uses hK τ true]
    simp [hSτ, τ, setAtom]
  intro hs
  rcases hs with hs | hs
  · exact hs K hsupport
  · exact hs K hsupport

/-- STAGE1 §4: every all-field of GF b is A*. -/
theorem gf_all_fixed (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) (n : Nat) :
    (run (Class.ofFormula (.globally (.eventually b))) w n).all =
      U (Class.ofFormula (.globally (.eventually b))) := by
  have hx : NNFClass (Class.ofFormula (.globally (.eventually b))) :=
    ⟨.globally (.eventually b), finite_nnf b hb, rfl⟩
  induction n with
  | zero => exact initial_all _
  | succ n ih =>
    change (transition (w n) (run _ w n)).target.all = _
    rw [transition_all_exact _ _ (run_invariant _ hx w n), ih]
    exact gf_derivative_fixed b (w n)

/-- A semantic/propositional upper bound on renewed seeds. This is enough
for the unbounded-start converse, without replacing a finite remainder by true. -/
theorem gf_seed_bound (b : Formula (Fin ap)) (hb : finite b) (v : Letter (Fin ap)) :
    rho (D v (U (Class.ofFormula (.globally (.eventually b))))) ⇒ₚ
      join (U (Class.ofFormula (.eventually b))) (U (D v (Class.ofFormula b))) := by
  let H := Formula.eventually b
  let K := Formula.globally H
  let S := U (Class.ofFormula H)
  let A := U (Class.ofFormula K)
  let E := D v (Class.ofFormula b)
  have hUb : U (Class.ofFormula b) = Class.ofFormula b := by
    rw [U_ofFormula, unfold_bounded b (finite_bounded b hb)]
  have hH : D v (Class.ofFormula H) = Class.ofFormula H := by apply Class.ext; intro σ; rfl
  have hK : D v (Class.ofFormula K) = Class.ofFormula K := by apply Class.ext; intro σ; rfl
  have hraw : D v A = meet (Class.ofFormula K) (join (Class.ofFormula H) E) := by
    dsimp only [A, K, H]
    rw [U_globally, U_eventually, hUb, D_meet, D_join, hH, hK]
    apply Class.ext; intro σ
    change ((E σ || Class.ofFormula H σ) && Class.ofFormula K σ) =
      (Class.ofFormula K σ && (Class.ofFormula H σ || E σ))
    cases E σ <;> cases Class.ofFormula H σ <;> cases Class.ofFormula K σ <;> rfl
  have hreduceK : reduce (Class.ofFormula K) = Class.top := by
    change replaceTrue (fun a => ¬isAP a ∧ ¬cosafety a) (Class.ofFormula K) = Class.top
    rw [replaceTrue_ofFormula]
    simp [replaceTrueSyntax, K, isAP, cosafety, Class.top]
  have hcoS : HasTag cosafety S := U_cosafety (formula_cosafety_tag H (finite_implies_cosafety b hb))
  have hcoE : HasTag cosafety E := D_cosafety v (formula_cosafety_tag b (finite_implies_cosafety b hb))
  have hcoH : HasTag cosafety (Class.ofFormula H) := formula_cosafety_tag H (finite_implies_cosafety b hb)
  have hdropE : dropX (join (Class.ofFormula H) E) = join (Class.ofFormula H) E := by
    apply search_dropX_fixed
    intro a ha hX
    change Uses (D v (Class.ofFormula b)) a at ha
    rw [D_ofFormula] at ha
    have hd : (Class.ofFormula (stepSyntax v b)).DependsOn (modalAtoms (stepSyntax v b)) :=
      fun σ τ hh => propEval_local _ _ _ hh
    exact step_X_subformula b hb v a (uses_in_bound hd ha) hX
  have hdropS : dropX S = S := by
    dsimp only [S, H]
    rw [U_eventually, hUb]
    have he : join (Class.ofFormula b) (Class.ofFormula (.eventually b)) =
        join (Class.ofFormula (.eventually b)) (Class.ofFormula b) := by
      apply Class.ext; intro σ; exact Bool.or_comm ..
    rw [he]
    apply search_dropX_fixed
    intro a ha _
    have hd : (Class.ofFormula b).DependsOn (modalAtoms b) := fun σ τ hh => propEval_local _ _ _ hh
    exact modalAtom_subformula b a (uses_in_bound hd ha)
  have hpassA : extractPass A = S := by
    have hr : reduce A = S := by
      dsimp only [A, K]
      rw [U_globally, reduce_meet, reduce_cosafety_fixed hcoS, hreduceK]
      apply Class.ext; intro σ; exact Bool.and_true _
    rw [extractPass, hr, elide_fixed S hdropS]
    exact U_idempotent _
  have hpassRaw : extractPass (D v A) = join S (U E) := by
    have hr : reduce (D v A) = join (Class.ofFormula H) E := by
      rw [hraw, reduce_meet, hreduceK, reduce_cosafety_fixed (join_tag hcoH hcoE)]
      apply Class.ext; intro σ; exact Bool.true_and _
    rw [extractPass, hr, elide_fixed _ hdropE, U_join]
  have hUraw : U (D v A) = A := gf_derivative_fixed b v
  change rho (D v A) ⇒ₚ join S (U E)
  unfold rho; split
  · rw [hUraw, hpassA]
    intro σ hs; change (S σ || U E σ) = true; simp [hs]
  · rw [hpassRaw]; exact implies_refl _

/-- STAGE1 §4, GF finite windows, both directions, using §3's exact
retained-obligation theorem for the converse. -/
theorem gf_language (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) :
    Inf (marks (Class.ofFormula (.globally (.eventually b))) w) ↔
      Sat none w (.globally (.eventually b)) 0 := by
  let x := Class.ofFormula (.globally (.eventually b))
  have hx : NNFClass x := ⟨.globally (.eventually b), finite_nnf b hb, rfl⟩
  constructor
  · intro hi
    refine ⟨trivial, fun t _ _ => ?_⟩
    obtain ⟨n, htn, hn⟩ := hi t
    have hsimple : ¬Simple (run x w (n+1)).all := by
      rw [gf_all_fixed b hb w (n+1)]
      exact gf_not_simple b hb
    have hseed := accepting_renewal_seed x hx w hi n hn hsimple
    rw [gf_all_fixed b hb w n] at hseed
    have hs := implication_sound (gf_seed_bound b hb (w n)) hseed
    change (U (Class.ofFormula (.eventually b)) (truthAssignment w (n+1)) ||
      U (D (w n) (Class.ofFormula b)) (truthAssignment w (n+1))) = true at hs
    rcases Bool.or_eq_true_iff.mp hs with h | h
    · have hf := (ofFormula_holds (.eventually b)).mp ((U_holds _).mp h)
      obtain ⟨j, hnj, _, hj⟩ := hf.2
      exact ⟨trivial, j, by omega, trivial, hj⟩
    · have hUb : U (Class.ofFormula b) = Class.ofFormula b := by
        rw [U_ofFormula, unfold_bounded b (finite_bounded b hb)]
      have hd : Holds w (n+1) (delta (w n) (Class.ofFormula b)) := by
        change Holds w (n+1) (U (D (w n) (Class.ofFormula b))) at h
        simpa only [delta, hUb] using h
      have hbnow := (ofFormula_holds b).mp ((derivative _ w n).mpr hd)
      exact ⟨trivial, n, htn, trivial, hbnow⟩
  · intro hw
    exact satisfying_accepts x hx w ((ofFormula_holds _).mpr hw)

/-- STAGE1 §§4–5: complement on the identical complete GF run. -/
theorem gf_complement (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) :
    FinMarks (marks (Class.ofFormula (.globally (.eventually b))) w) ↔
      ¬Sat none w (.globally (.eventually b)) 0 := by
  rw [complete_complement, gf_language b hb w]

/-- NNF dualization preserves the finite-window grammar. -/
theorem finite_nnf_polarity (b : Formula α) (hb : finite b) (pol : Bool) :
    finite (Tlsf.Rewrites.to_nnf b pol false) := by
  induction b generalizing pol with
  | tt | ff | ap _ => cases pol <;> trivial
  | neg f ih =>
    cases f <;> simp only [finite] at hb
    case ap p => cases pol <;> trivial
  | conj f g ihf ihg | disj f g ihf ihg =>
    cases pol <;> exact ⟨ihf hb.1 _, ihg hb.2 _⟩
  | next f ih => cases pol <;> exact ih hb _
  | _ => contradiction

/-- STAGE1 §4: FG b is the Fin(0) complement of GF bar(b). -/
theorem fg_language (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) :
    FinMarks (marks (Class.ofFormula (.globally (.eventually (Tlsf.Rewrites.to_nnf b false false)))) w) ↔
      Sat none w (.eventually (.globally b)) 0 := by
  rw [gf_complement _ (finite_nnf_polarity b hb false) w]
  have hd := Tlsf.Rewrites.nnf_sat (len := none) (fin := false) (j := 0)
    (Or.inr rfl) (.eventually (.globally b)) false w trivial
  have hn := not_congr hd
  simpa only [Tlsf.Rewrites.to_nnf, Bool.false_eq_true, ↓reduceIte, Classical.not_not] using hn

/-- STAGE1 §5 composed with the GF language theorem. -/
theorem gf_maxOdd (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) :
    MaxOdd (oneSetExport false (marks (Class.ofFormula (.globally (.eventually b))) w)) ↔
      Sat none w (.globally (.eventually b)) 0 :=
  (oneSet_max_inf _).trans (gf_language b hb w)

/-- STAGE1 §5 composed with the FG complement theorem. -/
theorem fg_maxOdd (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) :
    MaxOdd (oneSetExport true
      (marks (Class.ofFormula (.globally (.eventually (Tlsf.Rewrites.to_nnf b false false)))) w)) ↔
      Sat none w (.eventually (.globally b)) 0 :=
  (oneSet_max_fin _).trans (fg_language b hb w)

/-- Propositional cofactoring does not descend inside a frozen modality. -/
def falseCofactorSyntax (a : Formula (Fin ap)) : Formula (Fin ap) → Formula (Fin ap)
  | .tt => .tt | .ff => .ff
  | .neg f => .neg (falseCofactorSyntax a f)
  | .conj f g => .conj (falseCofactorSyntax a f) (falseCofactorSyntax a g)
  | .disj f g => .disj (falseCofactorSyntax a f) (falseCofactorSyntax a g)
  | .impl f g => .impl (falseCofactorSyntax a f) (falseCofactorSyntax a g)
  | .equiv f g => .equiv (falseCofactorSyntax a f) (falseCofactorSyntax a g)
  | f => if f = a then .ff else f

theorem falseCofactor_eval (a f : Formula (Fin ap)) (σ : Assignment ap) :
    propEval σ (falseCofactorSyntax a f) = propEval (setAtom σ a false) f := by
  induction f with
  | tt | ff => rfl
  | neg f ih => simp only [falseCofactorSyntax, propEval, ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [falseCofactorSyntax, propEval, ihf, ihg]
  | _ => simp only [falseCofactorSyntax]; split <;> simp_all [propEval, setAtom]

def falseCofactor (x : Class ap) (a : Formula (Fin ap)) : Class ap :=
  ⟨fun σ => x (setAtom σ a false), falseCofactorSyntax a x.repr, by
    funext σ; rw [falseCofactor_eval, repr_eval]⟩

/-- STAGE2 §6.3 (8): loss of a protector permits its removal from the proof
constraint. This is a false cofactor, not an extractor operation. -/
theorem losing_protector {x y C : Class ap} (hxy : x ⇒ₚ y) (hyC : y ⇒ₚ C)
    (habsent : ¬Uses y H) : x ⇒ₚ falseCofactor C H := by
  intro σ hx
  apply hyC (setAtom σ H false)
  rw [not_uses habsent]
  exact hxy σ hx

/-- A protected constraint survives every simultaneous true-substitution
that leaves its supported variables untouched. -/
theorem elision_preserves_constraint {y C : Class ap} (hyC : y ⇒ₚ C)
    (p : Formula (Fin ap) → Prop) (hp : ∀ a, Uses C a → ¬p a) : replaceTrue p y ⇒ₚ C := by
  have he := replaceTrue_eq p C hp
  have hm : replaceTrue p y ⇒ₚ replaceTrue p C := fun σ h => hyC _ h
  rwa [he] at hm

/-- STAGE2 §6.2: abandoned false finite candidates become propositionally
false after their horizon, rather than merely remaining LTL-false. -/
theorem flush_false_window (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap))
    (t n : Nat) (hn : horizon b + 1 ≤ n) (hfalse : ¬Sat none w b t) :
    derivatives w t n (Class.ofFormula b) = Class.bot := by
  apply derivatives_bot_persists _ hn
  simpa only [hfalse, ↓reduceIte] using finite_window_constant b hb w t

/-- The numerical descent principle used when the failed-clause index set
only loses elements. It bounds the number of losses, not their last time. -/
theorem decreasing_eventually_constant (f : Nat → Nat)
    (h : ∀ i j, i ≤ j → f j ≤ f i) : ∃ N, ∀ n, N ≤ n → f n = f N := by
  have hex : ∃ k, ∃ n, f n = k := ⟨f 0, 0, rfl⟩
  obtain ⟨k, ⟨N, hN⟩, hmin⟩ := exists_least_nat hex
  refine ⟨N, fun n hn => ?_⟩
  have hle := h N n hn
  have hge : k ≤ f n := by
    apply Nat.le_of_not_gt
    intro hlt
    exact hmin (f n) hlt ⟨n, rfl⟩
  omega

/-- The raw all-field at a position, with x₀ equal to the canonical input. -/
def rawAll (x : Class ap) (w : Word (Fin ap)) : Nat → Class ap
  | 0 => x
  | n+1 => D (w n) (run x w n).all

/-- STAGE2 §6.5: the last step of the targeted converse, with §6.4 (9)
explicitly supplied as a hypothesis. This theorem does not discharge (9). -/
theorem converse_of_eventually_false_seeds (x : Class ap) (hx : NNFClass x) (w : Word (Fin ap))
    (hseeds : ¬Holds w 0 x → (∀ n, (run x w n).all ≠ Class.bot) →
      ∃ N, ∀ n, N ≤ n → ¬Holds w n (rho (rawAll x w n))) :
    Inf (marks x w) → Holds w 0 x := by
  intro hi
  apply Classical.byContradiction; intro hn
  obtain ⟨N, hN⟩ := hseeds hn (accepting_never_bot x hx w hi)
  obtain ⟨n, hNn, hm⟩ := hi N
  have hs : ¬Simple (run x w (n+1)).all := by
    intro hs
    have hsat := accepting_simple_suffix x hx w hi (n+1) hs
    exact hn ((all_field_exactness x hx w (n+1)).mp hsat)
  have hseed := accepting_renewal_seed x hx w hi n hm hs
  exact hN (n+1) (by omega) hseed

/-- The corresponding min-even language equality for GF finite windows. -/
theorem gf_minEven (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) :
    MinEven (oneSetMin false (marks (Class.ofFormula (.globally (.eventually b))) w)) ↔
      Sat none w (.globally (.eventually b)) 0 :=
  (oneSet_min_inf _).trans (gf_language b hb w)

/-- The corresponding min-even language equality for FG finite windows. -/
theorem fg_minEven (b : Formula (Fin ap)) (hb : finite b) (w : Word (Fin ap)) :
    MinEven (oneSetMin true
      (marks (Class.ofFormula (.globally (.eventually (Tlsf.Rewrites.to_nnf b false false)))) w)) ↔
      Sat none w (.eventually (.globally b)) 0 :=
  (oneSet_min_fin _).trans (fg_language b hb w)

end
end Tlsf.Dpa
