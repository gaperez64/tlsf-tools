import TlsfProofs.Dpa.Zielonka

/-! # STAGE2 §§1,6,8: flat converse and assembled admitted grammar
The failed-clause proof follows equations (6)–(9), retaining finite candidates
and inspecting every intermediate extraction pass. §9 is in Refinements.lean.
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

/-- The exact syntactic grammar of STAGE2 §8; `admitted_grammar` assembles
its component/product/parity language theorem below. -/
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


/-! ## STAGE2 §6.1: failed clauses and exact residuals (6)–(7). -/
def flatLoops (bs : List (Formula (Fin ap))) : Class ap :=
  allJoin (bs.map (fun b => Class.ofFormula (.eventually b)))
def flatBodies (bs : List (Formula (Fin ap))) : Class ap := allJoin (bs.map Class.ofFormula)

theorem join_nnf (hx : NNFClass x) (hy : NNFClass y) : NNFClass (join x y) := by
  obtain ⟨f, hf, rfl⟩ := hx; obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨.disj f g, ⟨hf,hg⟩, by apply Class.ext; intro σ; rfl⟩

theorem formula_finite_tag (b : Formula (Fin ap)) (hb : finite b) : HasTag finite (Class.ofFormula b) := by
  intro a ha
  exact finite_atoms b hb a (uses_in_bound (fun σ τ hh => propEval_local b σ τ hh) ha)

theorem finite_U_fixed (h : HasTag finite x) : U x = x := by
  apply Class.ext; intro σ
  change x (unfoldAtom σ) = x σ
  apply support_locality
  intro a ha
  change propEval σ (unfoldSyntax a) = σ a
  rw [unfold_bounded a (finite_bounded a (h a ha))]
  exact propEval_used_atom ha σ

theorem D_finite (v : Letter (Fin ap)) (h : HasTag finite x) : HasTag finite (D v x) :=
  tags_intersection (D_safety v (fun a ha => finite_implies_safety a (h a ha)))
    (D_cosafety v (fun a ha => finite_implies_cosafety a (h a ha)))

theorem allJoin_tag (xs : List (Class ap)) (h : ∀ x, x ∈ xs → HasTag tag x) : HasTag tag (allJoin xs) := by
  induction xs with
  | nil => exact bot_hasTag _
  | cons x xs ih => exact join_tag (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem allJoin_nnf (xs : List (Class ap)) (h : ∀ x, x ∈ xs → NNFClass x) : NNFClass (allJoin xs) := by
  induction xs with
  | nil => exact ⟨.ff, trivial, rfl⟩
  | cons x xs ih => exact join_nnf (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem flatBodies_finite (hb : ∀ b, b ∈ bs → finite b) : HasTag finite (flatBodies bs) := by
  apply allJoin_tag; intro x hx
  obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hx
  exact formula_finite_tag b (hb b hb')

theorem flatBodies_nnf (hb : ∀ b, b ∈ bs → finite b) : NNFClass (flatBodies bs) := by
  apply allJoin_nnf; intro x hx
  obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hx
  exact ⟨b,finite_nnf b (hb b hb'),rfl⟩

theorem flatLoops_cosafety (hb : ∀ b, b ∈ bs → finite b) : HasTag cosafety (flatLoops bs) := by
  apply allJoin_tag; intro x hx
  obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hx
  exact formula_cosafety_tag _ (finite_implies_cosafety b (hb b hb'))

theorem flatLoops_nnf (hb : ∀ b, b ∈ bs → finite b) : NNFClass (flatLoops bs) := by
  apply allJoin_nnf; intro x hx
  obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hx
  exact ⟨.eventually b,finite_nnf b (hb b hb'),rfl⟩

theorem flatLoops_append (bs cs : List (Formula (Fin ap))) :
    flatLoops (bs++cs) = join (flatLoops bs) (flatLoops cs) := by
  simp only [flatLoops, List.map_append, allJoin_append]

theorem U_flatLoops (hb : ∀ b, b ∈ bs → finite b) :
    U (flatLoops bs) = join (flatLoops bs) (flatBodies bs) := by
  induction bs with
  | nil => apply Class.ext; intro σ; rfl
  | cons b bs ih =>
    have hUb : U (Class.ofFormula b) = Class.ofFormula b := finite_U_fixed (formula_finite_tag b (hb b (by simp)))
    simp only [flatLoops, flatBodies, List.map_cons, allJoin] at *
    rw [U_join, U_eventually, hUb, ih (fun c hc => hb c (by simp [hc]))]
    apply Class.ext; intro σ
    change ((_ || _) || (_ || _)) = ((_ || _) || (_ || _))
    cases Class.ofFormula b σ <;> cases Class.ofFormula (.eventually b) σ <;>
      cases allJoin (bs.map (fun b => Class.ofFormula (.eventually b))) σ <;>
      cases allJoin (bs.map Class.ofFormula) σ <;> rfl

theorem D_flatLoops (v : Letter (Fin ap)) (bs : List (Formula (Fin ap))) : D v (flatLoops bs) = flatLoops bs := by
  induction bs with
  | nil => apply Class.ext; intro σ; rfl
  | cons b bs ih =>
    change D v (join (Class.ofFormula (.eventually b)) (flatLoops bs)) = _
    rw [D_join, ih]
    rfl

/-- Equation (7), with the finite residual kept exactly. -/
theorem flat_residual_step (hb : ∀ b, b ∈ bs → finite b) (hE : HasTag finite E)
    (v : Letter (Fin ap)) :
    D v (U (join (flatLoops bs) E)) =
      join (flatLoops bs) (join (D v (flatBodies bs)) (D v E)) := by
  rw [U_join, U_flatLoops hb, finite_U_fixed hE, D_join, D_join, D_flatLoops]
  apply Class.ext; intro σ; exact Bool.or_assoc ..

theorem flatBodies_false (w : Word (Fin ap)) (n : Nat)
    (h : ∀ b, b ∈ bs → ¬Sat none w b n) : ¬Holds w n (flatBodies bs) := by
  apply Bool.eq_false_iff.mp
  apply (allJoin_false _ _).mpr
  intro x hx; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact Bool.eq_false_iff.mpr (fun ht => h b hb ((ofFormula_holds b).mp ht))

theorem flatLoops_false (w : Word (Fin ap)) (n : Nat)
    (h : ∀ b, b ∈ bs → ¬Sat none w (.eventually b) n) : ¬Holds w n (flatLoops bs) := by
  apply Bool.eq_false_iff.mp
  apply (allJoin_false _ _).mpr
  intro x hx; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact Bool.eq_false_iff.mpr (fun ht => h b hb ((ofFormula_holds _).mp ht))

theorem join_false (hx : ¬Holds w n x) (hy : ¬Holds w n y) : ¬Holds w n (join x y) := by
  change ¬(_ || _) = true
  simp only [Bool.or_eq_true]; exact fun h => h.elim hx hy

/-- The single failed clause of §6.1, separated into its H atoms and its
finite remainder, without changing the monitored formula. -/
theorem failed_flat_clause (hq : FlatQ q) (w : Word (Fin ap)) (t : Nat)
    (hf : ¬Sat none w q t) :
    ∃ bs E, (∀ b, b ∈ bs → finite b) ∧ NNFClass E ∧ HasTag finite E ∧
      (Class.ofFormula q ⇒ₚ join (flatLoops bs) E) ∧ ¬Holds w t E ∧
      (∀ b, b ∈ bs → ∀ n, t ≤ n → ¬Sat none w (.eventually b) n) := by
  induction hq with
  | @window b hb =>
    refine ⟨[], Class.ofFormula b, by simp, ⟨b,finite_nnf b hb,rfl⟩, formula_finite_tag b hb, ?_, ?_, by simp⟩
    · intro σ h; change (false || propEval σ b) = true; exact h
    · exact fun ht => hf ((ofFormula_holds b).mp ht)
  | @eventual b hb =>
    refine ⟨[b],Class.bot, ?_, ⟨.ff,trivial,rfl⟩,bot_hasTag _,?_,by intro h; exact Bool.noConfusion h,?_⟩
    · intro c hc; have he := List.mem_singleton.mp hc; subst c; exact hb
    · intro σ h; change ((σ (.eventually b) || false) || false) = true; change σ (.eventually b) = true at h; simpa using h
    · intro c hc n hn hs; have he := List.mem_singleton.mp hc; subst c
      obtain ⟨j,hj,_,hs⟩ := hs.2
      exact hf ⟨trivial,j,by omega,trivial,hs⟩
  | @conj q r hq hr ihq ihr =>
    by_cases h : Sat none w q t
    · obtain ⟨bs,E,hb,he,hfin,hi,hfE,hfalse⟩ := ihr (fun hh => hf ⟨trivial,h,hh⟩)
      refine ⟨bs,E,hb,he,hfin,?_,hfE,hfalse⟩
      intro σ hh; apply hi σ; exact (Bool.and_eq_true_iff.mp hh).2
    · obtain ⟨bs,E,hb,he,hfin,hi,hfE,hfalse⟩ := ihq h
      refine ⟨bs,E,hb,he,hfin,?_,hfE,hfalse⟩
      intro σ hh; apply hi σ; exact (Bool.and_eq_true_iff.mp hh).1
  | @disj q r hq hr ihq ihr =>
    obtain ⟨bs,E,hb,he,hfin,hi,hfE,hfalse⟩ := ihq (fun h => hf ⟨trivial,Or.inl h⟩)
    obtain ⟨cs,F,hc,hf',hfin',hi',hfF,hfalse'⟩ := ihr (fun h => hf ⟨trivial,Or.inr h⟩)
    refine ⟨bs++cs,join E F,?_,join_nnf he hf',join_tag hfin hfin',?_,join_false hfE hfF,?_⟩
    · intro b hb'; exact (List.mem_append.mp hb').elim (hb b) (hc b)
    · intro σ hh; rw [flatLoops_append]
      change ((_ || _) || (_ || _)) = true
      rcases Bool.or_eq_true_iff.mp hh with hh | hh
      · have ht := hi σ hh; change (_ || _) = true at ht
        rcases Bool.or_eq_true_iff.mp ht with ht | ht <;> simp [ht]
      · have ht := hi' σ hh; change (_ || _) = true at ht
        rcases Bool.or_eq_true_iff.mp ht with ht | ht <;> simp [ht]
    · intro b hb'; exact (List.mem_append.mp hb').elim (hfalse b) (hfalse' b)

/-- Exact all-field/raw-field relation used in (6). -/
theorem U_rawAll (hx : NNFClass x) (w : Word (Fin ap)) (n : Nat) :
    U (rawAll x w n) = (run x w n).all := by
  cases n with
  | zero => exact (initial_all x).symm
  | succ n => exact (transition_all_exact _ _ (run_invariant x hx w n)).symm

theorem rawAll_nnf (hx : NNFClass x) (w : Word (Fin ap)) (n : Nat) : NNFClass (rawAll x w n) := by
  cases n with
  | zero => exact hx
  | succ n => exact D_nnfClass _ (run_invariant x hx w n).1

/-- G's retained continuation forces U(q) at every all-field. -/
theorem global_all_implies (q : Formula (Fin ap)) (hn : NNF q) (w : Word (Fin ap)) (n : Nat) :
    (run (Class.ofFormula (.globally q)) w n).all ⇒ₚ U (Class.ofFormula q) := by
  have hx : NNFClass (Class.ofFormula (.globally q)) := ⟨.globally q,hn,rfl⟩
  have hK : ∀ n, (run (Class.ofFormula (.globally q)) w n).all ⇒ₚ U (Class.ofFormula (.globally q)) := by
    intro n; induction n with
    | zero => rw [run,initial_all]; exact implies_refl _
    | succ n ih =>
      rw [show (run _ w (n+1)).all = _ from transition_all_exact _ _ (run_invariant _ hx w n)]
      apply implies_trans (U_monotone (D_monotone _ ih))
      rw [U_globally, D_meet, U_meet]
      simp only [D_ofFormula, stepSyntax]
      intro σ h; simpa only [U_globally] using (Bool.and_eq_true_iff.mp h).2
  apply implies_trans (hK n)
  rw [U_globally]
  intro σ h; exact (Bool.and_eq_true_iff.mp h).1

theorem flatQ_nnf (hq : FlatQ q) : NNF q := by
  induction hq with
  | window h => exact finite_nnf _ h
  | @eventual b h => exact finite_nnf b h
  | conj _ _ ih ih' | disj _ _ ih ih' => exact ⟨ih,ih'⟩

/-- A false clause constraint (6). The selected loops never become true;
E records all pending finite candidates exactly. -/
def BadFlatConstraint (x : Class ap) (w : Word (Fin ap))
    (bs : List (Formula (Fin ap))) (n : Nat) (E : Class ap) : Prop :=
  (∀ b, b ∈ bs → finite b) ∧ NNFClass E ∧ HasTag finite E ∧
    (∀ b, b ∈ bs → ∀ j, n ≤ j → ¬Sat none w (.eventually b) j) ∧
    ¬Holds w n E ∧ (rawAll x w n ⇒ₚ join (flatLoops bs) E)

/-- One exact step of (6)–(7). -/
theorem badFlat_step (hx : NNFClass x) (h : BadFlatConstraint x w bs n E) :
    BadFlatConstraint x w bs (n+1) (join (D (w n) (flatBodies bs)) (D (w n) E)) := by
  obtain ⟨hb,hn,hfin,hfalse,hE,hi⟩ := h
  have hdf : ∀ y, HasTag finite y → (Holds w (n+1) (D (w n) y) ↔ Holds w n y) := by
    intro y hy
    have hh := derivative y w n
    simpa only [delta, finite_U_fixed hy, finite_U_fixed (D_finite _ hy)] using hh.symm
  refine ⟨hb, join_nnf (D_nnfClass _ (flatBodies_nnf hb)) (D_nnfClass _ hn),
    join_tag (D_finite _ (flatBodies_finite hb)) (D_finite _ hfin),
    fun b hb' j hj => hfalse b hb' j (by omega), ?_, ?_⟩
  · apply join_false
    · intro hh; apply flatBodies_false w n (fun b hb' hs => hfalse b hb' n (Nat.le_refl _) ⟨trivial,n,Nat.le_refl _,trivial,hs⟩)
      exact (hdf _ (flatBodies_finite hb)).mp hh
    · exact fun hh => hE ((hdf _ hfin).mp hh)
  · change D (w n) (run x w n).all ⇒ₚ _
    rw [← U_rawAll hx w n]
    have hh := D_monotone (w n) (U_monotone hi)
    rwa [flat_residual_step hb hfin] at hh

/-- A failed G(q) supplies the initial clause constraint, after one raw step. -/
theorem initial_badFlat (hq : FlatQ q) (w : Word (Fin ap)) (hf : ¬Sat none w (.globally q) 0) :
    ∃ bs n E, BadFlatConstraint (Class.ofFormula (.globally q)) w bs n E := by
  have hn := flatQ_nnf hq
  have ht : ∃ t, ¬Sat none w q t := by
    apply Classical.byContradiction; intro h
    apply hf; exact ⟨trivial,fun t _ _ => Classical.byContradiction (fun hn => h ⟨t,hn⟩)⟩
  obtain ⟨t,ht⟩ := ht
  obtain ⟨bs,E,hb,hE,hfin,hi,hfalse,hloops⟩ := failed_flat_clause hq w t ht
  let F := join (D (w t) (flatBodies bs)) (D (w t) E)
  have hdf : ∀ y, HasTag finite y → (Holds w (t+1) (D (w t) y) ↔ Holds w t y) := by
    intro y hy; simpa only [delta,finite_U_fixed hy,finite_U_fixed (D_finite _ hy)] using (derivative y w t).symm
  refine ⟨bs,t+1,F,hb,join_nnf (D_nnfClass _ (flatBodies_nnf hb)) (D_nnfClass _ hE),
    join_tag (D_finite _ (flatBodies_finite hb)) (D_finite _ hfin),
    fun b hb' j hj => hloops b hb' j (by omega),?_,?_⟩
  · apply join_false
    · intro hh; apply flatBodies_false w t (fun b hb' hs => hloops b hb' t (Nat.le_refl _) ⟨trivial,t,Nat.le_refl _,trivial,hs⟩)
      exact (hdf _ (flatBodies_finite hb)).mp hh
    · exact fun hh => hfalse ((hdf _ hfin).mp hh)
  · have hh := D_monotone (w t) (implies_trans (global_all_implies q hn w t) (U_monotone hi))
    rwa [flat_residual_step hb hfin] at hh


/-! ## STAGE2 §6.2: flushing abandoned candidates. -/
theorem subformula_trans (hab : a ∈ subformulas b) (hbc : b ∈ subformulas c) : a ∈ subformulas c := by
  induction c with
  | tt | ff | ap _ =>
    have he := List.mem_singleton.mp hbc; subst b; exact hab
  | neg f ih | next f ih | strongNext f ih | eventually f ih | globally f ih =>
    rcases List.mem_cons.mp hbc with he | hh
    · subst b; exact hab
    · exact List.mem_cons_of_mem _ (ih hh)
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg
  | «until» f g ihf ihg | release f g ihf ihg | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    rcases List.mem_cons.mp hbc with he | hh
    · subst b; exact hab
    · rcases List.mem_append.mp hh with hh | hh
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihf hh))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihg hh))

theorem modalAtoms_shape (f : Formula (Fin ap)) (a : Formula (Fin ap)) (ha : a ∈ modalAtoms f) :
    isAP a ∨ isX a ∨ ¬finite a := by
  induction f with
  | tt | ff => contradiction
  | ap p | next f | strongNext f | eventually f | globally f
  | «until» f g | release f g | weakUntil f g | strongRelease f g =>
    have he := List.mem_singleton.mp ha; subst a
    simp [isAP,isX,finite]
  | neg f ih => exact ih ha
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    exact (List.mem_append.mp ha).elim ihf ihg

/-- Every surviving X belongs to a still selected finite body. -/
def TailBound (bs : List (Formula (Fin ap))) (E : Class ap) : Prop :=
  ∀ a, Uses E a → isX a → ∃ b, b ∈ bs ∧ a ∈ subformulas b

theorem tailBound_bot (bs : List (Formula (Fin ap))) : TailBound bs Class.bot := by
  intro a ha; obtain ⟨σ,b,hb⟩ := ha; exact False.elim (hb rfl)

theorem tailBound_join (hx : TailBound bs x) (hy : TailBound bs y) : TailBound bs (join x y) :=
  fun a ha hX => (join_uses ha).elim (fun h => hx a h hX) (fun h => hy a h hX)

theorem allJoin_uses (xs : List (Class ap)) (h : Uses (allJoin xs) a) : ∃ x, x ∈ xs ∧ Uses x a := by
  induction xs with
  | nil => obtain ⟨σ,b,hb⟩ := h; exact False.elim (hb rfl)
  | cons x xs ih =>
    rcases join_uses h with hx | hx
    · exact ⟨x,by simp,hx⟩
    · obtain ⟨y,hy,ha⟩ := ih hx; exact ⟨y,by simp [hy],ha⟩

theorem tailBound_bodies (_hb : ∀ b, b ∈ bs → finite b) : TailBound bs (flatBodies bs) := by
  intro a ha _
  obtain ⟨x,hx,hu⟩ := allJoin_uses _ ha
  obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hx
  exact ⟨b,hb',modalAtom_subformula b a (uses_in_bound (fun σ τ hh => propEval_local b σ τ hh) hu)⟩

theorem tailBound_D (hfin : HasTag finite E) (h : TailBound bs E) (v : Letter (Fin ap)) :
    TailBound bs (D v E) := by
  intro t ht hX
  obtain ⟨a,ha,hat⟩ := D_uses v ht
  have hmem : t ∈ modalAtoms (stepSyntax v a) := uses_in_bound (fun σ τ hh => propEval_local _ σ τ hh) hat
  have hshape := modalAtoms_shape E.repr a (uses_in_bound (fun σ τ hh => by rw [← repr_eval E σ,← repr_eval E τ]; exact propEval_local _ σ τ hh) ha)
  rcases hshape with hap | hax | hmodal
  · cases a <;> simp only [isAP] at hap
    case ap p => cases hv : v p <;> simp_all [stepSyntax,modalAtoms]
  · obtain ⟨b,hb,hsub⟩ := h a ha hax
    exact ⟨b,hb,subformula_trans (step_X_subformula a (hfin a ha) v t hmem hX) hsub⟩
  · exact False.elim (hmodal (hfin a ha))

/-- The exact finite part of (7), iterated without dropping old candidates. -/
def flatCandidates (bs : List (Formula (Fin ap))) (w : Word (Fin ap)) (t : Nat) : Nat → Class ap → Class ap
  | 0, E => E
  | n+1, E => join (D (w (t+n)) (flatBodies bs)) (D (w (t+n)) (flatCandidates bs w t n E))

theorem flatCandidates_finite (hb : ∀ b, b ∈ bs → finite b) (hE : HasTag finite E) (n : Nat) :
    HasTag finite (flatCandidates bs w t n E) := by
  induction n with
  | zero => exact hE
  | succ n ih => exact join_tag (D_finite _ (flatBodies_finite hb)) (D_finite _ ih)

theorem flatCandidates_bound (hb : ∀ b, b ∈ bs → finite b) (n : Nat) :
    TailBound bs (flatCandidates bs w t n Class.bot) := by
  induction n with
  | zero => exact tailBound_bot bs
  | succ n ih =>
    exact tailBound_join (tailBound_D (flatBodies_finite hb) (tailBound_bodies hb) _)
      (tailBound_D (flatCandidates_finite hb (bot_hasTag _) n) ih _)

theorem derivatives_finite (hE : HasTag finite E) (w : Word (Fin ap)) (t n : Nat) :
    HasTag finite (derivatives w t n E) := by
  induction n with
  | zero => simpa only [derivatives,finite_U_fixed hE] using hE
  | succ n ih =>
    rw [derivatives_snoc]
    simpa only [finite_U_fixed (D_finite _ ih)] using D_finite (w (t+n)) ih

/-- Initial finite candidates and fresh candidates evolve independently in
(7). This equality is used only in the proof, without changing the automaton. -/
theorem flatCandidates_split (hE : HasTag finite E) (n : Nat) :
    flatCandidates bs w t n E =
      join (flatCandidates bs w t n Class.bot) (derivatives w t n E) := by
  induction n with
  | zero => rw [flatCandidates,flatCandidates,derivatives,finite_U_fixed hE]; apply Class.ext; intro σ; rfl
  | succ n ih =>
    rw [flatCandidates,ih,D_join,derivatives_snoc,finite_U_fixed (D_finite _ (derivatives_finite hE w t n))]
    apply Class.ext; intro σ
    exact (Bool.or_assoc ..).symm

theorem badFlat_iterate (hx : NNFClass x) (h : BadFlatConstraint x w bs t E) (n : Nat) :
    BadFlatConstraint x w bs (t+n) (flatCandidates bs w t n E) := by
  induction n with
  | zero => exact h
  | succ n ih => exact badFlat_step hx ih

/-- STAGE2 §6.2: after a finite wait, every X of the false constraint is
protected by a selected body. False old candidates have become Boolean false. -/
theorem badFlat_flush (hx : NNFClass x) (h : BadFlatConstraint x w bs t E) :
    ∃ N, t ≤ N ∧ ∀ n, N ≤ n → ∃ F, BadFlatConstraint x w bs n F ∧ TailBound bs F := by
  have hs : HasTag safety E := fun a ha => finite_implies_safety a (h.2.2.1 a ha)
  obtain ⟨k,hk⟩ := class_safety_bad_prefix E (nnfClass_positive h.2.1) hs h.2.2.2.2.1
  refine ⟨t+k,by omega,fun n hn => ?_⟩
  have hi := badFlat_iterate hx h (n-t)
  have he : flatCandidates bs w t (n-t) E = flatCandidates bs w t (n-t) Class.bot := by
    rw [flatCandidates_split h.2.2.1,derivatives_bot_persists hk (by omega)]
    apply Class.ext; intro σ; exact Bool.or_false _
  rw [Nat.add_sub_cancel' (by omega : t ≤ n),he] at hi
  exact ⟨_,hi,flatCandidates_bound h.1 (n-t)⟩


/-! ## STAGE2 §6.3: losing a protector, equation (8). -/
def removeBody (b : Formula (Fin ap)) (bs : List (Formula (Fin ap))) : List (Formula (Fin ap)) :=
  bs.filter (fun c => decide (c ≠ b))

theorem removeBody_shorter (hb : b ∈ bs) : (removeBody b bs).length < bs.length := by
  have hh := filter_strict bs (fun _ => true) (fun c => decide (c ≠ b))
    (fun _ _ _ => rfl) ⟨b,hb,rfl,by simp⟩
  rw [show bs.filter (fun _ => true) = bs from List.filter_eq_self.mpr (by simp)] at hh
  exact hh

theorem flatLoops_cofactor (b : Formula (Fin ap)) (bs : List (Formula (Fin ap))) (σ : Assignment ap) :
    flatLoops bs (setAtom σ (.eventually b) false) = flatLoops (removeBody b bs) σ := by
  induction bs with
  | nil => rfl
  | cons c cs ih =>
    by_cases he : c = b
    · subst c
      rw [show removeBody b (b::cs) = removeBody b cs by simp [removeBody]]
      change (setAtom σ (.eventually b) false (.eventually b) || flatLoops cs (setAtom σ (.eventually b) false)) = _
      rw [ih]
      simp [setAtom]
    · have hh : Formula.eventually c ≠ Formula.eventually b := fun h => he (Formula.eventually.inj h)
      rw [show removeBody b (c::cs) = c::removeBody b cs by simp [removeBody,he]]
      change (setAtom σ (.eventually b) false (.eventually c) || flatLoops cs (setAtom σ (.eventually b) false)) =
        (σ (.eventually c) || flatLoops (removeBody b cs) σ)
      rw [ih]
      simp [setAtom,hh]

/-- Support independence justifies the smaller false clause, preserving E. -/
theorem badFlat_remove (h : BadFlatConstraint x w bs n E) (_hb : b ∈ bs)
    (hxy : rawAll x w n ⇒ₚ y) (hyC : y ⇒ₚ join (flatLoops bs) E)
    (habs : ¬Uses y (.eventually b)) : BadFlatConstraint x w (removeBody b bs) n E := by
  have hEC : ¬Uses E (.eventually b) := fun hu => h.2.2.1 _ hu
  have hi := losing_protector hxy hyC habs
  refine ⟨fun c hc => h.1 c (List.mem_filter.mp hc).1,h.2.1,h.2.2.1,
    fun c hc => h.2.2.2.1 c (List.mem_filter.mp hc).1,h.2.2.2.2.1,?_⟩
  intro σ hs
  have hh := hi σ hs
  change (flatLoops bs (setAtom σ (.eventually b) false) || E (setAtom σ (.eventually b) false)) = true at hh
  rw [flatLoops_cofactor,not_uses hEC] at hh
  exact hh

/-- A finite false obligation forces a later false all-field; this does not
assume Büchi acceptance. It is the finite-horizon observation of §6.4. -/
theorem neverBot_finite_obligation (hx : NNFClass x) (hnever : ∀ n, (run x w n).all ≠ Class.bot)
    (hE : NNFClass E) (hfin : HasTag finite E) (hi : (run x w n).all ⇒ₚ E) : Holds w n E := by
  apply Classical.byContradiction; intro hf
  obtain ⟨k,hk⟩ := class_safety_bad_prefix E (nnfClass_positive hE)
    (fun a ha => finite_implies_safety a (hfin a ha)) hf
  have hh := derivatives_monotone w n k hi
  rw [hk,← run_after x hx w n k] at hh
  exact hnever (n+k) (implies_bot hh)

theorem extractPass_nnf (hx : NNFClass x) : NNFClass (extractPass x) :=
  U_nnfClass (elideFuel_nnfClass _ (replaceTrue_nnfClass _ hx))

theorem extractPass_weakens (hx : NNFClass x) : U x ⇒ₚ extractPass x := by
  apply U_monotone
  apply implies_trans (replaceTrue_weakens (nnfClass_positive hx) _ ?_)
    (elideFuel_weakens _ (replaceTrue_positive (nnfClass_positive hx) _))
  intro a ha hp; exact hp.1 ha

/-- At a least-size failed clause, every selected protector survives every
intermediate extraction class. A loss would give (8) with strictly fewer Hs. -/
theorem minimal_protectors (h : BadFlatConstraint x w bs n E)
    (hmin : ∀ cs j F, BadFlatConstraint x w cs j F → bs.length ≤ cs.length)
    (hxy : rawAll x w n ⇒ₚ y) (hyC : y ⇒ₚ join (flatLoops bs) E) :
    ∀ b, b ∈ bs → Uses y (.eventually b) := by
  intro b hb
  apply Classical.byContradiction; intro habs
  have hh := hmin _ _ _ (badFlat_remove h hb hxy hyC habs)
  have hlt := removeBody_shorter hb
  omega

/-- Selected Hs protect every supported X of a flushed constraint, at each
simultaneous removal pass, with protection recomputed at that pass. -/
theorem flat_constraint_protected (hbound : TailBound bs E)
    (hp : ∀ b, b ∈ bs → Uses y (.eventually b)) :
    ∀ a, Uses (join (flatLoops bs) E) a → isX a → Protected y a := by
  intro a ha hX
  rcases join_uses ha with hl | he
  · obtain ⟨z,hz,hu⟩ := allJoin_uses _ hl
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    have hd : (Class.ofFormula (.eventually b)).DependsOn [.eventually b] := fun σ τ h => h _ (by simp)
    have he := List.mem_singleton.mp (uses_in_bound hd hu)
    subst a; exact False.elim hX
  · obtain ⟨b,hb,hs⟩ := hbound a he hX
    exact ⟨.eventually b,hp b hb,trivial,List.mem_cons_of_mem _ hs⟩

/-- The whole first extraction pass preserves the false constraint after the
last loss/flush. This includes all intermediate X-removal iterations. -/
theorem minimal_extractPass_constraint (hx : NNFClass x) (h : BadFlatConstraint x w bs n E)
    (hbound : TailBound bs E)
    (hmin : ∀ cs j F, BadFlatConstraint x w cs j F → bs.length ≤ cs.length) :
    extractPass (rawAll x w n) ⇒ₚ U (join (flatLoops bs) E) := by
  let C := join (flatLoops bs) E
  have hco : HasTag cosafety C := join_tag (flatLoops_cosafety h.1)
    (fun a ha => finite_implies_cosafety a (h.2.2.1 a ha))
  have hrnn := rawAll_nnf hx w n
  have hred : reduce (rawAll x w n) ⇒ₚ C := by
    have hh : reduce (rawAll x w n) ⇒ₚ reduce C := fun σ hs => h.2.2.2.2.2 _ hs
    rwa [reduce_cosafety_fixed hco] at hh
  have hweak : rawAll x w n ⇒ₚ reduce (rawAll x w n) := by
    apply replaceTrue_weakens (nnfClass_positive hrnn)
    intro a ha hp; exact hp.1 ha
  have loop : ∀ fuel y, NNFClass y → (rawAll x w n ⇒ₚ y) → (y ⇒ₚ C) → elideFuel fuel y ⇒ₚ C := by
    intro fuel; induction fuel with
    | zero => intro y _ _ hy; exact hy
    | succ fuel ih =>
      intro y hyn hxy hy
      have hp := flat_constraint_protected hbound (minimal_protectors h hmin hxy hy)
      have hd : dropX y ⇒ₚ C := elision_preserves_constraint hy _ (by
        intro a ha hh; exact hh.2 (hp a ha hh.1))
      have hw : y ⇒ₚ dropX y := replaceTrue_weakens (nnfClass_positive hyn) _ (by
        intro a ha hp; cases a <;> simp_all [isAP,isX])
      simp only [elideFuel]
      split
      · exact hy
      · exact ih _ (replaceTrue_nnfClass _ hyn) (implies_trans hxy hw) hd
  exact U_monotone (loop _ _ (replaceTrue_nnfClass _ hrnn) hweak hred)

/-! ## STAGE2 §6.4: eventually every extracted seed is false, equation (9). -/
/-- Equation (9) for exactly the flat G grammar. A least-size constraint is
the finite descent of §6.3; no bound on its last loss time is assumed. -/
theorem flat_eventually_false_seeds (hq : FlatQ q) (w : Word (Fin ap))
    (hfalse : ¬Sat none w (.globally q) 0)
    (hnever : ∀ n, (run (Class.ofFormula (.globally q)) w n).all ≠ Class.bot) :
    ∃ N, ∀ n, N ≤ n → ¬Holds w n (rho (rawAll (Class.ofFormula (.globally q)) w n)) := by
  let x := Class.ofFormula (.globally q)
  have hx : NNFClass x := ⟨.globally q,flatQ_nnf (q := q) hq,rfl⟩
  obtain ⟨bs,t,E,h⟩ := initial_badFlat hq w hfalse
  have hex : ∃ k, ∃ bs n E, bs.length = k ∧ BadFlatConstraint x w bs n E := ⟨bs.length,bs,t,E,rfl,h⟩
  obtain ⟨k,⟨bs,t,E,hk,h⟩,hmin⟩ := exists_least_nat hex
  have minimal : ∀ cs j F, BadFlatConstraint x w cs j F → bs.length ≤ cs.length := by
    intro cs j F hc
    apply Nat.le_of_not_gt; intro hh
    exact hmin cs.length (by omega) ⟨cs,j,F,rfl,hc⟩
  obtain ⟨N,_,hN⟩ := badFlat_flush hx h
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨F,hF,hbound⟩ := hN n hn
  have hmin' : ∀ cs j G, BadFlatConstraint x w cs j G → bs.length ≤ cs.length := minimal
  have hi := minimal_extractPass_constraint hx hF hbound hmin'
  have hC : ¬Holds w n (join (flatLoops bs) F) := join_false
    (flatLoops_false w n (fun b hb => hF.2.2.2.1 b hb n (Nat.le_refl _))) hF.2.2.2.2.1
  have hpass : ¬Holds w n (extractPass (rawAll x w n)) := by
    intro ht; exact hC ((U_holds _).mp (implication_sound hi ht))
  have hnotfinite : ¬HasTag finite (extractPass (rawAll x w n)) := by
    intro hf
    apply hpass
    apply neverBot_finite_obligation hx hnever (extractPass_nnf (rawAll_nnf hx w n)) hf
    rw [← U_rawAll hx w n]
    exact extractPass_weakens (rawAll_nnf hx w n)
  change ¬Holds w n (rho (rawAll x w n))
  simpa only [rho,hnotfinite,false_and,↓reduceIte] using hpass

/-! ## STAGE2 §6.5: the converse and its F(r) dual. -/
/-- Both inclusions for the actual complete component, including finite
remainders, suspension, and the retry on raw all-fields. -/
theorem flat_global_language (hq : FlatQ q) (w : Word (Fin ap)) :
    Inf (marks (Class.ofFormula (.globally q)) w) ↔ Sat none w (.globally q) 0 := by
  have hx : NNFClass (Class.ofFormula (.globally q)) := ⟨.globally q,flatQ_nnf (q := q) hq,rfl⟩
  constructor
  · intro hi
    apply (ofFormula_holds _).mp
    apply converse_of_eventually_false_seeds _ hx w (fun hf hn =>
      flat_eventually_false_seeds hq w (fun hs => hf ((ofFormula_holds _).mpr hs)) hn) hi
  · intro hs; exact satisfying_accepts _ hx w ((ofFormula_holds _).mpr hs)

/-- NNF duality exchanges exactly the flat r and q grammars. -/
theorem flatR_dual (hr : FlatR r) : FlatQ (Tlsf.Rewrites.to_nnf r false false) := by
  induction hr with
  | window h => exact .window (finite_nnf_polarity _ h false)
  | global h => exact .eventual (finite_nnf_polarity _ h false)
  | conj _ _ ih ih' => exact .disj ih ih'
  | disj _ _ ih ih' => exact .conj ih ih'

/-- The identical complete G(bar(r)) run with Fin(0) recognizes F(r). -/
theorem flat_eventual_language (hr : FlatR r) (w : Word (Fin ap)) :
    FinMarks (marks (Class.ofFormula (.globally (Tlsf.Rewrites.to_nnf r false false))) w) ↔
      Sat none w (.eventually r) 0 := by
  rw [complete_complement,flat_global_language (flatR_dual hr)]
  have hd := Tlsf.Rewrites.nnf_sat (len := none) (fin := false) (j := 0)
    (Or.inr rfl) (.eventually r) false w trivial
  simpa only [Tlsf.Rewrites.to_nnf,Bool.false_eq_true,↓reduceIte,Classical.not_not] using not_congr hd


/-! ## STAGE2 §8: assembling the admitted grammar. -/
theorem safety_nnf (hs : safety s) : NNF s := by
  induction s with
  | tt | ff | ap _ => trivial
  | neg f ih => cases f <;> simp_all [safety,NNF]
  | conj f g ih ih' | disj f g ih ih' | release f g ih ih' | weakUntil f g ih ih' => exact ⟨ih hs.1,ih' hs.2⟩
  | next f ih | globally f ih => exact ih hs
  | _ => contradiction

theorem cosafety_nnf (hc : cosafety c) : NNF c := by
  induction c with
  | tt | ff | ap _ => trivial
  | neg f ih => cases f <;> simp_all [cosafety,NNF]
  | conj f g ih ih' | disj f g ih ih' | «until» f g ih ih' | strongRelease f g ih ih' => exact ⟨ih hc.1,ih' hc.2⟩
  | next f ih | eventually f ih => exact ih hc
  | _ => contradiction

theorem formula_safety_tag (s : Formula (Fin ap)) (hs : safety s) : HasTag safety (Class.ofFormula s) := by
  intro a ha
  exact safety_atoms s hs a (uses_in_bound (fun σ τ hh => propEval_local s σ τ hh) ha)

def leftCoordinate (i : Fin m) : Fin (m+n) := ⟨i.val,by omega⟩
def rightCoordinate (i : Fin n) : Fin (m+n) := ⟨m+i.val,by omega⟩
def appendCoordinates (xs : Fin m → α) (ys : Fin n → α) (i : Fin (m+n)) : α :=
  if h : i.val < m then xs ⟨i.val,h⟩ else ys ⟨i.val-m,by omega⟩

theorem append_left (xs : Fin m → α) (ys : Fin n → α) (i : Fin m) :
    appendCoordinates xs ys (leftCoordinate i) = xs i := by
  simp only [appendCoordinates,leftCoordinate,Fin.isLt,↓reduceDIte]

theorem append_right (xs : Fin m → α) (ys : Fin n → α) (i : Fin n) :
    appendCoordinates xs ys (rightCoordinate i) = ys i := by
  simp only [appendCoordinates,rightCoordinate,show ¬m+i.val<m by omega,↓reduceDIte,Nat.add_sub_cancel_left]

/-- A fixed finite Boolean product of exact complete components. Negative
occurrences use the same component run through Boolean negation in β. -/
def ProductPresentation (f : Formula (Fin ap)) (xs : Fin m → Class ap) (β : Skeleton m) : Prop :=
  (∀ i w, Inf (marks (xs i) w) ↔ Holds w 0 (xs i)) ∧
    ∀ w, β (componentTruth xs w) = true ↔ Sat none w f 0

theorem singleton_presentation (h : ∀ w, Inf (marks x w) ↔ Holds w 0 x)
    (hs : ∀ w, Holds w 0 x ↔ Sat none w f 0) :
    ProductPresentation f (fun _ : Fin 1 => x) (fun z => z 0) := by
  refine ⟨fun _ => h,fun w => ?_⟩
  simpa only [componentTruth,decide_eq_true_eq] using hs w

theorem combine_presentation (hl : ProductPresentation f xs β) (hr : ProductPresentation g ys γ)
    (op : Bool) :
    ProductPresentation (if op then .conj f g else .disj f g) (appendCoordinates xs ys)
      (fun z => if op then β (fun i => z (leftCoordinate i)) && γ (fun i => z (rightCoordinate i))
        else β (fun i => z (leftCoordinate i)) || γ (fun i => z (rightCoordinate i))) := by
  constructor
  · intro i w
    unfold appendCoordinates
    split
    · exact hl.1 _ w
    · exact hr.1 _ w
  · intro w
    have hleft : (fun i => componentTruth (appendCoordinates xs ys) w (leftCoordinate i)) = componentTruth xs w := by
      funext i; simp only [componentTruth,append_left]
    have hright : (fun i => componentTruth (appendCoordinates xs ys) w (rightCoordinate i)) = componentTruth ys w := by
      funext i; simp only [componentTruth,append_right]
    cases op <;> simp only [Bool.false_eq_true,↓reduceIte,hleft,hright,
      Bool.and_eq_true,Bool.or_eq_true,hl.2 w,hr.2 w,Sat,InRange,true_and]

/-- §8's exact component/product assembly, with no premise about the general
Π₂ converse and no equivalence oracle in the grammar. -/
theorem admitted_product (hf : Admitted f) :
    ∃ (m : Nat) (xs : Fin m → Class ap) (β : Skeleton m), ProductPresentation f xs β := by
  induction hf with
  | @safety s hs =>
    refine ⟨1,fun _ => Class.ofFormula s,fun z => z 0,?_⟩
    exact singleton_presentation (fun w => safety_language _ (nnf_positive s (safety_nnf hs))
      (formula_safety_tag s hs) w) (fun _ => ofFormula_holds s)
  | @cosafety c hc =>
    refine ⟨1,fun _ => Class.ofFormula c,fun z => z 0,?_⟩
    exact singleton_presentation (fun w => cosafety_language _ ⟨c,cosafety_nnf hc,rfl⟩
      (formula_cosafety_tag c hc) w) (fun _ => ofFormula_holds c)
  | @global q hq =>
    refine ⟨1,fun _ => Class.ofFormula (.globally q),fun z => z 0,?_⟩
    exact singleton_presentation (fun w => (flat_global_language hq w).trans (ofFormula_holds _).symm)
      (fun _ => ofFormula_holds _)
  | @eventual r hr =>
    let x := Class.ofFormula (.globally (Tlsf.Rewrites.to_nnf r false false))
    refine ⟨1,fun _ => x,fun z => !(z 0),?_,?_⟩
    · intro _ w; exact (flat_global_language (flatR_dual hr) w).trans (ofFormula_holds _).symm
    · intro w
      change (!decide (Holds w 0 x)) = true ↔ _
      rw [Bool.not_eq_true',decide_eq_false_iff_not,← (flat_global_language (flatR_dual hr) w).trans (ofFormula_holds _).symm,
        ← complete_complement]
      exact flat_eventual_language hr w
  | conj _ _ ih ih' =>
    obtain ⟨m,xs,β,hx⟩ := ih; obtain ⟨n,ys,γ,hy⟩ := ih'
    exact ⟨m+n,_,_,combine_presentation hx hy true⟩
  | disj _ _ ih ih' =>
    obtain ⟨m,xs,β,hx⟩ := ih; obtain ⟨n,ys,γ,hy⟩ := ih'
    exact ⟨m+n,_,_,combine_presentation hx hy false⟩

/-- The fixed global tree recognizes the formula of any exact product. -/
theorem presentation_parity {m : Nat} {xs : Fin m → Class ap} {β : Skeleton m} (h : ProductPresentation f xs β) (T : ZTree β (fullColours m))
    (w : Word (Fin ap)) :
    (MinEven (treePriority T (productColours xs w)) ↔ Sat none w f 0) ∧
    (MaxOdd (fun n => exportBound m - treePriority T (productColours xs w) n) ↔ Sat none w f 0) := by
  have hp := (product_language xs β w (fun i => h.1 i w)).trans (h.2 w)
  exact ⟨(tree_minEven T _).trans hp,(tree_maxOdd T _).trans hp⟩

/-- STAGE2 §8 admitted-grammar theorem: one fixed complete product and one
covered global tree recognize each admitted formula, in both orientations. -/
theorem admitted_grammar (hf : Admitted f) :
    ∃ (m : Nat) (xs : Fin m → Class ap) (β : Skeleton m) (T : ZTree β (fullColours m)),
      ProductPresentation f xs β ∧ ∀ w,
        (MinEven (treePriority T (productColours xs w)) ↔ Sat none w f 0) ∧
        (MaxOdd (fun n => exportBound m - treePriority T (productColours xs w) n) ↔ Sat none w f 0) := by
  obtain ⟨m,xs,β,h⟩ := admitted_product hf
  exact ⟨m,xs,β,buildTree β (fullColours m),h,presentation_parity h _⟩

end
end Tlsf.Dpa
