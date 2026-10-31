import TlsfProofs.Dpa.Converse

/-! # STAGE2 §9: exact representation refinements
These are semantic reference algorithms. Interned C DAGs, memo keys, budgets
and error statuses still require the representation bridge in the README.
-/
namespace Tlsf.Dpa
open Class Formula
variable {ap m : Nat}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## §9.1: grouping and the original admission domain. -/
def booleanFold (op : Bool) : List (Formula α) → Formula α
  | [] => if op then .tt else .ff
  | f::fs => if op then .conj f (booleanFold op fs) else .disj f (booleanFold op fs)

theorem booleanFold_sat (op : Bool) (fs : List (Formula α)) (w : Word α) (n : Nat) :
    Sat none w (booleanFold op fs) n ↔
      if op then ∀ f, f ∈ fs → Sat none w f n else ∃ f, f ∈ fs ∧ Sat none w f n := by
  induction fs with
  | nil => cases op <;> simp [booleanFold,Sat,InRange]
  | cons f fs ih => cases op <;> simp [booleanFold,Sat,InRange,ih]

theorem booleanFold_safety (op : Bool) (hs : ∀ f, f ∈ fs → safety f) : safety (booleanFold op fs) := by
  induction fs with
  | nil => cases op <;> trivial
  | cons f fs ih => cases op <;> exact ⟨hs f (by simp),ih (fun g hg => hs g (by simp [hg]))⟩

theorem booleanFold_cosafety (op : Bool) (hc : ∀ f, f ∈ fs → cosafety f) : cosafety (booleanFold op fs) := by
  induction fs with
  | nil => cases op <;> trivial
  | cons f fs ih => cases op <;> exact ⟨hc f (by simp),ih (fun g hg => hc g (by simp [hg]))⟩

def compatibleGroups (op : Bool) (S C B T : List (Formula α)) : List (Formula α) :=
  if C = [] then booleanFold op (S++B) :: booleanFold op C :: T
  else booleanFold op S :: booleanFold op (C++B) :: T

theorem booleanFold_append_sat (op : Bool) (xs ys : List (Formula α)) (w : Word α) (n : Nat) :
    Sat none w (booleanFold op (xs++ys)) n ↔
      if op then Sat none w (booleanFold op xs) n ∧ Sat none w (booleanFold op ys) n
      else Sat none w (booleanFold op xs) n ∨ Sat none w (booleanFold op ys) n := by
  induction xs with
  | nil => cases op <;> simp [booleanFold,Sat,InRange]
  | cons f fs ih => cases op <;> simp [booleanFold,Sat,InRange,ih,and_assoc,or_assoc]

/-- Associativity, commutativity and identity justify grouping at either
outer Boolean operator. The finite group is assigned to C when C is nonempty. -/
theorem compatibleGroups_sat (op : Bool) (S C B T : List (Formula α)) (w : Word α) (n : Nat) :
    Sat none w (booleanFold op (compatibleGroups op S C B T)) n ↔
      Sat none w (booleanFold op (S++C++B++T)) n := by
  cases op <;> by_cases hC : C = [] <;>
    simp [compatibleGroups,hC,booleanFold,Sat,InRange,booleanFold_append_sat,and_assoc,or_assoc]

/-- Grouped components have both language inclusions by Stage 1, and their
fixed product/global parity construction is exact by §8. -/
theorem compatibleGroups_admitted (op : Bool) (S C B T : List (Formula (Fin ap)))
    (hs : ∀ f, f ∈ S → safety f) (hc : ∀ f, f ∈ C → cosafety f)
    (hb : ∀ f, f ∈ B → finite f) (ht : ∀ f, f ∈ T → Admitted f) :
    Admitted (booleanFold op (compatibleGroups op S C B T)) := by
  have fold_admitted : ∀ fs : List (Formula (Fin ap)), (∀ f, f ∈ fs → Admitted f) → Admitted (booleanFold op fs) := by
    intro fs hf; induction fs with
    | nil => cases op <;> exact .safety trivial
    | cons f fs ih =>
      have htail := ih (fun g hg => hf g (by simp [hg]))
      cases op
      · exact .disj (hf f (by simp)) htail
      · exact .conj (hf f (by simp)) htail
  apply fold_admitted
  unfold compatibleGroups
  split
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · apply Admitted.safety; apply booleanFold_safety
      intro g hg; exact (List.mem_append.mp hg).elim (hs g) (fun h => finite_implies_safety g (hb g h))
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact .cosafety (booleanFold_cosafety op hc)
      · exact ht f hf
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact .safety (booleanFold_safety op hs)
    · rcases List.mem_cons.mp hf with rfl | hf
      · apply Admitted.cosafety; apply booleanFold_cosafety
        intro g hg; exact (List.mem_append.mp hg).elim (hc g) (fun h => finite_implies_cosafety g (hb g h))
      · exact ht f hf

/-- The canonical decision recursion, with whole-class and supported-atom
admission supplied by the original guard in the selected mode. -/
inductive AdmissionDecision where
  | constant
  | branch (whole atom : Bool) (low high : AdmissionDecision)

def AdmissionDecision.domain : AdmissionDecision → Prop
  | .constant => True
  | .branch whole atom low high => whole = true ∨ (atom = true ∧ low.domain ∧ high.domain)

def AdmissionDecision.check : AdmissionDecision → Bool
  | .constant => true
  | .branch whole atom low high => if whole then true else atom && low.check && high.check

theorem check_admission_exact (d : AdmissionDecision) : d.check = true ↔ d.domain := by
  induction d with
  | constant => simp [AdmissionDecision.check,AdmissionDecision.domain]
  | branch whole atom low high ih ih' =>
    cases whole <;> simp [AdmissionDecision.check,AdmissionDecision.domain,ih,ih',and_assoc]

/-- Syntax inspection visits every Boolean branch, including one that a
canonical class might have absorbed. -/
def groupableSyntax (leaf : Formula α → Bool) : Formula α → Bool
  | .conj f g | .disj f g => groupableSyntax leaf f && groupableSyntax leaf g
  | f => leaf f

def booleanLeaves : Formula α → List (Formula α)
  | .conj f g | .disj f g => booleanLeaves f ++ booleanLeaves g
  | f => [f]

theorem groupable_all_leaves (leaf : Formula α → Bool) (f : Formula α) :
    groupableSyntax leaf f = true ↔ ∀ g, g ∈ booleanLeaves f → leaf g = true := by
  induction f with
  | conj f g ih ih' | disj f g ih ih' => simp [groupableSyntax,booleanLeaves,ih,ih',or_imp,forall_and]
  | _ => simp [groupableSyntax,booleanLeaves]

/-- On successful resource-bounded execution, failure of the grouping guard
falls back to the original admission recursion; it never expands its domain. -/
def factoredAdmission (d : AdmissionDecision) (groupable : Bool) : Bool :=
  if d.check then (if groupable then true else d.check) else false

theorem factoring_admission_exact (d : AdmissionDecision) (groupable : Bool) :
    factoredAdmission d groupable = true ↔ d.domain := by
  rw [← check_admission_exact]
  cases h : d.check <;> cases groupable <;> simp [factoredAdmission,h]

/-! ## §9.2: temporal distributions under arbitrary syntax contexts. -/
theorem distribute_G_context (c : Tlsf.Rewrites.Context (Fin ap)) (a b : Formula (Fin ap)) :
    Tlsf.Rewrites.Exact false (c.fill (.globally (.conj a b)))
      (c.fill (.conj (.globally a) (.globally b))) := by
  apply Tlsf.Rewrites.context_exact
  intro len hl w n hn
  have he : len = none := hl.elim (fun h => Bool.noConfusion h) id
  subst len; exact distribute_G_conj a b w n

theorem distribute_F_context (c : Tlsf.Rewrites.Context (Fin ap)) (a b : Formula (Fin ap)) :
    Tlsf.Rewrites.Exact false (c.fill (.eventually (.disj a b)))
      (c.fill (.disj (.eventually a) (.eventually b))) := by
  apply Tlsf.Rewrites.context_exact
  intro len hl w n hn
  have he : len = none := hl.elim (fun h => Bool.noConfusion h) id
  subst len; exact distribute_F_disj a b w n

/-! ## §9.3: terminally decided products. -/
theorem terminal_all_marks (xs : Fin m → Class ap) (w : Word (Fin ap)) (i : Fin m) (N : Nat) (b : Bool)
    (h : (run (xs i) w N).all = if b then Class.top else Class.bot) :
    ∀ n, N ≤ n → marks (xs i) w n = b := by
  have hstates : ∀ k, (run (xs i) w (N+k)).all = if b then Class.top else Class.bot := by
    intro k; induction k with
    | zero => exact h
    | succ k ih =>
      change (transition (w (N+k)) (run (xs i) w (N+k))).target.all = _
      cases b
      · exact (false_transition _ _ ih).1
      · exact (true_transition _ _ ih).1
  intro n hn
  have hs := hstates (n-N)
  rw [Nat.add_sub_cancel' hn] at hs
  cases b
  · exact (false_transition _ _ hs).2
  · exact (true_transition _ _ hs).2

theorem terminal_recurrent_colour (xs : Fin m → Class ap) (w : Word (Fin ap)) (i : Fin m) (N : Nat) (b : Bool)
    (h : (run (xs i) w N).all = if b then Class.top else Class.bot) :
    recurrentColours (productColours xs w) i = b := by
  have hh := terminal_all_marks xs w i N b h
  cases b
  · simp only [recurrentColours,decide_eq_false_iff_not,product_colour]
    exact (complete_complement _).mp ⟨N,hh⟩
  · simp only [recurrentColours,decide_eq_true_eq,product_colour]
    intro M; exact ⟨max M N,Nat.le_max_left _ _,hh _ (Nat.le_max_right _ _)⟩

def fillConstants (known : Fin m → Option Bool) (z : Fin m → Bool) : Fin m → Bool :=
  fun i => (known i).getD (z i)

/-- Only terminal all-fields supply constants. Arbitrary complemented
occurrences are handled by the unchanged Boolean function β. -/
theorem terminal_product_decided (xs : Fin m → Class ap) (β : Skeleton m) (w : Word (Fin ap))
    (N : Nat) (known : Fin m → Option Bool) (b : Bool)
    (hknown : ∀ i t, known i = some t → (run (xs i) w N).all = if t then Class.top else Class.bot)
    (hconstant : ∀ z, β (fillConstants known z) = b) :
    EmersonLei β (productColours xs w) ↔ b = true := by
  have he : fillConstants known (recurrentColours (productColours xs w)) = recurrentColours (productColours xs w) := by
    funext i; cases hk : known i with
    | none => simp [fillConstants,hk]
    | some t => simpa only [fillConstants,hk,Option.getD_some] using
        (terminal_recurrent_colour xs w i N t (hknown i t hk)).symm
  have hh := hconstant (recurrentColours (productColours xs w))
  rw [he] at hh
  exact hh ▸ Iff.rfl

/-- An absorbing suffix has max-odd truth t for priorities P and P−1.
The entering priority and all earlier edges are arbitrary. -/
theorem absorbing_maxOdd (p : Nat → Nat) (P N : Nat) (b : Bool) (hP : P%2=1)
    (h : ∀ n, N ≤ n → p n = if b then P else P-1) : MaxOdd p ↔ b = true := by
  constructor
  · rintro ⟨k,hk,hi,_⟩
    obtain ⟨n,hn,he⟩ := hi N
    have hh := h n hn
    cases b <;> simp_all <;> omega
  · intro hb; subst b
    refine ⟨P,hP,?_,N,fun n hn => by have hh := h n hn; simp only [↓reduceIte] at hh; omega⟩
    intro M; exact ⟨max M N,Nat.le_max_left _ _,h _ (Nat.le_max_right _ _)⟩

/-- Replacement by the reserved absorbing product preserves acceptance
whenever substitution in the fixed β yields a Boolean constant. -/
theorem terminal_absorption (xs : Fin m → Class ap) (β : Skeleton m) (T : ZTree β (fullColours m))
    (w : Word (Fin ap)) (N : Nat) (known : Fin m → Option Bool) (b : Bool) (p : Nat → Nat)
    (hknown : ∀ i t, known i = some t → (run (xs i) w N).all = if t then Class.top else Class.bot)
    (hconstant : ∀ z, β (fillConstants known z) = b)
    (hp : ∀ n, N ≤ n → p n = if b then exportBound m else exportBound m-1) :
    MaxOdd (fun n => exportBound m - treePriority T (productColours xs w) n) ↔ MaxOdd p :=
  (tree_maxOdd T _).trans ((terminal_product_decided xs β w N known b hknown hconstant).trans
    (absorbing_maxOdd p (exportBound m) N b (exportBound_odd m) hp).symm)

/-! ## §9.4: unfolding under a current-AP cube, with frozen continuations. -/
abbrev APCube (ap : Nat) := Fin ap → Option Bool

def CubeMatches (C : APCube ap) (σ : Assignment ap) : Prop :=
  ∀ p b, C p = some b → σ (.ap p) = b

def careAssignment (C : APCube ap) (σ : Assignment ap) : Assignment ap
  | .ap p => (C p).getD (σ (.ap p))
  | a => σ a

/-- Cofactoring traverses only Boolean syntax and current APs. Every modal
atom, including X, remains frozen. -/
def restrictCurrent (C : APCube ap) : Formula (Fin ap) → Formula (Fin ap)
  | .tt => .tt | .ff => .ff
  | .ap p => match C p with | none => .ap p | some true => .tt | some false => .ff
  | .neg f => .neg (restrictCurrent C f)
  | .conj f g => .conj (restrictCurrent C f) (restrictCurrent C g)
  | .disj f g => .disj (restrictCurrent C f) (restrictCurrent C g)
  | .impl f g => .impl (restrictCurrent C f) (restrictCurrent C g)
  | .equiv f g => .equiv (restrictCurrent C f) (restrictCurrent C g)
  | a => a

theorem restrictCurrent_eval (C : APCube ap) (f : Formula (Fin ap)) (σ : Assignment ap) :
    propEval σ (restrictCurrent C f) = propEval (careAssignment C σ) f := by
  induction f with
  | tt | ff => rfl
  | ap p => cases hc : C p with
    | none => simp [restrictCurrent,careAssignment,hc,propEval]
    | some b => cases b <;> simp [restrictCurrent,careAssignment,hc,propEval]
  | neg f ih => simp only [restrictCurrent,propEval,ih]
  | conj f g ih ih' | disj f g ih ih' | impl f g ih ih' | equiv f g ih ih' =>
    simp only [restrictCurrent,propEval,ih,ih']
  | _ => rfl

def restrictClass (C : APCube ap) (x : Class ap) : Class ap :=
  ⟨fun σ => x (careAssignment C σ),restrictCurrent C x.repr,by
    funext σ; rw [restrictCurrent_eval,repr_eval]⟩

def unfoldCare (C : APCube ap) (x : Class ap) : Class ap := restrictClass C (U x)

theorem careAssignment_matches (h : CubeMatches C σ) : careAssignment C σ = σ := by
  funext a; cases a <;> try rfl
  case ap p => cases hc : C p with
    | none => simp [careAssignment,hc]
    | some b => simpa [careAssignment,hc] using (h p b hc).symm

/-- Simultaneous syntax/class care invariant: agreement with frozen U on
all independent modal valuations satisfying the current-AP cube. -/
theorem unfolding_care_exact (h : CubeMatches C σ) : unfoldCare C x σ = U x σ := by
  change U x (careAssignment C σ) = U x σ
  rw [careAssignment_matches h]

theorem unfolding_syntax_care_exact (f : Formula (Fin ap)) (h : CubeMatches C σ) :
    propEval σ (restrictCurrent C (unfoldSyntax f)) = propEval σ (unfoldSyntax f) := by
  rw [restrictCurrent_eval,careAssignment_matches h]

/-- At the root the care result is propositionally identical to U. -/
theorem unfolding_care_root (x : Class ap) : unfoldCare (fun _ => none) x = U x := by
  apply Class.ext; intro σ
  exact unfolding_care_exact (C := fun _ => none) (by intro p b hb; contradiction)

theorem care_finite_return (hf : HasTag finite x) (h : CubeMatches C σ) : unfoldCare C x σ = x σ := by
  rw [unfolding_care_exact h,finite_U_fixed hf]

theorem care_frozen_next (C : APCube ap) (f : Formula (Fin ap)) : restrictCurrent C (.next f) = .next f := rfl

def setCube (C : APCube ap) (p : Fin ap) (b : Bool) : APCube ap := fun q => if q=p then some b else C q

theorem cube_branch (h : CubeMatches C σ) (p : Fin ap) : CubeMatches (setCube C p (σ (.ap p))) σ := by
  intro q b hb
  by_cases hq : q=p
  · subst q; simp only [setCube,↓reduceIte,Option.some.injEq] at hb; exact hb
  · apply h q b; simpa [setCube,hq] using hb

/-- Shannon recombination of AP low/high traversals under their respective
care cubes. Modal branches use the same cube and the same Boolean identity. -/
theorem care_shannon (C : APCube ap) (σ : Assignment ap) (p : Fin ap) (low high : Class ap)
    (h : CubeMatches C σ) :
    (if σ (.ap p) then unfoldCare (setCube C p true) high σ else unfoldCare (setCube C p false) low σ) =
      (if σ (.ap p) then U high σ else U low σ) := by
  have hh := cube_branch h p
  cases hp : σ (.ap p)
  · simpa only [hp,Bool.false_eq_true,↓reduceIte] using unfolding_care_exact (x := low) (by simpa only [hp] using hh)
  · simpa only [hp,↓reduceIte] using unfolding_care_exact (x := high) (by simpa only [hp] using hh)

theorem care_modal_shannon (C : APCube ap) (σ : Assignment ap) (a : Formula (Fin ap))
    (low high : Class ap) (h : CubeMatches C σ) :
    (if unfoldCare C (Class.ofFormula a) σ then unfoldCare C high σ else unfoldCare C low σ) =
      (if U (Class.ofFormula a) σ then U high σ else U low σ) := by
  rw [unfolding_care_exact h,unfolding_care_exact h,unfolding_care_exact h]

/-! ## §9.5: support tags, cached bounds and exact fallback. -/
abbrev TagBits (τ : Type) := τ → Bool

def BitsBelow (L H : TagBits τ) : Prop := ∀ t, L t = true → H t = true

def bitsMeet (x y : TagBits τ) : TagBits τ := fun t => x t && y t

theorem bounds_intersection (hx : BitsBelow L T ∧ BitsBelow T H)
    (hy : BitsBelow L' T' ∧ BitsBelow T' H') :
    BitsBelow (bitsMeet L L') (bitsMeet T T') ∧ BitsBelow (bitsMeet T T') (bitsMeet H H') := by
  constructor
  · intro t ht; exact Bool.and_eq_true_iff.mpr ⟨hx.1 t (Bool.and_eq_true_iff.mp ht).1,hy.1 t (Bool.and_eq_true_iff.mp ht).2⟩
  · intro t ht; exact Bool.and_eq_true_iff.mpr ⟨hx.2 t (Bool.and_eq_true_iff.mp ht).1,hy.2 t (Bool.and_eq_true_iff.mp ht).2⟩

def maskHit (T M : TagBits τ) : Prop := ∃ t, T t = true ∧ M t = true

def boundedTagTest (L T H M : TagBits τ) : Bool :=
  if decide (maskHit L M) then true else if decide (maskHit H M) then decide (maskHit T M) else false

/-- Every mask, including safety|co-safety, gives exactly the original test.
The undecided case calls the exact predicate unchanged. -/
theorem bounded_tag_test_exact {τ : Type} {L T H : TagBits τ} (h : BitsBelow L T ∧ BitsBelow T H) (M : TagBits τ) :
    boundedTagTest L T H M = decide (maskHit T M) := by
  apply fragment_bounds_exact (decide (maskHit L M)) (decide (maskHit T M)) (decide (maskHit H M))
  · simp only [decide_eq_true_eq]; rintro ⟨t,ht,hm⟩; exact ⟨t,h.1 t ht,hm⟩
  · simp only [decide_eq_true_eq]; rintro ⟨t,ht,hm⟩; exact ⟨t,h.2 t ht,hm⟩

/-- Boolean support absorption can add a syntax tag, and cannot invalidate a
cached lower bound whose supporting atoms are still a sound superset. -/
theorem support_pruning_tag (hxy : ∀ a, Uses y a → Uses x a) (hx : HasTag tag x) : HasTag tag y :=
  fun a ha => hx a (hxy a ha)

/-- A refined atom preserves every prior sound lower bound. -/
theorem cached_lower_refinement (hL : BitsBelow L T) (hrefine : BitsBelow T T') : BitsBelow L T' :=
  fun t ht => hrefine t (hL t ht)

/-- Exact fallback preserves the safety-first order and all subsequent table
and extractor decisions. It does not replace exact tags by conservative tags. -/
theorem exact_tests_preserve_order (s c s' c' : Bool) (hs : s'=s) (hc : c'=c) :
    (if s' then 0 else if c' then 1 else 2) = (if s then 0 else if c then 1 else 2) := by rw [hs,hc]


/-- The Σ₂ grammar dual to the intended Π₂ grammar; this is a syntax tag,
not an additional component-language theorem. -/
inductive Sigma2 : Formula α → Prop where
  | base (h : safety s) : Sigma2 s
  | conj (h : Sigma2 f) (h' : Sigma2 g) : Sigma2 (.conj f g)
  | disj (h : Sigma2 f) (h' : Sigma2 g) : Sigma2 (.disj f g)
  | next (h : Sigma2 f) : Sigma2 (.next f)
  | eventual (h : Sigma2 f) : Sigma2 (.eventually f)
  | until (h : Sigma2 f) (h' : Sigma2 g) : Sigma2 (.until f g)
  | strongRelease (h : Sigma2 f) (h' : Sigma2 g) : Sigma2 (.strongRelease f g)

theorem pi2_atoms {f : Formula (Fin ap)} (h : Pi2 f) : ∀ a, a ∈ modalAtoms f → Pi2 a := by
  induction h with
  | base hc => intro a ha; exact .base (cosafety_atoms _ hc a ha)
  | conj _ _ ih ih' | disj _ _ ih ih' => intro a ha; exact (List.mem_append.mp ha).elim (ih a) (ih' a)
  | next h _ih => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .next h
  | global h _ih => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .global h
  | release h h' _ih _ih' => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .release h h'
  | weakUntil h h' _ih _ih' => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .weakUntil h h'

theorem sigma2_atoms {f : Formula (Fin ap)} (h : Sigma2 f) : ∀ a, a ∈ modalAtoms f → Sigma2 a := by
  induction h with
  | base hs => intro a ha; exact .base (safety_atoms _ hs a ha)
  | conj _ _ ih ih' | disj _ _ ih ih' => intro a ha; exact (List.mem_append.mp ha).elim (ih a) (ih' a)
  | next h _ih => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .next h
  | eventual h _ih => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .eventual h
  | «until» h h' _ih _ih' => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .until h h'
  | strongRelease h h' _ih _ih' => intro a ha; have he := List.mem_singleton.mp ha; subst a; exact .strongRelease h h'

inductive FragmentTag where
  | finite | safety | cosafety | pi2 | sigma2

def fragmentSyntax : FragmentTag → Formula α → Prop
  | .finite => finite | .safety => safety | .cosafety => cosafety | .pi2 => Pi2 | .sigma2 => Sigma2

/-- Structural syntax memberships supply sound initial lower bounds, even
when Boolean canonicalization later removes supported atoms. -/
theorem syntax_tag_lower (f : Formula (Fin ap)) (t : FragmentTag) (h : fragmentSyntax t f) :
    HasTag (fragmentSyntax t) (Class.ofFormula f) := by
  intro a ha
  have hm := uses_in_bound (fun σ τ hh => propEval_local f σ τ hh) ha
  cases t with
  | finite => exact finite_atoms f h a hm
  | safety => exact safety_atoms f h a hm
  | cosafety => exact cosafety_atoms f h a hm
  | pi2 => exact pi2_atoms h a hm
  | sigma2 => exact sigma2_atoms h a hm

/-- The actual modal operator excludes finite and the impossible safety or
co-safety bit; AP and X impose no upper restriction on operand tags. -/
def operatorTagUpper (t : FragmentTag) : Formula α → Prop
  | .eventually _ | .until _ _ | .strongRelease _ _ => t ≠ .finite ∧ t ≠ .safety
  | .globally _ | .release _ _ | .weakUntil _ _ => t ≠ .finite ∧ t ≠ .cosafety
  | _ => True

theorem syntax_operator_upper (a : Formula α) (t : FragmentTag) (h : fragmentSyntax t a) : operatorTagUpper t a := by
  cases t with
  | finite => cases a <;> simp_all [operatorTagUpper,fragmentSyntax,finite]
  | safety => cases a <;> simp_all [operatorTagUpper,fragmentSyntax,safety]
  | cosafety => cases a <;> simp_all [operatorTagUpper,fragmentSyntax,cosafety]
  | pi2 => cases a <;> simp [operatorTagUpper]
  | sigma2 => cases a <;> simp [operatorTagUpper]

theorem setAtom_comm (σ : Assignment ap) (a t : Formula (Fin ap)) (b v : Bool) (hne : t ≠ a) :
    setAtom (setAtom σ t v) a b = setAtom (setAtom σ a b) t v := by
  funext q
  by_cases hq : q=a <;> by_cases ht : q=t <;> simp_all [setAtom]

theorem cofactor_support {low x : Class ap} {a t : Formula (Fin ap)} {b : Bool} (hl : ∀ σ, low σ = x (setAtom σ a b)) (hu : Uses low t) : Uses x t := by
  apply Classical.byContradiction; intro hn
  obtain ⟨σ,v,hv⟩ := hu
  apply hv
  rw [hl,hl]
  by_cases ht : t=a
  · subst t; apply congrArg x; funext q; simp [setAtom]; split <;> simp_all
  · rw [setAtom_comm σ a t b v ht,not_uses hn]

/-- Shannon support gives exactly the original three-way tag intersection:
supported top atom, low cofactor and high cofactor. -/
theorem tags_shannon_intersection {x low high : Class ap} {a : Formula (Fin ap)} (ha : Uses x a)
    (hl : ∀ σ, low σ = x (setAtom σ a false))
    (hh : ∀ σ, high σ = x (setAtom σ a true)) :
    HasTag tag x ↔ tag a ∧ HasTag tag low ∧ HasTag tag high := by
  constructor
  · intro h; exact ⟨h a ha,fun t ht => h t (cofactor_support hl ht),fun t ht => h t (cofactor_support hh ht)⟩
  · rintro ⟨hta,htl,hth⟩ t ht
    by_cases hta' : t=a
    · simpa only [hta'] using hta
    · have hs : Uses low t ∨ Uses high t := by
        apply Classical.byContradiction; intro hn
        have hnl : ¬Uses low t := fun h => hn (Or.inl h)
        have hnh : ¬Uses high t := fun h => hn (Or.inr h)
        have expand : ∀ σ, x σ = if σ a then high σ else low σ := by
          intro σ
          have hid : setAtom σ a (σ a) = σ := by funext q; by_cases he : q=a <;> simp_all [setAtom]
          cases hb : σ a
          · simp only [Bool.false_eq_true,↓reduceIte]; rw [hl,← hb,hid]
          · simp only [↓reduceIte]; rw [hh,← hb,hid]
        obtain ⟨σ,v,hv⟩ := ht
        apply hv
        rw [expand,expand,show setAtom σ t v a = σ a by simp [setAtom,Ne.symm hta'],not_uses hnl,not_uses hnh]
      exact hs.elim (htl t) (hth t)


/-- §9.1's grouped construction has the original formula's infinite-word
language, with the same fixed product and global parity update. -/
theorem compatibleGroups_parity (op : Bool) (S C B T : List (Formula (Fin ap)))
    (hs : ∀ f, f ∈ S → safety f) (hc : ∀ f, f ∈ C → cosafety f)
    (hb : ∀ f, f ∈ B → finite f) (ht : ∀ f, f ∈ T → Admitted f) :
    ∃ (m : Nat) (xs : Fin m → Class ap) (β : Skeleton m) (tree : ZTree β (fullColours m)),
      ∀ w, (MinEven (treePriority tree (productColours xs w)) ↔
        Sat none w (booleanFold op (S++C++B++T)) 0) ∧
        (MaxOdd (fun n => exportBound m - treePriority tree (productColours xs w) n) ↔
        Sat none w (booleanFold op (S++C++B++T)) 0) := by
  obtain ⟨m,xs,β,tree,_,h⟩ := admitted_grammar (compatibleGroups_admitted op S C B T hs hc hb ht)
  exact ⟨m,xs,β,tree,fun w => ⟨(h w).1.trans (compatibleGroups_sat op S C B T w 0),
    (h w).2.trans (compatibleGroups_sat op S C B T w 0)⟩⟩

end
end Tlsf.Dpa
