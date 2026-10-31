import TlsfProofs.Dpa.Product

/-!
# STAGE2 §5: covered trees, ordinary updates and parity export

Reference construction: Casares–Colcombet–Fijalkow, ICALP'21,
arXiv:2011.13041; Casares et al., TACAS'22, Proposition 1. The latter uses
Support, NextBranch, and Depth(Support) for transition-based EL automata.
The results below do not substitute a citation for the recurrent-path proof.
-/
namespace Tlsf.Dpa
variable {m : Nat}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev ColourSet (m : Nat) := Fin m → Bool

def Subset (x y : ColourSet m) : Prop := ∀ i, x i = true → y i = true

theorem subset_refl (x : ColourSet m) : Subset x x := fun _ h => h
theorem subset_trans (h : Subset x y) (h' : Subset y z) : Subset x z := fun i hi => h' i (h i hi)
theorem subset_antisymm (h : Subset x y) (h' : Subset y x) : x = y := by
  funext i; cases hx : x i <;> cases hy : y i <;> simp_all [Subset]

/-- An inclusion-maximal opposite-acceptance subset of C. Such a subset is
proper: the opposite-acceptance requirement itself excludes C. -/
def MaximalOpposite (α : Skeleton m) (C M : ColourSet m) : Prop :=
  Subset M C ∧ α M ≠ α C ∧
    ∀ N, Subset N C → α N ≠ α C → Subset M N → N = M

theorem maximal_proper (h : MaximalOpposite α C M) : M ≠ C := by
  intro he; exact h.2.1 (congrArg α he)

/-- The conjunction of the builder's blocking clauses: X must not be a
subset of any previously recorded model. -/
def Unblocked (recorded : List (ColourSet m)) (X : ColourSet m) : Prop :=
  ∀ M, M ∈ recorded → ¬Subset X M

theorem unblocked_upward (h : Unblocked recorded X) (hxy : Subset X Y) : Unblocked recorded Y :=
  fun M hM hy => h M hM (subset_trans hxy hy)

/-- An ascent maximal under the accumulated clauses is maximal for the
original query: all blocking clauses are upward closed. -/
theorem maximal_under_blocks (α : Skeleton m) (C X : ColourSet m)
    (hXC : Subset X C) (hopp : α X ≠ α C) (hb : Unblocked recorded X)
    (hmax : ∀ Y, Subset Y C → α Y ≠ α C → Unblocked recorded Y → Subset X Y → Y = X) :
    MaximalOpposite α C X := by
  exact ⟨hXC, hopp, fun Y hYC ho hXY => hmax Y hYC ho (unblocked_upward hb hXY) hXY⟩

/-- Abstract SAT-builder completeness. If all outputs are maximal and the
remaining blocked query is unsatisfiable, every maximal model was output.
The statement includes the empty colour set and does not assume greedy
single-bit ascent. SAT calls and resource exhaustion are outside this theorem. -/
theorem maximal_builder_complete (α : Skeleton m) (C : ColourSet m)
    (recorded : List (ColourSet m))
    (hsound : ∀ M, M ∈ recorded → MaximalOpposite α C M)
    (hstop : ¬∃ X, Subset X C ∧ α X ≠ α C ∧ Unblocked recorded X)
    (M : ColourSet m) (hM : MaximalOpposite α C M) : M ∈ recorded := by
  apply Classical.byContradiction; intro hn
  apply hstop
  refine ⟨M, hM.1, hM.2.1, ?_⟩
  intro N hN hMN
  have hmaxN := hsound N hN
  have he := hM.2.2 N hmaxN.1 hmaxN.2.1 hMN
  exact hn (he ▸ hN)

/-- The final set-theoretic step of the recurrent-anchor argument, with the
child-cover and no-containing-child obligations explicit. -/
theorem recurrent_set_acceptance (α : Skeleton m) (C S : ColourSet m)
    (children : List (ColourSet m)) (_hSC : Subset S C)
    (hcover : α S ≠ α C → ∃ D, D ∈ children ∧ Subset S D)
    (hno : ∀ D, D ∈ children → ¬Subset S D) : α S = α C := by
  apply Classical.byContradiction; intro hn
  obtain ⟨D, hD, hSD⟩ := hcover hn
  exact hno D hD hSD

/-- The smallest odd P strictly greater than m+1, also used by C's export. -/
def exportBound (m : Nat) : Nat := 2 * ((m+2)/2) + 1

theorem exportBound_odd (m : Nat) : exportBound m % 2 = 1 := by unfold exportBound; omega

theorem exportBound_large (m : Nat) : m+1 < exportBound m := by unfold exportBound; omega

/-- STAGE2 §5: for any bounded priority stream and odd P, P−p exchanges
min-even and max-odd. This is independent of tree or component correctness. -/
theorem parity_export (p : Nat → Nat) (P : Nat) (hP : P % 2 = 1)
    (hp : ∀ n, p n ≤ P) : MinEven p ↔ MaxOdd (fun n => P - p n) := by
  constructor
  · rintro ⟨k, hk, hi, N, hN⟩
    have hkP : k ≤ P := by
      obtain ⟨n, _, he⟩ := hi 0
      have ht := hp n; omega
    refine ⟨P-k, by omega, ?_, N, ?_⟩
    · intro M; obtain ⟨n, hn, he⟩ := hi M
      exact ⟨n, hn, by change P - p n = P - k; rw [he]⟩
    · intro n hn; have ht := hN n hn
      change P - p n ≤ P - k
      omega
  · rintro ⟨r, hr, hi, N, hN⟩
    dsimp only at hi hN
    have hrP : r ≤ P := by
      obtain ⟨n, _, he⟩ := hi 0
      omega
    refine ⟨P-r, by omega, ?_, N, ?_⟩
    · intro M; obtain ⟨n, hn, he⟩ := hi M
      exact ⟨n, hn, by have ht := hp n; omega⟩
    · intro n hn; have ht := hN n hn; have hb := hp n; omega

/-- All ordinary exported priorities are positive under the stated depth bound. -/
theorem exported_positive (h : p ≤ m+1) : 0 < exportBound m - p := by
  have hb := exportBound_large m
  omega

/-- All Boolean colour vectors, including the unique empty vector. -/
def colourVectors : (m : Nat) → List (ColourSet m)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (colourVectors n).flatMap (fun X => [Fin.cases false X, Fin.cases true X])

theorem mem_colourVectors (X : ColourSet m) : X ∈ colourVectors m := by
  induction m with
  | zero =>
    simp only [colourVectors, List.mem_singleton]
    funext i; exact Fin.elim0 i
  | succ m ih =>
    let tail : ColourSet m := fun i => X i.succ
    have ht := ih tail
    have he : Fin.cases (X 0) tail = X := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    simp only [colourVectors, List.mem_flatMap]
    refine ⟨tail, ht, ?_⟩
    cases hv : X 0
    · simp only [hv] at he
      simp [← he]
    · simp only [hv] at he
      simp [← he]

/-- Finite-poset maximality, stated directly over a finite candidate list. -/
theorem list_maximal (xs : List (ColourSet m)) (P : ColourSet m → Prop)
    (hne : ∃ X, X ∈ xs ∧ P X) :
    ∃ M, M ∈ xs ∧ P M ∧ ∀ Y, Y ∈ xs → P Y → Subset M Y → Y = M := by
  induction xs with
  | nil => obtain ⟨X, hX, _⟩ := hne; contradiction
  | cons a xs ih =>
    by_cases htail : ∃ X, X ∈ xs ∧ P X
    · obtain ⟨M, hM, hPM, hmax⟩ := ih htail
      by_cases htake : P a ∧ Subset M a
      · refine ⟨a, by simp, htake.1, ?_⟩
        intro Y hY hPY haY
        rcases List.mem_cons.mp hY with he | hY
        · exact he
        · have he := hmax Y hY hPY (subset_trans htake.2 haY)
          subst Y
          exact subset_antisymm htake.2 haY
      · refine ⟨M, by simp [hM], hPM, ?_⟩
        intro Y hY hPY hMY
        rcases List.mem_cons.mp hY with he | hY
        · subst Y; exact False.elim (htake ⟨hPY, hMY⟩)
        · exact hmax Y hY hPY hMY
    · obtain ⟨X, hX, hPX⟩ := hne
      have he : X = a := by
        rcases List.mem_cons.mp hX with he | hX
        · exact he
        · exact False.elim (htail ⟨X, hX, hPX⟩)
      subst X
      refine ⟨a, by simp, hPX, ?_⟩
      intro Y hY hPY _
      rcases List.mem_cons.mp hY with he | hY
      · exact he
      · exact False.elim (htail ⟨Y, hY, hPY⟩)

/-- Every opposite subset extends to an inclusion-maximal opposite subset. -/
theorem maximal_opposite_extension (α : Skeleton m) (C S : ColourSet m)
    (hSC : Subset S C) (hopp : α S ≠ α C) :
    ∃ M, MaximalOpposite α C M ∧ Subset S M := by
  let P := fun X => Subset X C ∧ α X ≠ α C ∧ Subset S X
  obtain ⟨M, _, hM, hmax⟩ := list_maximal (colourVectors m) P
    ⟨S, mem_colourVectors S, hSC, hopp, subset_refl S⟩
  refine ⟨M, ⟨hM.1, hM.2.1, ?_⟩, hM.2.2⟩
  intro Y hYC ho hMY
  exact hmax Y (mem_colourVectors Y) ⟨hYC, ho, subset_trans hM.2.2 hMY⟩ hMY

def colourCard (X : ColourSet m) : Nat := ((List.finRange m).filter X).length

theorem colourCard_strict (h : Subset X C) (hne : X ≠ C) : colourCard X < colourCard C := by
  apply filter_strict
  · intro i _ hi; exact h i hi
  · have hlost : ∃ i, C i = true ∧ X i = false := by
      apply Classical.byContradiction; intro hn
      apply hne
      apply subset_antisymm h
      intro i hi
      cases hx : X i
      · exact False.elim (hn ⟨i, hi, hx⟩)
      · rfl
    obtain ⟨i, hi, hx⟩ := hlost
    exact ⟨i, by simp, hi, hx⟩

theorem colourCard_le (X : ColourSet m) : colourCard X ≤ m := by
  have h := List.length_filter_le X (List.finRange m)
  simpa only [colourCard, List.length_finRange] using h

/-- Intrinsically covered Zielonka trees. Equal labels may share a subtree;
paths still retain their distinct child occurrences. -/
inductive ZTree (α : Skeleton m) : ColourSet m → Type where
  | node (C : ColourSet m) (children : List (ColourSet m))
      (sound : ∀ M, M ∈ children → MaximalOpposite α C M)
      (cover : ∀ M, MaximalOpposite α C M → M ∈ children)
      (subtree : ∀ M, M ∈ children → ZTree α M) : ZTree α C

/-- A reference builder using exhaustive semantic vectors. This verifies the
mathematical tree; `maximal_builder_complete` treats the abstract SAT builder. -/
def buildTree (α : Skeleton m) (C : ColourSet m) : ZTree α C :=
  let children := (colourVectors m).filter (fun M => decide (MaximalOpposite α C M))
  ZTree.node C children
    (fun _ h => of_decide_eq_true (List.mem_filter.mp h).2)
    (fun M h => List.mem_filter.mpr ⟨mem_colourVectors M, decide_eq_true h⟩)
    (fun M _h => buildTree α M)
termination_by colourCard C
decreasing_by
  have hm : MaximalOpposite α C M := of_decide_eq_true (List.mem_filter.mp _h).2
  exact colourCard_strict hm.1 (maximal_proper hm)

/-- The children cover every opposite subset, including the empty subset. -/
theorem child_cover (α : Skeleton m) (C S : ColourSet m)
    (children : List (ColourSet m))
    (hcover : ∀ M, MaximalOpposite α C M → M ∈ children)
    (hSC : Subset S C) (hopp : α S ≠ α C) :
    ∃ D, D ∈ children ∧ Subset S D := by
  obtain ⟨D, hD, hSD⟩ := maximal_opposite_extension α C S hSC hopp
  exact ⟨D, hcover D hD, hSD⟩

/-- Static conclusion of the recurrent-set proof for the actual covered
children. The stream/rotation argument must establish `hno`. -/
theorem covered_recurrent_acceptance (α : Skeleton m) (C S : ColourSet m)
    (children : List (ColourSet m))
    (hcover : ∀ M, MaximalOpposite α C M → M ∈ children)
    (hSC : Subset S C) (hno : ∀ D, D ∈ children → ¬Subset S D) : α S = α C :=
  recurrent_set_acceptance α C S children hSC (child_cover α C S children hcover hSC) hno

namespace ZTree
variable {α : Skeleton m} {C : ColourSet m}

def leftmost : {C : ColourSet m} → ZTree α C → List Nat
  | _, .node _ [] _ _ _ => []
  | _, .node _ (M :: rest) _ _ subtree => 0 :: leftmost (subtree M (by simp))

def ValidPath : {C : ColourSet m} → ZTree α C → List Nat → Prop
  | _, .node _ children _ _ subtree, [] => children = []
  | _, .node _ children _ _ subtree, i :: rest =>
      ∃ hi : i < children.length, ValidPath (subtree children[i] (List.getElem_mem hi)) rest

theorem leftmost_valid (T : ZTree α C) : ValidPath T (leftmost T) := by
  induction T with
  | node C children hs hc subtree ih =>
    cases children with
    | nil => rfl
    | cons M rest =>
      exact ⟨by simp, ih M (by simp)⟩

/-- Strict label decrease bounds every leaf path by the number of colours. -/
theorem path_length_le (T : ZTree α C) (path : List Nat) (hv : ValidPath T path) :
    path.length ≤ colourCard C := by
  induction path generalizing C with
  | nil => exact Nat.zero_le _
  | cons i rest ih =>
    cases T with
    | node C children hs hc subtree =>
      obtain ⟨hi, hrest⟩ := hv
      have hlen := ih (subtree children[i] (List.getElem_mem hi)) hrest
      have hmax := hs children[i] (List.getElem_mem hi)
      have hlt := colourCard_strict hmax.1 (maximal_proper hmax)
      simp only [List.length_cons]; omega

/-- The ordinary one-sibling update. Failure denotes an invalid path or an
edge outside the root label, never a transition of the complete global tree.
The reported depth is the first containing anchor. There is no sibling skip. -/
def step : {C : ColourSet m} → ZTree α C → List Nat → ColourSet m → Option (List Nat × Nat)
  | C, .node _ children _ _ subtree, path, E =>
    if Subset E C then
      match path with
      | [] => if children = [] then some ([], 0) else none
      | i :: rest =>
        if hi : i < children.length then
          if Subset E children[i] then
            (step (subtree children[i] (List.getElem_mem hi)) rest E).map
              (fun r => (i :: r.1, r.2+1))
          else
            let j := (i+1) % children.length
            have hj : j < children.length := Nat.mod_lt _ (by omega)
            some (j :: leftmost (subtree children[j] (List.getElem_mem hj)), 0)
        else none
    else none
termination_by _ _ path _ => path.length

theorem step_valid (T : ZTree α C) (path : List Nat) (E : ColourSet m)
    (hv : ValidPath T path) (hEC : Subset E C) :
    ∃ r, step T path E = some r ∧ ValidPath T r.1 ∧ r.2 ≤ path.length := by
  induction path generalizing C with
  | nil =>
    cases T with
    | node C children hs hc subtree =>
      change children = [] at hv
      subst children
      exact ⟨([], 0), by simp [step, hEC], rfl, Nat.le_refl _⟩
  | cons i rest ih =>
    cases T with
    | node C children hs hc subtree =>
      obtain ⟨hi, hrest⟩ := hv
      by_cases hchild : Subset E children[i]
      · obtain ⟨⟨path', depth⟩, hstep, hvalid, hdepth⟩ :=
          ih (subtree children[i] (List.getElem_mem hi)) hrest hchild
        refine ⟨(i :: path', depth+1), ?_, ⟨hi, hvalid⟩, by simp only [List.length_cons]; omega⟩
        simp only [step, hEC, hi, hchild, ↓reduceDIte, ↓reduceIte, hstep, Option.map_some]
      · let j := (i+1) % children.length
        have hj : j < children.length := Nat.mod_lt _ (by omega)
        refine ⟨(j :: leftmost (subtree children[j] (List.getElem_mem hj)), 0), ?_,
          ⟨hj, leftmost_valid _⟩, Nat.zero_le _⟩
        simp only [step, hEC, hi, hchild, ↓reduceDIte, ↓reduceIte]
        rfl

/-- Total presentation of the partial update; its default is unreachable on
valid leaf paths and edges contained in the root. -/
def advance (T : ZTree α C) (path : List Nat) (E : ColourSet m) : List Nat × Nat :=
  (step T path E).getD (path, 0)

theorem advance_valid (T : ZTree α C) (path : List Nat) (E : ColourSet m)
    (hv : ValidPath T path) (hEC : Subset E C) :
    ValidPath T (advance T path E).1 ∧ (advance T path E).2 ≤ colourCard C := by
  obtain ⟨r, hr, hv', hd⟩ := step_valid T path E hv hEC
  simp only [advance, hr, Option.getD_some]
  exact ⟨hv', Nat.le_trans hd (path_length_le T path hv)⟩

end ZTree

/-- Full global universe; there are no local-tree resets. -/
def fullColours (m : Nat) : ColourSet m := fun _ => true

def treeRun (T : ZTree α (fullColours m)) (colours : Nat → ColourSet m) : Nat → List Nat
  | 0 => T.leftmost
  | n+1 => (T.advance (treeRun T colours n) (colours n)).1

theorem treeRun_valid (T : ZTree α (fullColours m)) (colours : Nat → ColourSet m) (n : Nat) :
    T.ValidPath (treeRun T colours n) := by
  induction n with
  | zero => exact T.leftmost_valid
  | succ n ih => exact (T.advance_valid _ _ ih (fun _ _ => rfl)).1

/-- Depth(Support) plus the rejecting-root offset, on every edge. -/
def treePriority (T : ZTree α (fullColours m)) (colours : Nat → ColourSet m) (n : Nat) : Nat :=
  (T.advance (treeRun T colours n) (colours n)).2 + if α (fullColours m) then 0 else 1

theorem treePriority_le (T : ZTree α (fullColours m)) (colours : Nat → ColourSet m) (n : Nat) :
    treePriority T colours n ≤ m+1 := by
  have hd := (T.advance_valid (treeRun T colours n) (colours n)
    (treeRun_valid T colours n) (fun _ _ => rfl)).2
  have hc := colourCard_le (fullColours m)
  unfold treePriority
  split <;> omega

/-- The checked ordinary update has a priority on every edge; its export
preserves its min-even language independently of the remaining EL theorem. -/
theorem tree_export (T : ZTree α (fullColours m)) (colours : Nat → ColourSet m) :
    MinEven (treePriority T colours) ↔
      MaxOdd (fun n => exportBound m - treePriority T colours n) := by
  apply parity_export _ _ (exportBound_odd m)
  intro n
  have h := treePriority_le T colours n
  have hb := exportBound_large m
  omega


/-- Unbounded recurrence; finite prefixes do not affect it. -/
def Often (p : Nat → Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ p n

theorem often_shift (p : Nat → Prop) (N : Nat) : Often (fun n => p (N+n)) ↔ Often p := by
  constructor
  · intro h M; obtain ⟨n, hn, hp⟩ := h M; exact ⟨N+n, by omega, hp⟩
  · intro h M; obtain ⟨n, hn, hp⟩ := h (N+M); exact ⟨n-N, by omega, by simpa [Nat.add_sub_cancel' (by omega : N ≤ n)] using hp⟩

theorem not_often (p : Nat → Prop) : ¬Often p ↔ ∃ N, ∀ n, N ≤ n → ¬p n := by
  simp only [Often, Classical.not_forall, not_exists, not_and]

theorem finite_eventually (xs : List α) (p : α → Nat → Prop)
    (h : ∀ a, a ∈ xs → ∃ N, ∀ n, N ≤ n → p a n) :
    ∃ N, ∀ n, N ≤ n → ∀ a, a ∈ xs → p a n := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨N, hN⟩ := h a (by simp)
    obtain ⟨M, hM⟩ := ih (fun b hb => h b (by simp [hb]))
    refine ⟨max N M, fun n hn b hb => ?_⟩
    rcases List.mem_cons.mp hb with he | hb
    · subst b; exact hN n (by omega)
    · exact hM n (by omega) b hb

/-- Finitely many nonrecurring colours have a common last-occurrence bound. -/
theorem recurrent_eventually_subset (E : Nat → ColourSet m) (D : ColourSet m)
    (h : Subset (recurrentColours E) D) : ∃ N, ∀ n, N ≤ n → Subset (E n) D := by
  obtain ⟨N, hN⟩ := finite_eventually (List.finRange m)
    (fun i n => E n i = true → D i = true) (by
      intro i _
      by_cases hi : D i = true
      · exact ⟨0, fun _ _ _ => hi⟩
      · have hn : ¬Inf (fun n => E n i) := fun hh => hi (h i (by simpa [recurrentColours] using hh))
        obtain ⟨N, hN⟩ := (not_inf_iff_fin _).mp hn
        exact ⟨N, fun n hn he => False.elim (Bool.noConfusion ((hN n hn).symm.trans he))⟩)
  exact ⟨N, fun n hn i => hN n hn i (by simp)⟩

theorem recurrent_subset (E : Nat → ColourSet m) (C : ColourSet m)
    (h : ∀ n, Subset (E n) C) : Subset (recurrentColours E) C := by
  intro i hi
  have hh : Inf (fun n => E n i) := by simpa [recurrentColours] using hi
  obtain ⟨n, _, hn⟩ := hh 0
  exact h n i hn

theorem recurrent_shift (E : Nat → ColourSet m) (N : Nat) :
    recurrentColours (fun n => E (N+n)) = recurrentColours E := by
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [recurrentColours, decide_eq_true_eq]
  exact often_shift (fun n => E n i = true) N

theorem minEven_shift (p : Nat → Nat) (N : Nat) :
    MinEven (fun n => p (N+n)) ↔ MinEven p := by
  constructor
  · rintro ⟨k, hk, hi, M, hM⟩
    exact ⟨k, hk, (often_shift _ N).mp hi, N+M, fun n hn => by
      have hh := hM (n-N) (by omega)
      simpa [Nat.add_sub_cancel' (by omega : N ≤ n)] using hh⟩
  · rintro ⟨k, hk, hi, M, hM⟩
    exact ⟨k, hk, (often_shift _ N).mpr hi, M, fun n hn => hM (N+n) (by omega)⟩

theorem minEven_zero_anchor (d : Nat → Nat) (ε : Nat) (h : Often (fun n => d n = 0)) :
    MinEven (fun n => d n + ε) ↔ ε % 2 = 0 := by
  constructor
  · rintro ⟨k, hk, hi, N, hN⟩
    obtain ⟨n, hn, he⟩ := h N
    have hle := hN n hn
    dsimp only at hle
    obtain ⟨j, _, hj⟩ := hi 0
    dsimp only at hj
    have heq : k = ε := by omega
    simpa [heq] using hk
  · intro he
    refine ⟨ε, he, ?_, 0, fun n _ => by dsimp only; omega⟩
    intro N; obtain ⟨n, hn, he⟩ := h N; exact ⟨n, hn, by simp [he]⟩

/-- Distance to a fixed sibling in the ordinary circular order. -/
def siblingDistance (l j i : Nat) : Nat := if i ≤ j then j-i else l+j-i

theorem sibling_distance_step (hi : i < l) (hj : j < l) (hne : i ≠ j) :
    siblingDistance l j ((i+1)%l) < siblingDistance l j i := by
  by_cases hlast : i+1 = l
  · rw [hlast, Nat.mod_self]
    unfold siblingDistance
    split <;> split <;> omega
  · have hh : i+1 < l := by omega
    rw [Nat.mod_eq_of_lt hh]
    unfold siblingDistance
    split <;> split <;> omega

/-- Infinite ordinary rotations cannot avoid any sibling at rotation time.
This is the rotation part of STAGE2 §5, including one-child nodes. -/
theorem rotation_visits (i d : Nat → Nat) (l : Nat) (hi : ∀ n, i n < l)
    (hm : ∀ n, i (n+1) = if d n = 0 then (i n+1)%l else i n)
    (hd : Often (fun n => d n = 0)) (j : Nat) (hj : j < l) :
    Often (fun n => i n = j ∧ d n = 0) := by
  apply Classical.byContradiction; intro hn
  obtain ⟨N, hN⟩ := not_often _ |>.mp hn
  let f := fun n => siblingDistance l j (i n)
  have hmono : ∀ n, N ≤ n → f (n+1) ≤ f n := by
    intro n hn
    by_cases hz : d n = 0
    · have hne : i n ≠ j := fun he => hN n hn ⟨he, hz⟩
      have hh := sibling_distance_step (hi n) hj hne
      dsimp only [f]; rw [hm n, ite_eq_left hz]; omega
    · dsimp only [f]; rw [hm n, ite_eq_right hz]
      exact Nat.le_refl _
  obtain ⟨k, ⟨t, ht, htk⟩, hmin⟩ := exists_least_nat (show ∃ k, ∃ t, N ≤ t ∧ f t = k from ⟨f N, N, Nat.le_refl _, rfl⟩)
  obtain ⟨n, htn, hz⟩ := hd t
  have hle : f n ≤ f t := by
    have hh : ∀ s, f (t+s) ≤ f t := by
      intro s; induction s with
      | zero => exact Nat.le_refl _
      | succ s ih => exact Nat.le_trans (hmono (t+s) (by omega)) ih
    simpa [Nat.add_sub_cancel' htn] using hh (n-t)
  have hne : i n ≠ j := fun he => hN n (by omega) ⟨he, hz⟩
  have hlt : f (n+1) < k := by
    have hh := sibling_distance_step (hi n) hj hne
    dsimp only [f] at *
    rw [hm n, ite_eq_left hz]
    omega
  exact hmin _ hlt ⟨n+1, by omega, rfl⟩

namespace ZTree

/-- A stream of valid paths follows exactly the ordinary update. The two
alternatives expose child retention and one-sibling rotation. -/
theorem node_motion (children : List (ColourSet m))
    (hs : ∀ M, M ∈ children → MaximalOpposite α C M)
    (hc : ∀ M, MaximalOpposite α C M → M ∈ children)
    (sub : ∀ M, M ∈ children → ZTree α M)
    (i : Nat) (rest next : List Nat) (E : ColourSet m) (d : Nat)
    (hv : ValidPath (.node C children hs hc sub) (i::rest))
    (hEC : Subset E C)
    (he : step (.node C children hs hc sub) (i::rest) E = some (next,d)) :
    ∃ hi : i < children.length,
      (Subset E children[i] ∧ 0 < d ∧ next.headD 0 = i ∧
        step (sub children[i] (List.getElem_mem hi)) rest E = some (next.tail,d-1)) ∨
      (¬Subset E children[i] ∧ d = 0 ∧ next.headD 0 = (i+1)%children.length) := by
  obtain ⟨hi, hrest⟩ := hv
  refine ⟨hi, ?_⟩
  by_cases hchild : Subset E children[i]
  · obtain ⟨⟨p,k⟩, hp, _, _⟩ := step_valid (sub children[i] (List.getElem_mem hi)) rest E hrest hchild
    simp only [step, hEC, hi, hchild, ↓reduceIte, ↓reduceDIte, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he.symm
    exact Or.inl ⟨hchild, by omega, rfl, by simpa using hp⟩
  · simp only [step, hEC, hi, hchild, ↓reduceIte, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at he
    exact Or.inr ⟨hchild, he.2.symm, by rw [← he.1]; rfl⟩

/-- Full recurrent-run theorem, generalized to any root label, initial leaf
and offset. The proof follows the recurrent-anchor argument of STAGE2 §5. -/
theorem recurrent_run (T : ZTree α C) (E : Nat → ColourSet m)
    (r : Nat → List Nat) (d : Nat → Nat) (ε : Nat)
    (hv : ∀ n, ValidPath T (r n)) (hEC : ∀ n, Subset (E n) C)
    (hm : ∀ n, step T (r n) (E n) = some (r (n+1), d n))
    (hε : ε % 2 = 0 ↔ α C = true) :
    MinEven (fun n => d n + ε) ↔ α (recurrentColours E) = true := by
  induction T generalizing E r d ε with
  | node C children hs hc sub ih =>
    have hSC := recurrent_subset E C hEC
    by_cases hz : Often (fun n => d n = 0)
    · have hno : ∀ D, D ∈ children → ¬Subset (recurrentColours E) D := by
        intro D hD hSD
        obtain ⟨j, hj, heD⟩ := List.getElem_of_mem hD
        obtain ⟨N, hN⟩ := recurrent_eventually_subset E D hSD
        have hnonempty : children ≠ [] := by intro he; simp [he] at hD
        have hr : ∀ n, ∃ i rest, r n = i::rest := by
          intro n; cases he : r n with
          | nil => have hh := hv n; rw [he] at hh; exact False.elim (hnonempty hh)
          | cons i rest => exact ⟨i, rest, rfl⟩
        let ix := fun n => (r n).headD 0
        have hi : ∀ n, ix n < children.length := by
          intro n; obtain ⟨i, rest, he⟩ := hr n
          have hh := hv n; rw [he] at hh
          simpa [ix, he] using hh.1
        have motion := fun n => node_motion children hs hc sub (ix n) (r n).tail (r (n+1)) (E n) (d n)
          (by obtain ⟨i, rest, he⟩ := hr n; simpa [ix, he] using hv n) (hEC n)
          (by obtain ⟨i, rest, he⟩ := hr n; simpa [ix, he] using hm n)
        have hix : ∀ n, ix (n+1) = if d n = 0 then (ix n+1)%children.length else ix n := by
          intro n; obtain ⟨_, hh | hh⟩ := motion n
          · rw [ite_eq_right (by omega : d n ≠ 0)]; exact hh.2.2.1
          · rw [ite_eq_left hh.2.1]; exact hh.2.2
        obtain ⟨n, hn, hij, hdn⟩ := rotation_visits ix d children.length hi hix hz j hj N
        obtain ⟨hi', hh | hh⟩ := motion n
        · omega
        · apply hh.1
          simpa [hij, heD] using hN n hn
      have heq := covered_recurrent_acceptance α C (recurrentColours E) children hc hSC hno
      rw [minEven_zero_anchor d ε hz, hε, heq]
    · obtain ⟨N, hN⟩ := (not_often _).mp hz
      have hnonempty : children ≠ [] := by
        intro he
        have hp := hv N
        have hh := hm N
        cases hpEq : r N with
        | nil => simp [step, he, hEC N, hpEq] at hh; exact hN N (Nat.le_refl _) hh.2.symm
        | cons i rest => rw [hpEq] at hp; obtain ⟨hi, _⟩ := hp; simp [he] at hi
      have hr : ∀ n, ∃ i rest, r n = i::rest := by
        intro n; cases he : r n with
        | nil => have hh := hv n; rw [he] at hh; exact False.elim (hnonempty hh)
        | cons i rest => exact ⟨i, rest, rfl⟩
      let ix := fun n => (r n).headD 0
      have motion := fun n => node_motion children hs hc sub (ix n) (r n).tail (r (n+1)) (E n) (d n)
        (by obtain ⟨i, rest, he⟩ := hr n; simpa [ix, he] using hv n) (hEC n)
        (by obtain ⟨i, rest, he⟩ := hr n; simpa [ix, he] using hm n)
      have stable : ∀ n, ix (N+n) = ix N := by
        intro n; induction n with
        | zero => rfl
        | succ n ih =>
          obtain ⟨_, hh | hh⟩ := motion (N+n)
          · exact hh.2.2.1.trans ih
          · exact False.elim (hN (N+n) (by omega) hh.2.1)
      have hj := (motion N).1
      let D := children[ix N]
      have hD := List.getElem_mem hj
      have hopp := (hs D hD).2.1
      have hε' : (ε+1)%2=0 ↔ α D = true := by
        cases ha : α C <;> cases hb : α D <;> simp_all <;> omega
      have hsub : ∀ n, Subset (E (N+n)) D ∧
          step (sub D hD) (r (N+n)).tail (E (N+n)) = some ((r (N+n+1)).tail, d (N+n)-1) := by
        intro n; obtain ⟨_, hh | hh⟩ := motion (N+n)
        · have transport : ∀ M (hM : M ∈ children), M = D →
              Subset (E (N+n)) M ∧ step (sub M hM) (r (N+n)).tail (E (N+n)) =
                some ((r (N+n+1)).tail, d (N+n)-1) →
              Subset (E (N+n)) D ∧ step (sub D hD) (r (N+n)).tail (E (N+n)) =
                some ((r (N+n+1)).tail, d (N+n)-1) := by
            intro M hM he hh; subst M; exact hh
          exact transport _ _ (by simp only [D, stable n]) ⟨hh.1, hh.2.2.2⟩
        · exact False.elim (hN (N+n) (by omega) hh.2.1)
      have hv' : ∀ n, ValidPath (sub D hD) (r (N+n)).tail := by
        intro n
        obtain ⟨i, rest, he⟩ := hr (N+n)
        have hh := hv (N+n); rw [he] at hh
        have hs' := stable n
        simp only [ix, he, List.headD_cons] at hs'
        subst i
        simpa [he] using hh.2
      have hh := ih D hD (fun n => E (N+n)) (fun n => (r (N+n)).tail)
        (fun n => d (N+n)-1) (ε+1) hv' (fun n => (hsub n).1)
        (by intro n; simpa [Nat.add_assoc] using (hsub n).2) hε'
      have he : (fun n => d (N+n)-1+(ε+1)) = (fun n => d (N+n)+ε) := by
        funext n; have hn := hN (N+n) (by omega); omega
      rw [he, recurrent_shift] at hh
      rw [← minEven_shift (fun n => d n + ε) N]
      exact hh

end ZTree

/-- STAGE2 §5: min-even of the ordinary global run is exactly α(S), for
every colour stream, including empty marks, constant α and zero colours. -/
theorem tree_minEven (T : ZTree α (fullColours m)) (colours : Nat → ColourSet m) :
    MinEven (treePriority T colours) ↔ EmersonLei α colours := by
  apply T.recurrent_run colours (treeRun T colours)
    (fun n => (T.advance (treeRun T colours n) (colours n)).2)
    (if α (fullColours m) then 0 else 1) (treeRun_valid T colours) (fun _ _ _ => rfl)
  · intro n
    obtain ⟨r, hr, _, _⟩ := T.step_valid (treeRun T colours n) (colours n) (treeRun_valid T colours n) (fun _ _ => rfl)
    simp only [treeRun, ZTree.advance, hr, Option.getD_some]
  · cases α (fullColours m) <;> simp

/-- STAGE2 §5: the exported recurring maximum is odd exactly when α(S). -/
theorem tree_maxOdd (T : ZTree α (fullColours m)) (colours : Nat → ColourSet m) :
    MaxOdd (fun n => exportBound m - treePriority T colours n) ↔ EmersonLei α colours :=
  (tree_export T colours).symm.trans (tree_minEven T colours)

end
end Tlsf.Dpa
