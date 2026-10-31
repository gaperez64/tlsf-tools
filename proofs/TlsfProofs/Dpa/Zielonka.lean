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

end
end Tlsf.Dpa
