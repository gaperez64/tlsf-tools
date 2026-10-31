import TlsfProofs.Dpa.Impl.Cache

/-!
# Selection and execution from frozen Boolean syntax

`src/lib/dpa_formula.c:563` traverses equal-operator operands left to right,
classifies finite operands before safety and co-safety, and immediately
executes the recursive rest operands. `src/lib/dpa_formula.c:583` then calls
canonical acceptance on both folded groups, in either C argument order.
The co-safety class's equality with the Boolean identity selects where the
finite group goes (`src/lib/dpa_formula.c:597`).

This module selects a concrete ordered plan from that syntax. Its canonical
leaves execute the cached constructor; binary syntax nodes have no acceptance
cache of their own. The frozen input here is the result of factoring; the
imperative `factor_term` recursion is a separate bridge.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

/-- Executable structural partition, without the abstract module's classical
decision instances. Filtering retains traversal order and multiplicity. -/
def partitionSyntax (fs : List (Formula (Fin ap))) : OperandGroups ap :=
  ⟨fs.filter (fun f => !finiteb f && safetyb f),
   fs.filter (fun f => !finiteb f && !safetyb f && cosafetyb f),
   fs.filter finiteb,
   fs.filter (fun f => !finiteb f && !safetyb f && !cosafetyb f)⟩

theorem partitionSyntax_exact (fs : List (Formula (Fin ap))) :
    partitionSyntax fs = partitionOperands fs := by
  classical
  have hs : (fun f : Formula (Fin ap) => !finiteb f && safetyb f) =
      (fun f => decide (¬finite f ∧ safety f)) := by
    funext f
    apply Bool.eq_iff_iff.mpr
    simp [Bool.eq_false_iff, finiteb_exact, safetyb_exact]
  have hc : (fun f : Formula (Fin ap) => !finiteb f && !safetyb f && cosafetyb f) =
      (fun f => decide (¬finite f ∧ ¬safety f ∧ cosafety f)) := by
    funext f
    apply Bool.eq_iff_iff.mpr
    simp [Bool.eq_false_iff, finiteb_exact, safetyb_exact, cosafetyb_exact, and_assoc]
  have hb : (finiteb : Formula (Fin ap) → Bool) = (fun f => decide (finite f)) := by
    funext f
    apply Bool.eq_iff_iff.mpr
    simp [finiteb_exact]
  have ht : (fun f : Formula (Fin ap) => !finiteb f && !safetyb f && !cosafetyb f) =
      (fun f => decide (¬finite f ∧ ¬safety f ∧ ¬cosafety f)) := by
    funext f
    apply Bool.eq_iff_iff.mpr
    simp [Bool.eq_false_iff, finiteb_exact, safetyb_exact, cosafetyb_exact, and_assoc]
  unfold partitionSyntax partitionOperands
  rw [hs, hc, ht, hb]

inductive OrderedPlan (ap : Nat) where
  | canonical : Formula (Fin ap) → OrderedPlan ap
  | binary : Bool → Bool → OrderedPlan ap → OrderedPlan ap → OrderedPlan ap
  deriving DecidableEq

def OrderedPlan.source : OrderedPlan ap → Formula (Fin ap)
  | .canonical f => f
  | .binary op _ f g => if op then .conj f.source g.source else .disj f.source g.source

def OrderedPlan.Valid : OrderedPlan ap → Prop
  | .canonical f => NNF f ∧ canonicalResearchCheck f = true
  | .binary _ _ f g => f.Valid ∧ g.Valid

def foldOrdered (op : Bool) : List (OrderedPlan ap) → OrderedPlan ap
  | [] => .canonical (booleanIdentity op)
  | p :: ps => .binary op true p (foldOrdered op ps)

theorem foldOrdered_source (op : Bool) (ps : List (OrderedPlan ap)) :
    (foldOrdered op ps).source = booleanFold op (ps.map OrderedPlan.source) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases op <;> simp [foldOrdered, OrderedPlan.source, booleanFold, ih]

theorem foldOrdered_valid (op : Bool) (ps : List (OrderedPlan ap))
    (hp : ∀ p, p ∈ ps → p.Valid) : (foldOrdered op ps).Valid := by
  induction ps with
  | nil => cases op <;> exact ⟨trivial, rfl⟩
  | cons p ps ih => exact ⟨hp p (by simp), ih (fun q hq => hp q (by simp [hq]))⟩

def selectedGroups (op : Bool) (S C B : List (Formula (Fin ap))) :
    Formula (Fin ap) × Formula (Fin ap) :=
  if equivalent (booleanFold op C) (booleanIdentity op) then
    (booleanFold op (S ++ B), booleanFold op C)
  else (booleanFold op S, booleanFold op (C ++ B))

/-- The outer node always executes the rest first. Only the inner node's
two canonical group calls have unspecified C argument order. -/
def orderedGroups (safetyFirst op : Bool) (S C B : List (Formula (Fin ap)))
    (rest : List (OrderedPlan ap)) : OrderedPlan ap :=
  let g := selectedGroups op S C B
  .binary op true (foldOrdered op rest)
    (.binary op safetyFirst (.canonical g.1) (.canonical g.2))

theorem selectedGroups_valid (op : Bool) (S C B : List (Formula (Fin ap)))
    (hs : ∀ f, f ∈ S → safety f) (hc : ∀ f, f ∈ C → cosafety f)
    (hb : ∀ f, f ∈ B → finite f) :
    (OrderedPlan.canonical (selectedGroups op S C B).1).Valid ∧
    (OrderedPlan.canonical (selectedGroups op S C B).2).Valid := by
  have safetyValid (f : Formula (Fin ap)) (hf : safety f) :
      (OrderedPlan.canonical f).Valid :=
    ⟨(whole_safety_valid f hf).1, researchAdmitted_check f (whole_safety_valid f hf).2⟩
  have cosafetyValid (f : Formula (Fin ap)) (hf : cosafety f) :
      (OrderedPlan.canonical f).Valid :=
    ⟨(whole_cosafety_valid f hf).1, researchAdmitted_check f (whole_cosafety_valid f hf).2⟩
  unfold selectedGroups
  split
  · refine ⟨safetyValid _ (booleanFold_safety op ?_), cosafetyValid _ (booleanFold_cosafety op hc)⟩
    intro f hf
    exact (List.mem_append.mp hf).elim (hs f) (fun h => finite_implies_safety f (hb f h))
  · refine ⟨safetyValid _ (booleanFold_safety op hs), cosafetyValid _ (booleanFold_cosafety op ?_)⟩
    intro f hf
    exact (List.mem_append.mp hf).elim (hc f) (fun h => finite_implies_cosafety f (hb f h))

theorem orderedGroups_valid (safetyFirst op : Bool) (S C B : List (Formula (Fin ap)))
    (rest : List (OrderedPlan ap)) (hs : ∀ f, f ∈ S → safety f)
    (hc : ∀ f, f ∈ C → cosafety f) (hb : ∀ f, f ∈ B → finite f)
    (hr : ∀ p, p ∈ rest → p.Valid) : (orderedGroups safetyFirst op S C B rest).Valid :=
  ⟨foldOrdered_valid op rest hr, selectedGroups_valid op S C B hs hc hb⟩

theorem orderedGroups_language (safetyFirst op : Bool) (S C B : List (Formula (Fin ap)))
    (rest : List (OrderedPlan ap)) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (orderedGroups safetyFirst op S C B rest).source n ↔
      Sat none w (booleanFold op (S ++ C ++ B ++ rest.map OrderedPlan.source)) n := by
  have hg := compatibleGroups_language op S C B (rest.map OrderedPlan.source) w n
  unfold compatibleGroups at hg
  unfold orderedGroups selectedGroups
  split <;> rename_i h <;> cases op <;>
    simp only [h, ↓reduceIte] at hg <;>
    simpa only [OrderedPlan.source, foldOrdered_source, Bool.false_eq_true, ↓reduceIte,
      booleanFold, Sat, InRange, true_and, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc] using hg

def selectCanonicalLeaf (f : Formula (Fin ap)) : Option (OrderedPlan ap) :=
  if canonicalResearchCheck f then some (.canonical f) else none

def selectGrouped (recur : Formula (Fin ap) → Option (OrderedPlan ap))
    (safetyFirst op : Bool) (fs : List (Formula (Fin ap))) : Option (OrderedPlan ap) := do
  let p := partitionSyntax fs
  let rest ← p.T.mapM recur
  pure (orderedGroups safetyFirst op p.S p.C p.B rest)

def syntaxSize : Formula α → Nat
  | .tt | .ff | .ap _ => 1
  | .neg f | .next f | .strongNext f | .eventually f | .globally f => syntaxSize f + 1
  | .conj f g | .disj f g | .impl f g | .equiv f g
  | .until f g | .release f g | .weakUntil f g | .strongRelease f g => syntaxSize f + syntaxSize g + 1

theorem flattenOperands_syntaxSize (op : Bool) (f : Formula α)
    (hg : g ∈ flattenOperands op f) : syntaxSize g ≤ syntaxSize f := by
  induction f with
  | conj f f' ih ih' | disj f f' ih ih' =>
    cases op <;> simp only [flattenOperands, Bool.false_eq_true, ↓reduceIte] at hg
    all_goals first
      | exact (List.mem_singleton.mp hg) ▸ Nat.le_refl _
      | rcases List.mem_append.mp hg with hg | hg
        · have hh := ih hg; simp only [syntaxSize]; omega
        · have hh := ih' hg; simp only [syntaxSize]; omega
  | _ => exact (List.mem_singleton.mp hg) ▸ Nat.le_refl _

/-- The syntax selector of `src/lib/dpa_formula.c:583`, after factoring.
Fuel bounds pure syntax recursion; it is not C's resource budget. -/
def selectSyntaxPlan (safetyFirst : Formula (Fin ap) → Bool) :
    Nat → Formula (Fin ap) → Option (OrderedPlan ap)
  | 0, _ => none
  | fuel + 1, f =>
    if researchAdmitted f then selectCanonicalLeaf f
    else match f with
    | .conj _ _ => selectGrouped (selectSyntaxPlan safetyFirst fuel)
        (safetyFirst f) true (flattenOperands true f)
    | .disj _ _ => selectGrouped (selectSyntaxPlan safetyFirst fuel)
        (safetyFirst f) false (flattenOperands false f)
    | _ => selectCanonicalLeaf f

def SelectedPlan (f : Formula (Fin ap)) (p : OrderedPlan ap) : Prop :=
  p.Valid ∧ ∀ w n, Sat none w p.source n ↔ Sat none w f n

theorem canonicalResearchCheck_boolean (op : Bool) (f g : Formula (Fin ap))
    (hf : canonicalResearchCheck f = true) (hg : canonicalResearchCheck g = true) :
    canonicalResearchCheck (if op then .conj f g else .disj f g) = true := by
  simp only [canonicalResearchCheck_exact] at hf hg ⊢
  exact fun a ha => (boolean_uses op f g ha).elim (hf a) (hg a)

theorem groupableResearch_canonical (f : Formula (Fin ap))
    (h : groupableSyntax canonicalResearchCheck f = true) : canonicalResearchCheck f = true := by
  induction f with
  | conj f g ih ih' =>
    exact canonicalResearchCheck_boolean true f g (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | disj f g ih ih' =>
    exact canonicalResearchCheck_boolean false f g (ih (Bool.and_eq_true_iff.mp h).1) (ih' (Bool.and_eq_true_iff.mp h).2)
  | _ => exact h

theorem flattenOperands_nnf (op : Bool) (f : Formula (Fin ap)) (hf : NNF f)
    (g : Formula (Fin ap)) (hg : g ∈ flattenOperands op f) : NNF g := by
  induction f with
  | conj f f' ih ih' | disj f f' ih ih' =>
    cases op <;> simp only [flattenOperands, Bool.false_eq_true, ↓reduceIte] at hg
    all_goals first
      | exact (List.mem_singleton.mp hg) ▸ hf
      | exact (List.mem_append.mp hg).elim (ih hf.1) (ih' hf.2)
  | _ => exact (List.mem_singleton.mp hg) ▸ hf

theorem partitionSyntax_fragments (fs : List (Formula (Fin ap))) :
    (∀ f, f ∈ (partitionSyntax fs).S → safety f) ∧
    (∀ f, f ∈ (partitionSyntax fs).C → cosafety f) ∧
    (∀ f, f ∈ (partitionSyntax fs).B → finite f) := by
  classical
  rw [partitionSyntax_exact]
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact (of_decide_eq_true (List.mem_filter.mp hf).2).2
  · intro f hf
    exact (of_decide_eq_true (List.mem_filter.mp hf).2).2.2
  · intro f hf
    exact of_decide_eq_true (List.mem_filter.mp hf).2

theorem mapM_selectedPlans (call : Formula (Fin ap) → Option (OrderedPlan ap))
    (op : Bool) (fs : List (Formula (Fin ap)))
    (h : ∀ f, f ∈ fs → ∃ p, call f = some p ∧ SelectedPlan f p) :
    ∃ ps, fs.mapM call = some ps ∧ (∀ p, p ∈ ps → p.Valid) ∧
      ∀ w n, Sat none w (booleanFold op (ps.map OrderedPlan.source)) n ↔
        Sat none w (booleanFold op fs) n := by
  induction fs with
  | nil => exact ⟨[], rfl, by simp, fun _ _ => Iff.rfl⟩
  | cons f fs ih =>
    obtain ⟨p, hp, vp, lp⟩ := h f (by simp)
    obtain ⟨ps, he, vs, ls⟩ := ih (fun f hf => h f (by simp [hf]))
    refine ⟨p :: ps, by simp [List.mapM_cons, hp, he], ?_, ?_⟩
    · intro q hq
      exact (List.mem_cons.mp hq).elim (fun h => h ▸ vp) (vs q)
    · intro w n
      cases op <;> simp [booleanFold, Sat, InRange, lp, ls]

theorem selectGrouped_success (recur : Formula (Fin ap) → Option (OrderedPlan ap))
    (safetyFirst op : Bool) (fs : List (Formula (Fin ap)))
    (h : ∀ f, f ∈ (partitionSyntax fs).T → ∃ p, recur f = some p ∧ SelectedPlan f p) :
    ∃ p, selectGrouped recur safetyFirst op fs = some p ∧ SelectedPlan (booleanFold op fs) p := by
  obtain ⟨rest, er, vr, lr⟩ := mapM_selectedPlans recur op (partitionSyntax fs).T h
  obtain ⟨hs, hc, hb⟩ := partitionSyntax_fragments fs
  refine ⟨orderedGroups safetyFirst op (partitionSyntax fs).S (partitionSyntax fs).C
    (partitionSyntax fs).B rest, ?_, orderedGroups_valid safetyFirst op _ _ _ rest hs hc hb vr, ?_⟩
  · simp [selectGrouped, er]
  · intro w n
    calc
      _ ↔ Sat none w (booleanFold op ((partitionSyntax fs).S ++ (partitionSyntax fs).C ++
          (partitionSyntax fs).B ++ rest.map OrderedPlan.source)) n :=
        orderedGroups_language safetyFirst op _ _ _ rest w n
      _ ↔ Sat none w (booleanFold op ((partitionSyntax fs).S ++ (partitionSyntax fs).C ++
          (partitionSyntax fs).B ++ (partitionSyntax fs).T)) n := by
        cases op <;> simp only [booleanFold_append_sat, Bool.false_eq_true, ↓reduceIte, lr]
      _ ↔ _ := by rw [partitionSyntax_exact]; exact partitionOperands_sat op fs w n

theorem selectSyntaxPlan_success (safetyFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (f : Formula (Fin ap)) (hf : NNF f) (hsize : syntaxSize f < fuel)
    (hguard : groupableSyntax canonicalResearchCheck f = true) :
    ∃ p, selectSyntaxPlan safetyFirst fuel f = some p ∧ SelectedPlan f p := by
  induction fuel generalizing f with
  | zero => omega
  | succ fuel ih =>
    have hc := groupableResearch_canonical f hguard
    by_cases hw : researchAdmitted f = true
    · exact ⟨.canonical f, by simp [selectSyntaxPlan, hw, selectCanonicalLeaf, hc],
        ⟨hf, hc⟩, fun _ _ => Iff.rfl⟩
    · cases f with
      | conj a b =>
        have hrec : ∀ f, f ∈ (partitionSyntax (flattenOperands true (.conj a b))).T →
            ∃ p, selectSyntaxPlan safetyFirst fuel f = some p ∧ SelectedPlan f p := by
          intro f hm
          have hmem : f ∈ flattenOperands true (.conj a b) := (List.mem_filter.mp hm).1
          apply ih f (flattenOperands_nnf true (.conj a b) hf f hmem)
          · simp only [flattenOperands, ↓reduceIte] at hmem
            rcases List.mem_append.mp hmem with hm | hm
            · have hh := flattenOperands_syntaxSize true a hm
              simp only [syntaxSize] at hsize; omega
            · have hh := flattenOperands_syntaxSize true b hm
              simp only [syntaxSize] at hsize; omega
          · exact flattenOperands_guard true (.conj a b) hguard hmem
        obtain ⟨p, ep, vp, lp⟩ := selectGrouped_success _ (safetyFirst (.conj a b)) true _ hrec
        exact ⟨p, by simp [selectSyntaxPlan, hw, ep], vp,
          fun w n => (lp w n).trans (flattenOperands_sat true (.conj a b) w n)⟩
      | disj a b =>
        have hrec : ∀ f, f ∈ (partitionSyntax (flattenOperands false (.disj a b))).T →
            ∃ p, selectSyntaxPlan safetyFirst fuel f = some p ∧ SelectedPlan f p := by
          intro f hm
          have hmem : f ∈ flattenOperands false (.disj a b) := (List.mem_filter.mp hm).1
          apply ih f (flattenOperands_nnf false (.disj a b) hf f hmem)
          · simp only [flattenOperands, Bool.false_eq_true, ↓reduceIte] at hmem
            rcases List.mem_append.mp hmem with hm | hm
            · have hh := flattenOperands_syntaxSize false a hm
              simp only [syntaxSize] at hsize; omega
            · have hh := flattenOperands_syntaxSize false b hm
              simp only [syntaxSize] at hsize; omega
          · exact flattenOperands_guard false (.disj a b) hguard hmem
        obtain ⟨p, ep, vp, lp⟩ := selectGrouped_success _ (safetyFirst (.disj a b)) false _ hrec
        exact ⟨p, by simp [selectSyntaxPlan, hw, ep], vp,
          fun w n => (lp w n).trans (flattenOperands_sat false (.disj a b) w n)⟩
      | _ => exact ⟨.canonical _, by simp [selectSyntaxPlan, hw, selectCanonicalLeaf, hc],
          ⟨hf, hc⟩, fun _ _ => Iff.rfl⟩

def cachedBoolean (firstLeft op : Bool) (first second : CachedAssembly ap) : CachedAssembly ap :=
  ⟨second.state, if firstLeft then .binary op first.acceptance second.acceptance
    else .binary op second.acceptance first.acceptance, first.calls ++ second.calls⟩

theorem cachedBoolean_spec (s : AcceptanceState ap) (firstLeft op : Bool)
    (f g : Formula (Fin ap)) (first second : CachedAssembly ap)
    (hf : first.Spec s (if firstLeft then f else g))
    (hg : second.Spec first.state (if firstLeft then g else f)) :
    (cachedBoolean firstLeft op first second).Spec s (if op then .conj f g else .disj f g) := by
  refine ⟨hf.1.trans hg.1, hg.2.1, ?_, ?_⟩
  · cases firstLeft <;> exact ⟨
      by first | exact hg.2.2.1 | exact hf.2.2.1.mono _ hg.1.length_le,
      by first | exact hg.2.2.1 | exact hf.2.2.1.mono _ hg.1.length_le⟩
  · intro w
    have he := first.acceptance.eval_extends hg.1 hf.2.2.1 w
    have lf := hf.2.2.2 w
    have lg := hg.2.2.2 w
    cases firstLeft <;> cases op <;>
      simp_all only [cachedBoolean, Bool.false_eq_true, ↓reduceIte, ColourAcceptance.eval,
        Bool.and_eq_true, Bool.or_eq_true, Sat, InRange, true_and]

/-- Execute the selected calls with their original colour numbers. Syntax
combinations do not populate the canonical acceptance cache. -/
def runOrderedPlan (rank : Formula (Fin ap) → Nat) (highFirst : Formula (Fin ap) → Bool)
    (buchi : Bool) : OrderedPlan ap → AcceptanceState ap → Option (CachedAssembly ap)
  | .canonical f, s => runCanonical highFirst buchi (orderAtoms rank (modalAtoms f).eraseDups) f s
  | .binary op firstLeft f g, s =>
    if firstLeft then do
      let left ← runOrderedPlan rank highFirst buchi f s
      let right ← runOrderedPlan rank highFirst buchi g left.state
      pure (cachedBoolean true op left right)
    else do
      let right ← runOrderedPlan rank highFirst buchi g s
      let left ← runOrderedPlan rank highFirst buchi f right.state
      pure (cachedBoolean false op right left)

theorem runOrderedPlan_success (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (buchi : Bool) (p : OrderedPlan ap) (hp : p.Valid)
    (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runOrderedPlan rank highFirst buchi p s = some r ∧ r.Spec s p.source := by
  induction p generalizing s with
  | canonical f =>
    obtain ⟨r, er, sr, _⟩ := runCanonical_presentation highFirst buchi rank f hp.1 hp.2 s hs
    exact ⟨r, er, sr⟩
  | binary op firstLeft f g ihf ihg =>
    cases firstLeft
    · obtain ⟨right, er, sr⟩ := ihg hp.2 s hs
      obtain ⟨left, el, sl⟩ := ihf hp.1 right.state sr.2.1
      exact ⟨_, by simp [runOrderedPlan, er, el],
        cachedBoolean_spec s false op f.source g.source right left sr sl⟩
    · obtain ⟨left, el, sl⟩ := ihf hp.1 s hs
      obtain ⟨right, er, sr⟩ := ihg hp.2 left.state sl.2.1
      exact ⟨_, by simp [runOrderedPlan, el, er],
        cachedBoolean_spec s true op f.source g.source left right sl sr⟩

def runSyntax (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (f : Formula (Fin ap)) (s : AcceptanceState ap) : Option (CachedAssembly ap) := do
  let p ← selectSyntaxPlan safetyFirst (syntaxSize f + 1) f
  runOrderedPlan rank highFirst buchi p s

theorem runSyntax_presentation (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (f : Formula (Fin ap)) (hf : NNF f)
    (hg : groupableSyntax canonicalResearchCheck f = true)
    (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runSyntax rank highFirst safetyFirst buchi f s = some r ∧ r.Spec s f ∧
      ProductPresentation f (storeClasses r.state.store) r.assembly.skeleton := by
  obtain ⟨p, ep, vp, lp⟩ := selectSyntaxPlan_success safetyFirst (syntaxSize f + 1) f hf (by omega) hg
  obtain ⟨r, er, sr⟩ := runOrderedPlan_success rank highFirst buchi p vp s hs
  have spec := sr.language (fun w => lp w 0)
  exact ⟨r, by simp [runSyntax, ep, er], spec, spec.presentation⟩

/-- The branch guard and original-class fallback of
`src/lib/dpa_formula.c:610`. Factoring supplies its decoded output separately;
no equivalence between independently frozen modal operands is assumed. -/
def runFactored (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (original factored : Formula (Fin ap)) (s : AcceptanceState ap) : Option (CachedAssembly ap) :=
  if canonicalResearchCheck original then
    if groupableSyntax canonicalResearchCheck factored then
      runSyntax rank highFirst safetyFirst buchi factored s
    else runCanonical highFirst buchi (orderAtoms rank (modalAtoms original).eraseDups) original s
  else none

theorem runFactored_presentation (rank : Formula (Fin ap) → Nat)
    (highFirst safetyFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (original factored : Formula (Fin ap)) (ho : NNF original) (hf : NNF factored)
    (hl : ∀ w n, Sat none w factored n ↔ Sat none w original n)
    (hc : canonicalResearchCheck original = true) (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runFactored rank highFirst safetyFirst buchi original factored s = some r ∧
      r.Spec s original ∧ ProductPresentation original (storeClasses r.state.store) r.assembly.skeleton := by
  by_cases hg : groupableSyntax canonicalResearchCheck factored = true
  · obtain ⟨r, er, sr, _⟩ := runSyntax_presentation rank highFirst safetyFirst buchi factored hf hg s hs
    have spec := sr.language (fun w => hl w 0)
    exact ⟨r, by simp [runFactored, hc, hg, er], spec, spec.presentation⟩
  · obtain ⟨r, er, sr, pr⟩ := runCanonical_presentation highFirst buchi rank original ho hc s hs
    exact ⟨r, by simp [runFactored, hc, hg, er], sr, pr⟩

end Tlsf.Dpa.Impl
