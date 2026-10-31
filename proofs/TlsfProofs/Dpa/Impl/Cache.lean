import TlsfProofs.Dpa.Impl.Selection

/-!
# Acceptance-cache execution with ordered component calls

The successful canonical path of `src/lib/dpa_dela.c:117` tests constants,
then the class's acceptance cache, then whole-class admission. On a Shannon
miss it calls `component` for the top atom before either recursive child.
The two child calls are arguments of one C call, so either order is allowed.
`highFirst` selects that per-execution order; it does not reorder colours
after construction. `calls` records every component call, including hits in
the separate component store, but excludes acceptance-cache hits.

Cache keys use decoded canonical-class equality. The list represents the
nonempty cells of C's per-class cache; overwriting an equivalent key has the
same lookup meaning. Constant-cell writes, which are never read, are omitted.
Memory, syntax IDs and BDD representation remain at the decoded boundary.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

structure AcceptanceEntry (ap : Nat) where
  formula : Formula (Fin ap)
  acceptance : ColourAcceptance
  deriving DecidableEq

abbrev AcceptanceCache (ap : Nat) := List (AcceptanceEntry ap)

def AcceptanceCache.Valid (cache : AcceptanceCache ap) (s : ComponentStore ap) : Prop :=
  ∀ e, e ∈ cache → e.acceptance.Bounded s.length ∧
    ∀ w, e.acceptance.eval (storeTruth s w) = true ↔ Sat none w e.formula 0

def lookupAcceptance (f : Formula (Fin ap)) : AcceptanceCache ap → Option ColourAcceptance
  | [] => none
  | e :: cache =>
    if equivalent e.formula f then some e.acceptance else lookupAcceptance f cache

theorem lookupAcceptance_spec (f : Formula (Fin ap)) (cache : AcceptanceCache ap)
    (s : ComponentStore ap) (hc : cache.Valid s) (e : ColourAcceptance)
    (he : lookupAcceptance f cache = some e) :
    e.Bounded s.length ∧ ∀ w, e.eval (storeTruth s w) = true ↔ Sat none w f 0 := by
  induction cache with
  | nil => simp [lookupAcceptance] at he
  | cons entry cache ih =>
    simp only [lookupAcceptance] at he
    split at he
    · rename_i hf
      cases Option.some.inj he
      obtain ⟨hb, hl⟩ := hc entry (by simp)
      exact ⟨hb, fun w => (hl w).trans (class_language ((equivalent_exact _ _).mp hf) w 0)⟩
    · exact ih (fun x hx => hc x (by simp [hx])) he

theorem lookupAcceptance_equivalent (f g : Formula (Fin ap))
    (he : Class.ofFormula f = Class.ofFormula g) (cache : AcceptanceCache ap) :
    lookupAcceptance f cache = lookupAcceptance g cache := by
  induction cache with
  | nil => rfl
  | cons e cache ih =>
    have h : equivalent e.formula f = equivalent e.formula g := by
      apply Bool.eq_iff_iff.mpr
      simp only [equivalent_exact, he]
    simp only [lookupAcceptance, h, ih]

theorem AcceptanceCache.Valid.extends {cache : AcceptanceCache ap} {s t : ComponentStore ap}
    (hc : cache.Valid s) (he : StoreExtends s t) : cache.Valid t := by
  intro e hm
  obtain ⟨hb, hl⟩ := hc e hm
  exact ⟨hb.mono _ he.length_le, fun w => by rw [e.acceptance.eval_extends he hb w]; exact hl w⟩

structure AcceptanceState (ap : Nat) where
  store : ComponentStore ap
  cache : AcceptanceCache ap
  deriving DecidableEq

def AcceptanceState.Valid (s : AcceptanceState ap) : Prop :=
  StoreValid s.store ∧ s.cache.Valid s.store

theorem AcceptanceState.empty_valid : (⟨[], []⟩ : AcceptanceState ap).Valid := by
  constructor <;> intro e he <;> simp at he

structure CachedAssembly (ap : Nat) where
  state : AcceptanceState ap
  acceptance : ColourAcceptance
  calls : List (Formula (Fin ap))
  deriving DecidableEq

def CachedAssembly.Spec (r : CachedAssembly ap) (s : AcceptanceState ap)
    (f : Formula (Fin ap)) : Prop :=
  StoreExtends s.store r.state.store ∧ r.state.Valid ∧
    r.acceptance.Bounded r.state.store.length ∧
    ∀ w, r.acceptance.eval (storeTruth r.state.store w) = true ↔ Sat none w f 0

def CachedAssembly.remember (f : Formula (Fin ap)) (r : CachedAssembly ap) : CachedAssembly ap :=
  { r with state.cache := ⟨f, r.acceptance⟩ :: r.state.cache }

theorem CachedAssembly.Spec.remember {r : CachedAssembly ap} {s : AcceptanceState ap}
    {f : Formula (Fin ap)} (hr : r.Spec s f) : (r.remember f).Spec s f := by
  refine ⟨hr.1, ⟨hr.2.1.1, ?_⟩, hr.2.2⟩
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hr.2.2
  · exact hr.2.1.2 e he

theorem CachedAssembly.Spec.language {r : CachedAssembly ap} {s : AcceptanceState ap}
    {f g : Formula (Fin ap)} (hr : r.Spec s f)
    (he : ∀ w, Sat none w f 0 ↔ Sat none w g 0) : r.Spec s g :=
  ⟨hr.1, hr.2.1, hr.2.2.1, fun w => (hr.2.2.2 w).trans (he w)⟩

def cachedConstant (s : AcceptanceState ap) (b : Bool) : CachedAssembly ap :=
  ⟨s, .constant b, []⟩

theorem cachedConstant_spec (s : AcceptanceState ap) (hs : s.Valid) (b : Bool)
    (f : Formula (Fin ap)) (hf : equivalent f (if b then .tt else .ff) = true) :
    (cachedConstant s b).Spec s f := by
  refine ⟨StoreExtends.refl _, hs, trivial, ?_⟩
  intro w
  have h := class_language ((equivalent_exact _ _).mp hf) w 0
  cases b <;> simpa [cachedConstant, ColourAcceptance.eval, Sat, InRange] using h.symm

def cachedWhole (buchi : Bool) (s : AcceptanceState ap) (f : Formula (Fin ap)) :
    CachedAssembly ap :=
  let r := internComponent buchi s.store f
  (⟨⟨r.1, s.cache⟩, .literal r.2, [f]⟩ : CachedAssembly ap).remember f

theorem cachedWhole_spec (buchi : Bool) (s : AcceptanceState ap) (hs : s.Valid)
    (f : Formula (Fin ap)) (hf : NNF f) (ha : researchAdmitted f = true) :
    (cachedWhole buchi s f).Spec s f := by
  apply CachedAssembly.Spec.remember
  have he := internComponent_prefix buchi s.store f
  exact ⟨he, ⟨internComponent_valid buchi s.store hs.1 f hf ha, hs.2.extends he⟩,
    internComponent_bound buchi s.store f, internComponent_language buchi s.store hs.1 f hf ha⟩

def cachedTest (buchi : Bool) (s : AcceptanceState ap) (a : Formula (Fin ap)) :
    AcceptanceState ap × ColourLiteral :=
  let r := internComponent buchi s.store a
  (⟨r.1, s.cache⟩, r.2)

theorem cachedTest_valid (buchi : Bool) (s : AcceptanceState ap) (hs : s.Valid)
    (a : Formula (Fin ap)) (ha : NNF a ∧ researchAdmitted a = true) :
    (cachedTest buchi s a).1.Valid :=
  ⟨internComponent_valid buchi s.store hs.1 a ha.1 ha.2,
    hs.2.extends (internComponent_prefix buchi s.store a)⟩

/-- The first child's acceptance keeps its original index interpretation
while the second child grows the store. `firstHigh` changes call order only;
the ITE's high and low meanings remain in their original positions. -/
def cachedBranches (firstHigh : Bool) (test : ColourLiteral) (a : Formula (Fin ap))
    (first second : CachedAssembly ap) : CachedAssembly ap :=
  ⟨second.state,
    if firstHigh then .ite test first.acceptance second.acceptance
      else .ite test second.acceptance first.acceptance,
    a :: (first.calls ++ second.calls)⟩

theorem cachedBranches_spec (buchi : Bool) (s : AcceptanceState ap) (hs : s.Valid)
    (a high low : Formula (Fin ap)) (ha : NNF a ∧ researchAdmitted a = true)
    (firstHigh : Bool) (first second : CachedAssembly ap)
    (hfirst : first.Spec (cachedTest buchi s a).1 (if firstHigh then high else low))
    (hsecond : second.Spec first.state (if firstHigh then low else high)) :
    (cachedBranches firstHigh (cachedTest buchi s a).2 a first second).Spec s
      (.disj (.conj a high) (.conj (.neg a) low)) := by
  have et : StoreExtends s.store (cachedTest buchi s a).1.store :=
    internComponent_prefix buchi s.store a
  have bt := internComponent_bound buchi s.store a
  have lt := internComponent_language buchi s.store hs.1 a ha.1 ha.2
  have eb := hfirst.1.trans hsecond.1
  refine ⟨et.trans eb, hsecond.2.1, ?_, ?_⟩
  · cases firstHigh <;> exact ⟨Nat.lt_of_lt_of_le bt eb.length_le,
      by first | exact hsecond.2.2.1 | exact hfirst.2.2.1.mono _ hsecond.1.length_le,
      by first | exact hsecond.2.2.1 | exact hfirst.2.2.1.mono _ hsecond.1.length_le⟩
  · intro w
    have heTest := eb.literal w (cachedTest buchi s a).2 bt
    have heFirst := first.acceptance.eval_extends hsecond.1 hfirst.2.2.1 w
    have lf := hfirst.2.2.2 w
    have ls := hsecond.2.2.2 w
    dsimp only [cachedBranches]
    cases firstHigh <;>
      simp only [Bool.false_eq_true, ↓reduceIte, ColourAcceptance.eval, heTest, heFirst] <;>
      cases ht : (cachedTest buchi s a).2.eval (storeTruth (cachedTest buchi s a).1.store w) <;>
      have lat := lt w <;>
      change (cachedTest buchi s a).2.eval
        (storeTruth (cachedTest buchi s a).1.store w) = true ↔ Sat none w a 0 at lat <;>
      simp only [ht, Bool.false_eq_true, false_iff, true_iff] at lat <;>
      simp_all only [Bool.false_eq_true, ↓reduceIte, Sat, InRange, true_and,
        false_and, false_or, or_false, not_false_eq_true, not_true_eq_false]

/-- Execute the C canonical selector with the acceptance cache consulted
before admission. The pure ordered alphabet does not allocate components.
A skipped unsupported atom likewise makes no store call. -/
def runCanonical (highFirst : Formula (Fin ap) → Bool) (buchi : Bool) :
    List (Formula (Fin ap)) → Formula (Fin ap) → AcceptanceState ap → Option (CachedAssembly ap)
  | atoms, f, s =>
    if equivalent f .ff then some (cachedConstant s false)
    else if equivalent f .tt then some (cachedConstant s true)
    else match lookupAcceptance f s.cache with
    | some e => some ⟨s, e, []⟩
    | none =>
      if researchAdmitted f then some (cachedWhole buchi s f)
      else match atoms with
      | [] => none
      | a :: rest =>
        if uses f a then
          if researchAdmitted a then
            let test := cachedTest buchi s a
            if highFirst f then do
              let high ← runCanonical highFirst buchi rest (cofactor a true f) test.1
              let low ← runCanonical highFirst buchi rest (cofactor a false f) high.state
              pure ((cachedBranches true test.2 a high low).remember f)
            else do
              let low ← runCanonical highFirst buchi rest (cofactor a false f) test.1
              let high ← runCanonical highFirst buchi rest (cofactor a true f) low.state
              pure ((cachedBranches false test.2 a low high).remember f)
          else none
        else runCanonical highFirst buchi rest f s

theorem runCanonical_hit (highFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (atoms : List (Formula (Fin ap))) (f : Formula (Fin ap)) (s : AcceptanceState ap)
    (hf : equivalent f .ff = false) (ht : equivalent f .tt = false)
    (e : ColourAcceptance) (he : lookupAcceptance f s.cache = some e) :
    runCanonical highFirst buchi atoms f s = some ⟨s, e, []⟩ := by
  cases atoms <;> simp [runCanonical, hf, ht, he]

theorem runCanonical_refines (highFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (atoms : List (Formula (Fin ap))) (f : Formula (Fin ap)) (hf : NNF f)
    (p : AcceptancePlan ap) (hp : selectCanonicalPlan atoms f = some p)
    (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runCanonical highFirst buchi atoms f s = some r ∧ r.Spec s f := by
  induction atoms generalizing f p s with
  | nil =>
    by_cases hff : equivalent f .ff = true
    · exact ⟨cachedConstant s false, by simp [runCanonical, hff], cachedConstant_spec s hs false f hff⟩
    by_cases htt : equivalent f .tt = true
    · exact ⟨cachedConstant s true, by simp [runCanonical, hff, htt], cachedConstant_spec s hs true f htt⟩
    cases he : lookupAcceptance f s.cache with
    | some e =>
      exact ⟨(⟨s, e, []⟩ : CachedAssembly ap), by simp [runCanonical, hff, htt, he],
        StoreExtends.refl _, hs, lookupAcceptance_spec f s.cache s.store hs.2 e he⟩
    | none =>
      have hw : researchAdmitted f = true := by
        by_cases hw : researchAdmitted f = true
        · exact hw
        · simp [selectCanonicalPlan, hff, htt, hw] at hp
      exact ⟨cachedWhole buchi s f, by simp [runCanonical, hff, htt, he, hw], cachedWhole_spec buchi s hs f hf hw⟩
  | cons a atoms ih =>
    by_cases hff : equivalent f .ff = true
    · exact ⟨cachedConstant s false, by simp [runCanonical, hff], cachedConstant_spec s hs false f hff⟩
    by_cases htt : equivalent f .tt = true
    · exact ⟨cachedConstant s true, by simp [runCanonical, hff, htt], cachedConstant_spec s hs true f htt⟩
    cases he : lookupAcceptance f s.cache with
    | some e =>
      exact ⟨(⟨s, e, []⟩ : CachedAssembly ap), by simp [runCanonical, hff, htt, he],
        StoreExtends.refl _, hs, lookupAcceptance_spec f s.cache s.store hs.2 e he⟩
    | none =>
      by_cases hw : researchAdmitted f = true
      · exact ⟨cachedWhole buchi s f, by simp [runCanonical, hff, htt, he, hw], cachedWhole_spec buchi s hs f hf hw⟩
      cases hu : uses f a
      · have hp' : selectCanonicalPlan atoms f = some p := by
          simpa [selectCanonicalPlan, hff, htt, hw, hu] using hp
        obtain ⟨r, hr, sr⟩ := ih f hf p hp' s hs
        exact ⟨r, by simpa [runCanonical, hff, htt, he, hw, hu] using hr, sr⟩
      · have hm : a ∈ modalAtoms f := uses_in_bound
          (fun σ τ h => propEval_local f σ τ h) ((uses_exact f a).mp hu)
        have ha : researchAdmitted a = true := by
          by_cases ha : researchAdmitted a = true
          · exact ha
          · simp [selectCanonicalPlan, hff, htt, hw, hu, ha] at hp
        simp only [selectCanonicalPlan, hff, htt, hw, hu, ha, ↓reduceIte] at hp
        change (selectCanonicalPlan atoms (cofactor a true f)).bind (fun high =>
          (selectCanonicalPlan atoms (cofactor a false f)).bind (fun low =>
            some (.shannon a high low))) = some p at hp
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at hp
        obtain ⟨high, hh, low, hl, rfl⟩ := hp
        have va : NNF a ∧ researchAdmitted a = true := ⟨modalAtom_nnf f a hf hm, ha⟩
        have vt := cachedTest_valid buchi s hs a va
        have source := fun w => class_language (cofactor_shannon f a hm) w 0
        cases ho : highFirst f
        · obtain ⟨l, el, sl⟩ := ih _ (cofactor_nnf a f false hf) low hl _ vt
          obtain ⟨h, eh, sh⟩ := ih _ (cofactor_nnf a f true hf) high hh l.state sl.2.1
          refine ⟨_, ?_, (cachedBranches_spec buchi s hs a _ _ va false l h sl sh).language
            (fun w => source w) |>.remember⟩
          simp [runCanonical, hff, htt, he, hw, hu, ha, ho, el, eh]
        · obtain ⟨h, eh, sh⟩ := ih _ (cofactor_nnf a f true hf) high hh _ vt
          obtain ⟨l, el, sl⟩ := ih _ (cofactor_nnf a f false hf) low hl h.state sh.2.1
          refine ⟨_, ?_, (cachedBranches_spec buchi s hs a _ _ va true h l sh sl).language
            (fun w => source w) |>.remember⟩
          simp [runCanonical, hff, htt, he, hw, hu, ha, ho, eh, el]

def CachedAssembly.assembly (r : CachedAssembly ap) : Assembly ap :=
  ⟨r.state.store, r.acceptance⟩

theorem CachedAssembly.Spec.presentation {r : CachedAssembly ap} {s : AcceptanceState ap}
    {f : Formula (Fin ap)} (hr : r.Spec s f) :
    ProductPresentation f (storeClasses r.state.store) r.assembly.skeleton := by
  obtain ⟨_, hv, hb, hl⟩ := hr
  constructor
  · intro i w
    have he := List.getElem?_eq_getElem i.isLt
    have hc := storeColour_language r.state.store hv.1 i.val _ he w
    simpa only [storeClasses, marks_exact, storeColours, he] using
      hc.trans (ofFormula_holds _).symm
  · intro w
    have he := r.acceptance.eval_local hb
      (finiteValuation _ (componentTruth (storeClasses r.state.store) w))
      (storeTruth r.state.store w) (by
        intro i hi
        simp only [finiteValuation, hi, ↓reduceDIte]
        exact (storeTruth_componentTruth _ hv.1 w ⟨i, hi⟩).symm)
    change r.acceptance.eval
      (finiteValuation r.state.store.length (componentTruth (storeClasses r.state.store) w)) = true ↔ _
    rw [he]
    exact hl w

/-- Cache hits and either per-class C argument order refine the proved
uncached assembly in language. The stores and numeric colours may differ;
each result is interpreted in its own actual store. -/
theorem cached_uncached_language (highFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (atoms : List (Formula (Fin ap))) (f : Formula (Fin ap)) (hf : NNF f)
    (p : AcceptancePlan ap) (hp : selectCanonicalPlan atoms f = some p)
    (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runCanonical highFirst buchi atoms f s = some r ∧ r.Spec s f ∧
      ∀ w, (r.acceptance.eval (storeTruth r.state.store w) = true ↔
        (assemble buchi p s.store).acceptance.eval
          (storeTruth (assemble buchi p s.store).store w) = true) := by
  obtain ⟨r, er, sr⟩ := runCanonical_refines highFirst buchi atoms f hf p hp s hs
  obtain ⟨vp, ep⟩ := selectCanonicalPlan_spec atoms f hf p hp
  have uncached := (assemble_spec buchi p vp s.store hs.1).2.2.2
  exact ⟨r, er, sr, fun w => (sr.2.2.2 w).trans
    (((uncached w).trans (class_language ep w 0)).symm)⟩

/-- The same cached constructor, not an existential replacement store,
produces a product presentation on the complete canonical research domain. -/
theorem runCanonical_presentation (highFirst : Formula (Fin ap) → Bool) (buchi : Bool)
    (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) (hf : NNF f)
    (hc : canonicalResearchCheck f = true) (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runCanonical highFirst buchi (orderAtoms rank (modalAtoms f).eraseDups) f s = some r ∧
      r.Spec s f ∧ ProductPresentation f (storeClasses r.state.store) r.assembly.skeleton := by
  obtain ⟨p, hp⟩ := canonicalPlan_success rank f hc
  obtain ⟨r, er, sr⟩ := runCanonical_refines highFirst buchi _ f hf p hp s hs
  exact ⟨r, er, sr, sr.presentation⟩

theorem transported_cached_presentation (termRank atomRank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (buchi : Bool) (f t : Formula (Fin ap))
    (ht : transport termRank f false 0 = some t) (hc : canonicalResearchCheck t = true)
    (s : AcceptanceState ap) (hs : s.Valid) :
    ∃ r, runCanonical highFirst buchi (orderAtoms atomRank (modalAtoms t).eraseDups) t s = some r ∧
      r.state.Valid ∧ ProductPresentation f (storeClasses r.state.store) r.assembly.skeleton := by
  obtain ⟨r, er, sr, _⟩ := runCanonical_presentation highFirst buchi atomRank t
    (transport_nnf termRank f false 0 t ht) hc s hs
  refine ⟨r, er, sr.2.1, (sr.language ?_).presentation⟩
  intro w
  simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using
    transport_language termRank f false 0 t ht w 0

end Tlsf.Dpa.Impl
