import TlsfProofs.Dpa.Impl.SupportedTrace

/-!
# Cached predicate traces

`tagBounds` follows `src/lib/dpa_formula.c:127`: cache first, then the
supported top atom and low/high recursion, without exact operand queries.
`hasTags` is `src/lib/dpa_formula.c:157`, including both quick returns.
`TagProgram.execQuick` interprets predicate instructions with those caches.
Exact instructions retain their original meaning and are realized separately.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

theorem lookupTagBounds_congr (he : Class.ofFormula f = Class.ofFormula g)
    (memo : TagBoundsCache ap) : lookupTagBounds f memo = lookupTagBounds g memo := by
  induction memo with
  | nil => rfl
  | cons e memo ih =>
    have hh : equivalent e.1 f = equivalent e.1 g := by
      apply Bool.eq_iff_iff.mpr
      simp only [equivalent_exact, he]
    simp only [lookupTagBounds, hh, ih]

def TagBoundsCache.Extends (s t : TagBoundsCache ap) : Prop :=
  ∀ f b, lookupTagBounds f s = some b → lookupTagBounds f t = some b

theorem TagBoundsCache.Extends.refl (s : TagBoundsCache ap) : s.Extends s := fun _ _ h => h

theorem TagBoundsCache.Extends.trans {s t u : TagBoundsCache ap}
    (h : s.Extends t) (h' : t.Extends u) : s.Extends u := fun f b hb => h' f b (h f b hb)

theorem TagBoundsCache.Extends.remember {s t : TagBoundsCache ap} (h : s.Extends t)
    (hn : lookupTagBounds f s = none) : s.Extends ((f, b) :: t) := by
  intro g bits hg
  have hne : equivalent f g = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    rw [lookupTagBounds_congr ((equivalent_exact _ _).mp he), hg] at hn
    contradiction
  simpa only [lookupTagBounds, hne, Bool.false_eq_true, ↓reduceIte] using h g bits hg

def meetBounds (a : Formula (Fin ap)) (s : TagCache ap) (low high : TagBounds) : TagBounds :=
  ⟨bitsMeet (atomLower s a) (bitsMeet low.low high.low),
    bitsMeet (operatorBits a) (bitsMeet low.high high.high)⟩

theorem meetBounds_valid (s : TagCache ap) (hs : s.Valid)
    (ha : Uses (Class.ofFormula f) a) (hl : low.Valid (cofactor a false f))
    (hh : high.Valid (cofactor a true f)) : (meetBounds a s low high).Valid f := by
  have hsplit (tag : Formula (Fin ap) → Prop) :=
    tags_shannon_intersection (tag := tag) (low := Class.ofFormula (cofactor a false f))
      (high := Class.ofFormula (cofactor a true f)) ha
      (cofactor_eval a f false) (cofactor_eval a f true)
  constructor
  · intro t ht
    obtain ⟨hat, hrest⟩ := Bool.and_eq_true_iff.mp ht
    obtain ⟨hlt, hht⟩ := Bool.and_eq_true_iff.mp hrest
    exact (hsplit (RefinedAtom t)).mpr ⟨(atomLower_spec s hs a).2 t hat, hl.1 t hlt, hh.1 t hht⟩
  · intro t ht
    obtain ⟨hat, hlt, hht⟩ := (hsplit (RefinedAtom t)).mp ht
    exact Bool.and_eq_true_iff.mpr ⟨(operatorBits_exact a t).mpr hat.operator_upper,
      Bool.and_eq_true_iff.mpr ⟨hl.2 t hlt, hh.2 t hht⟩⟩

/-- Fuel exhaustion represents a declined computation, never an answer.
Cached constants are read too, just as in C's bounds procedure. -/
def tagBounds (rank : Formula (Fin ap) → Nat) : Nat → TagCache ap →
    Formula (Fin ap) → TagBoundsCache ap → Option (TagBounds × TagBoundsCache ap)
  | 0, _, _, _ => none
  | fuel+1, s, f, memo =>
    match lookupTagBounds f memo with
    | some b => some (b, memo)
    | none => do
      if equivalent f .ff || equivalent f .tt then
        let b : TagBounds := ⟨allFragmentBits, allFragmentBits⟩
        pure (b, (f, b) :: memo)
      else match (orderAtoms rank (modalAtoms f).eraseDups).find? (uses f) with
      | none => none
      | some a => do
        let (low, ml) ← tagBounds rank fuel s (cofactor a false f) memo
        let (high, mh) ← tagBounds rank fuel s (cofactor a true f) ml
        let b := meetBounds a s low high
        pure (b, (f, b) :: mh)

theorem tagBounds_spec (rank : Formula (Fin ap) → Nat) (fuel : Nat)
    (s : TagCache ap) (hs : s.Valid) (memo : TagBoundsCache ap) (hm : memo.Valid)
    (he : tagBounds rank fuel s f memo = some (b, out)) :
    b.Valid f ∧ out.Valid ∧ memo.Extends out ∧ lookupTagBounds f out = some b := by
  induction fuel generalizing f memo b out with
  | zero => simp [tagBounds] at he
  | succ fuel ih =>
    simp only [tagBounds] at he
    cases hc : lookupTagBounds f memo with
    | some bits =>
      simp only [hc, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨lookupTagBounds_valid memo hm hc, hm, .refl _, hc⟩
    | none =>
      simp only [hc] at he
      split at he
      · rename_i hconst
        cases Option.some.inj he
        have hv : (TagBounds.mk allFragmentBits allFragmentBits).Valid f := by
          refine ⟨?_, fun _ _ => rfl⟩
          intro t _
          rcases Bool.or_eq_true_iff.mp hconst with hf | hf
          · exact (constantClass_spec false).congr ((equivalent_exact _ _).mp hf).symm |>.2 t rfl
          · exact (constantClass_spec true).congr ((equivalent_exact _ _).mp hf).symm |>.2 t rfl
        refine ⟨hv, ?_, (TagBoundsCache.Extends.refl memo).remember hc, ?_⟩
        · intro e hm'
          rcases List.mem_cons.mp hm' with rfl | hm'
          · exact hv
          · exact hm e hm'
        · simp only [lookupTagBounds, (equivalent_exact f f).mpr rfl, ↓reduceIte]
      · cases ht : (orderAtoms rank (modalAtoms f).eraseDups).find? (uses f) with
        | none => simp [ht] at he
        | some a =>
          simp only [ht, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
          obtain ⟨⟨low, ml⟩, hl, ⟨high, mh⟩, hh, he⟩ := he
          obtain ⟨hvl, hml, hxl, _⟩ := ih _ hm hl
          obtain ⟨hvh, hmh, hxh, _⟩ := ih _ hml hh
          cases he
          have hv := meetBounds_valid s hs
            ((uses_exact _ _).mp (List.find?_some ht)) hvl hvh
          refine ⟨hv, ?_, (hxl.trans hxh).remember hc, ?_⟩
          · intro e hm'
            rcases List.mem_cons.mp hm' with rfl | hm'
            · exact hv
            · exact hmh e hm'
          · simp only [lookupTagBounds, (equivalent_exact f f).mpr rfl, ↓reduceIte]

structure QuickCache (ap : Nat) where
  tags : TagCache ap := {}
  bounds : TagBoundsCache ap := []

def QuickCache.Valid (s : QuickCache ap) : Prop := s.tags.Valid ∧ s.bounds.Valid

theorem QuickCache.empty_valid : ({} : QuickCache ap).Valid :=
  ⟨TagCache.empty_valid, fun _ h => by simp at h⟩

/-- Startup resets class tags only; quick bounds survive it. -/
def QuickCache.start (s : QuickCache ap) : QuickCache ap := {s with tags := s.tags.start}

theorem QuickCache.start_valid (s : QuickCache ap) (hs : s.Valid) : s.start.Valid :=
  ⟨TagCache.start_valid hs.1, hs.2⟩

def QuickCache.Extends (s t : QuickCache ap) : Prop :=
  s.tags.Extends t.tags ∧ s.bounds.Extends t.bounds

theorem QuickCache.Extends.refl (s : QuickCache ap) : s.Extends s := ⟨.refl _, .refl _⟩

theorem QuickCache.Extends.trans {s t u : QuickCache ap}
    (h : s.Extends t) (h' : t.Extends u) : s.Extends u := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- Quick lower answers and exact answers are separate observations.
Their union realizes predicate calls even if a class tag was cached before
an atom refinement. It need not realize an exposed full exact-bit query. -/
def quickClassifier (s : QuickCache ap) : TagClassifier ap := fun f t =>
  ((lookupTagBounds f s.bounds).map (fun b => b.low t)).getD false || cacheClassifier s.tags f t

theorem quickClassifier_sound (s : QuickCache ap) (hs : s.Valid) : (quickClassifier s).Sound := by
  intro f t ht
  rcases Bool.or_eq_true_iff.mp ht with ht | ht
  · cases hb : lookupTagBounds f s.bounds with
    | none => simp [hb] at ht
    | some b => exact (lookupTagBounds_valid _ hs.2 hb).1 t (by simpa [hb] using ht)
  · exact cacheClassifier_sound _ hs.1 f t ht

theorem quickClassifier_lower (s : QuickCache ap) (hs : s.Valid) : (quickClassifier s).Lower := by
  intro f t ht
  exact Bool.or_eq_true_iff.mpr (Or.inr (cacheClassifier_lower _ hs.1 f t ht))

theorem quickClassifier_congr (s : QuickCache ap)
    (he : Class.ofFormula f = Class.ofFormula g) : quickClassifier s f = quickClassifier s g := by
  funext t
  simp only [quickClassifier, lookupTagBounds_congr he, cacheClassifier_congr s.tags he]

def hasTags (rank : Formula (Fin ap) → Nat) (highFirst : Formula (Fin ap) → Bool)
    (fuel : Nat) (started : Bool) (f : Formula (Fin ap)) (mask : List FragmentTag)
    (s : QuickCache ap) : Option (Bool × QuickCache ap) := do
  let (b, memo) ← tagBounds rank fuel s.tags f s.bounds
  if mask.any b.low then pure (true, {s with bounds := memo})
  else if !mask.any b.high then pure (false, {s with bounds := memo})
  else
    let (bits, tags) ← defaultTags rank highFirst fuel started f s.tags
    pure (mask.any bits, ⟨tags, memo⟩)

theorem hasTags_spec (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (f : Formula (Fin ap)) (mask : List FragmentTag) (s : QuickCache ap) (hs : s.Valid)
    (he : hasTags rank highFirst fuel started f mask s = some (value, out)) :
    out.Valid ∧ s.Extends out ∧
      ∀ last, out.Extends last → last.Valid → mask.any (quickClassifier last f) = value := by
  simp only [hasTags, bind, Option.bind_eq_some_iff] at he
  obtain ⟨⟨b, memo⟩, hb, he⟩ := he
  obtain ⟨hbf, hmv, hmx, hread⟩ := tagBounds_spec rank fuel s.tags hs.1 _ hs.2 hb
  split at he
  · rename_i hl
    cases Option.some.inj he
    refine ⟨⟨hs.1, hmv⟩, ⟨.refl _, hmx⟩, ?_⟩
    intro last hx _
    obtain ⟨t, hm, ht⟩ := List.any_eq_true.mp hl
    change b.low t = true at ht
    apply List.any_eq_true.mpr
    exact ⟨t, hm, by simp [quickClassifier, hx.2 _ _ hread, ht]⟩
  · rename_i hl
    split at he
    · rename_i hh
      cases Option.some.inj he
      refine ⟨⟨hs.1, hmv⟩, ⟨.refl _, hmx⟩, ?_⟩
      intro last _ hv
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨t, hm, ht⟩ := List.any_eq_true.mp ht
      have hhigh := List.any_eq_true.mpr ⟨t, hm, hbf.2 t (quickClassifier_sound last hv f t ht)⟩
      simp [hhigh] at hh
    · rename_i hh
      simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at he
      obtain ⟨⟨bits, tags⟩, htags, he⟩ := he
      cases he
      refine ⟨⟨(defaultTags_sound rank highFirst fuel started _ _ _ _ hs.1 htags).1, hmv⟩,
        ⟨defaultTags_preserves rank highFirst fuel started _ _ _ _ htags, hmx⟩, ?_⟩
      intro last hx _
      have heq := defaultTags_read rank highFirst fuel started htags hx.1
      have hpoint (t : FragmentTag) (hm : t ∈ mask) : quickClassifier last f t = bits t := by
        have ht : b.low t = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          exact hl (List.any_eq_true.mpr ⟨t, hm, ht⟩)
        simp only [quickClassifier, hx.2 _ _ hread, Option.map_some, Option.getD_some,
          ht, Bool.false_or, heq]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨t, hm, ht⟩
        exact ⟨t, hm, (hpoint t hm) ▸ ht⟩
      · rintro ⟨t, hm, ht⟩
        exact ⟨t, hm, (hpoint t hm).symm ▸ ht⟩

/-- The exact interpreter `exec` remains available. This interpreter executes
the quick-predicate branches and threads every descendant bounds cell. -/
def TagProgram.execQuick (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool) :
    TagProgram ap α → QuickCache ap → Option (α × QuickCache ap)
  | .done a, s => some (a, s)
  | .query f k, s => do
    let (b, tags) ← defaultTags rank highFirst fuel started f s.tags
    (k b).execQuick rank highFirst fuel started {s with tags := tags}
  | .test f mask k, s => do
    let (b, s) ← hasTags rank highFirst fuel started f mask s
    (k b).execQuick rank highFirst fuel started s

/-- A full exact read and a predicate read have different realizations.
Only predicate-only programs may replace both by the quick classifier. -/
def TagProgram.evalSeparate (exactTags predicateTags : TagClassifier ap) : TagProgram ap α → α
  | .done a => a
  | .query f k => (k (exactTags f)).evalSeparate exactTags predicateTags
  | .test f mask k => (k (mask.any (predicateTags f))).evalSeparate exactTags predicateTags

def TagProgram.PredicateOnly : TagProgram ap α → Prop
  | .done _ => True
  | .query _ _ => False
  | .test _ _ k => ∀ b, (k b).PredicateOnly

theorem TagProgram.evalSeparate_predicateOnly (p : TagProgram ap α) (hp : p.PredicateOnly)
    (exactTags predicateTags : TagClassifier ap) :
    p.evalSeparate exactTags predicateTags = p.eval predicateTags := by
  induction p with
  | done _ => rfl
  | query _ _ _ => contradiction
  | test f mask k ih => exact ih (mask.any (predicateTags f)) (hp _)

theorem TagProgram.execQuick_spec (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (p : TagProgram ap α) (s : QuickCache ap) (hs : s.Valid)
    (he : p.execQuick rank highFirst fuel started s = some (a, out)) :
    out.Valid ∧ s.Extends out ∧ ∀ last, out.Extends last → last.Valid →
      p.evalSeparate (cacheClassifier last.tags) (quickClassifier last) = a := by
  induction p generalizing s with
  | done value =>
    cases Option.some.inj he
    exact ⟨hs, .refl _, fun _ _ _ => rfl⟩
  | query f k ih =>
    simp only [execQuick, Bind.bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨b, tags⟩, hb, he⟩ := he
    have hv : (QuickCache.mk tags s.bounds).Valid :=
      ⟨(defaultTags_sound rank highFirst fuel started _ _ _ _ hs.1 hb).1, hs.2⟩
    obtain ⟨hvo, hxo, hr⟩ := ih b _ hv he
    have hx : s.Extends ⟨tags, s.bounds⟩ :=
      ⟨defaultTags_preserves rank highFirst fuel started _ _ _ _ hb, .refl _⟩
    refine ⟨hvo, hx.trans hxo, ?_⟩
    intro last hlast hvlast
    simp only [evalSeparate, defaultTags_read rank highFirst fuel started hb (hxo.1.trans hlast.1)]
    exact hr last hlast hvlast
  | test f mask k ih =>
    simp only [execQuick, Bind.bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨b, sb⟩, hb, he⟩ := he
    obtain ⟨hvb, hxb, hread⟩ := hasTags_spec rank highFirst fuel started f mask s hs hb
    obtain ⟨hvo, hxo, hr⟩ := ih b sb hvb he
    refine ⟨hvo, hxb.trans hxo, ?_⟩
    intro last hlast hvlast
    simp only [evalSeparate, hread last (hxo.trans hlast) hvlast]
    exact hr last hlast hvlast

theorem TagProgram.quick_realizes (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (p : TagProgram ap α) (hp : p.PredicateOnly) (s : QuickCache ap) (hs : s.Valid)
    (he : p.execQuick rank highFirst fuel started s = some (a, out)) :
    (quickClassifier out).Sound ∧ (quickClassifier out).Lower ∧ p.eval (quickClassifier out) = a := by
  obtain ⟨hv, _, hr⟩ := p.execQuick_spec rank highFirst fuel started s hs he
  refine ⟨quickClassifier_sound out hv, quickClassifier_lower out hv, ?_⟩
  rw [← p.evalSeparate_predicateOnly hp (cacheClassifier out.tags)]
  exact hr out (.refl _) hv

theorem TagProgram.PredicateOnly.bind (p : TagProgram ap α) (hp : p.PredicateOnly)
    (k : α → TagProgram ap β) (hk : ∀ a, (k a).PredicateOnly) : (p.bind k).PredicateOnly := by
  induction p with
  | done a => exact hk a
  | query _ _ _ => contradiction
  | test f mask cont ih => exact fun b => ih b (hp b)

theorem mapSupported_predicateOnly
    (atomProgram : Formula (Fin ap) → TagProgram ap (Formula (Fin ap)))
    (hp : ∀ a, (atomProgram a).PredicateOnly) (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (memo : MappedCache ap) :
    (mapSupported atomProgram atoms f memo).PredicateOnly := by
  induction atoms generalizing f memo with
  | nil =>
    simp only [mapSupported]
    split
    · trivial
    · split
      · trivial
      · split <;> trivial
  | cons a atoms ih =>
    simp only [mapSupported]
    split
    · trivial
    · split
      · trivial
      · split
        · trivial
        · split
          · apply TagProgram.PredicateOnly.bind _ (hp a)
            intro v
            apply TagProgram.PredicateOnly.bind _ (ih _ _)
            intro low
            cases low with
            | none => trivial
            | some low =>
              apply TagProgram.PredicateOnly.bind _ (ih _ _)
              intro high
              cases high <;> trivial
          · exact ih _ _

theorem extractSupported_predicateOnly (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    (extractSupported rank f).PredicateOnly := by
  apply TagProgram.PredicateOnly.bind
  · apply mapSupported_predicateOnly
    intro a
    simp only [reduceAtomProgram]
    split
    · trivial
    · exact fun _ => trivial
  · intro _; trivial

theorem rhoSupported_predicateOnly (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    (rhoSupported rank f).PredicateOnly := by
  apply TagProgram.PredicateOnly.bind _ (extractSupported_predicateOnly rank f)
  intro first
  cases first with
  | none => trivial
  | some r =>
    intro yes
    dsimp only
    split
    · apply TagProgram.PredicateOnly.bind _ (extractSupported_predicateOnly rank _)
      intro second
      cases second with
      | none => trivial
      | some s => exact fun _ => trivial
    · trivial

/-- Supported REDUCE, protected extraction and retry now run C's predicate
path, preserving its actual shared tag/bounds history. -/
theorem rhoSupported_quick (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (s : QuickCache ap) (hs : s.Valid)
    (he : (rhoSupported rank f).execQuick rank highFirst fuel started s =
      some (some r, out)) :
    (quickClassifier out).Sound ∧ (quickClassifier out).Lower ∧
      Class.ofFormula r = Class.ofFormula (rhoTagged (quickClassifier out) f) := by
  obtain ⟨hsound, hlower, hr⟩ := TagProgram.quick_realizes rank highFirst fuel started
    (rhoSupported rank f) (rhoSupported_predicateOnly rank f) s hs he
  exact ⟨hsound, hlower, rhoSupported_spec _ (fun _ _ h => quickClassifier_congr out h) rank hr⟩

end Tlsf.Dpa.Impl
