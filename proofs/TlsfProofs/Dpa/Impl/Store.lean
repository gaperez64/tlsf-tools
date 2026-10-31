import TlsfProofs.Dpa.Impl.Dual

/-!
# Executable component interning and stable colour coordinates

`src/lib/dpa_dela.c:93` scans in insertion order, first comparing the stored
oriented formula, then (outside Büchi mode) its cached NNF dual. A miss
appends one Π₂-oriented component and returns its possibly complemented
colour. A colour's index is its insertion position, never its formula ID.

Equality tests are the executable canonical-class tests of `Classes.lean`.
The invariant relates the cached temporal dual to the stored formula's NNF
dual, not to its Boolean function complement. The theorem covers arbitrary
valid input stores, including both cache hits and fresh Σ₂ orientation.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

structure StoredComponent (ap : Nat) where
  formula : Formula (Fin ap)
  cachedDual : Formula (Fin ap)
  deriving DecidableEq

abbrev ComponentStore (ap : Nat) := List (StoredComponent ap)

def StoredComponent.Valid (e : StoredComponent ap) : Prop :=
  NNF e.formula ∧ classTag .pi2 e.formula = true ∧ NNF e.cachedDual ∧
    (Class.ofFormula e.cachedDual = Class.ofFormula (dual e.formula) ∨
      Class.ofFormula e.formula = Class.ofFormula (dual e.cachedDual))

def StoreValid (s : ComponentStore ap) : Prop := ∀ e, e ∈ s → e.Valid

/-- Stores grow by appending; old colour numbers are permanent. -/
def StoreExtends (s t : ComponentStore ap) : Prop := ∃ added, t = s ++ added

theorem StoreExtends.refl (s : ComponentStore ap) : StoreExtends s s :=
  ⟨[], by simp⟩

theorem StoreExtends.trans {s t u : ComponentStore ap}
    (hst : StoreExtends s t) (htu : StoreExtends t u) : StoreExtends s u := by
  obtain ⟨a, rfl⟩ := hst
  obtain ⟨b, rfl⟩ := htu
  exact ⟨a ++ b, by simp [List.append_assoc]⟩

theorem StoreExtends.length_le {s t : ComponentStore ap} (h : StoreExtends s t) :
    s.length ≤ t.length := by
  obtain ⟨a, rfl⟩ := h
  simp

theorem StoreExtends.index {s t : ComponentStore ap} (h : StoreExtends s t)
    (i : Nat) (hi : i < s.length) : t[i]? = s[i]? := by
  obtain ⟨a, rfl⟩ := h
  exact List.getElem?_append_left hi

structure ColourLiteral where
  index : Nat
  complement : Bool
  deriving DecidableEq, Repr

def ColourLiteral.eval (l : ColourLiteral) (v : Nat → Bool) : Bool :=
  if l.complement then !v l.index else v l.index

def ColourLiteral.shift (l : ColourLiteral) : ColourLiteral := ⟨l.index+1, l.complement⟩

def lookupComponent (shareDual : Bool) (f : Formula (Fin ap)) :
    ComponentStore ap → Option ColourLiteral
  | [] => none
  | e::s =>
    if equivalent e.formula f then some ⟨0, false⟩
    else if shareDual && equivalent e.cachedDual f then some ⟨0, true⟩
    else (lookupComponent shareDual f s).map ColourLiteral.shift

def freshComponent (f : Formula (Fin ap)) : StoredComponent ap :=
  ⟨orientedFormula f, if classTag .pi2 f then dual f else f⟩

def internComponent (buchi : Bool) (s : ComponentStore ap) (f : Formula (Fin ap)) :
    ComponentStore ap × ColourLiteral :=
  match lookupComponent (!buchi) f s with
  | some l => (s, l)
  | none => (s ++ [freshComponent f], ⟨s.length, complemented f⟩)

/-- Canonical class relation returned by the actual lookup, with its index. -/
def LiteralRepresents (s : ComponentStore ap) (l : ColourLiteral)
    (f : Formula (Fin ap)) : Prop :=
  ∃ e, s[l.index]? = some e ∧
    Class.ofFormula (if l.complement then e.cachedDual else e.formula) = Class.ofFormula f

theorem lookupComponent_represents (s : ComponentStore ap) (shareDual : Bool)
    (f : Formula (Fin ap)) (l : ColourLiteral)
    (hl : lookupComponent shareDual f s = some l) : LiteralRepresents s l f := by
  induction s generalizing l with
  | nil => simp [lookupComponent] at hl
  | cons e s ih =>
    simp only [lookupComponent] at hl
    split at hl
    · rename_i h
      cases Option.some.inj hl
      exact ⟨e, rfl, (equivalent_exact e.formula f).mp h⟩
    · split at hl
      · rename_i h
        cases Option.some.inj hl
        exact ⟨e, rfl, (equivalent_exact e.cachedDual f).mp (Bool.and_eq_true_iff.mp h).2⟩
      · cases ht : lookupComponent shareDual f s with
        | none => simp [ht] at hl
        | some k =>
          simp only [ht, Option.map_some, Option.some.injEq] at hl
          subst l
          obtain ⟨p, hp, hc⟩ := ih k ht
          exact ⟨p, by simpa [ColourLiteral.shift] using hp, hc⟩

theorem lookupComponent_positive (s : ComponentStore ap) (f : Formula (Fin ap))
    (l : ColourLiteral) (hl : lookupComponent false f s = some l) : l.complement = false := by
  induction s generalizing l with
  | nil => simp [lookupComponent] at hl
  | cons e s ih =>
    simp only [lookupComponent, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hl
    split at hl
    · cases Option.some.inj hl; rfl
    · cases ht : lookupComponent false f s with
      | none => simp [ht] at hl
      | some k =>
        simp only [ht, Option.map_some, Option.some.injEq] at hl
        subst l
        exact ih k ht

theorem freshComponent_valid (f : Formula (Fin ap)) (hn : NNF f)
    (ha : researchAdmitted f = true) : (freshComponent f).Valid := by
  cases hp : classTag .pi2 f with
  | false =>
    have hs : classTag .sigma2 f = true := by simpa [researchAdmitted, hp] using ha
    simp only [StoredComponent.Valid, freshComponent, orientedFormula, hp,
      Bool.false_eq_true, ↓reduceIte]
    exact ⟨dual_nnf f hn, classTag_sigma2_dual_pi2 f hn hs, hn, Or.inr trivial⟩
  | true =>
    simp only [StoredComponent.Valid, freshComponent, orientedFormula, hp, ↓reduceIte]
    exact ⟨hn, trivial, dual_nnf f hn, Or.inl trivial⟩

/-- Appending never changes an existing coordinate, including terminal ones. -/
theorem internComponent_prefix (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) : ∃ added, (internComponent buchi s f).1 = s ++ added := by
  unfold internComponent
  cases lookupComponent (!buchi) f s with
  | none => exact ⟨[freshComponent f], rfl⟩
  | some l => exact ⟨[], by simp⟩

theorem internComponent_preserves_index (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) (i : Nat) (hi : i < s.length) :
    (internComponent buchi s f).1[i]? = s[i]? := by
  obtain ⟨added, he⟩ := internComponent_prefix buchi s f
  rw [he, List.getElem?_append_left hi]

theorem internComponent_valid (buchi : Bool) (s : ComponentStore ap) (hs : StoreValid s)
    (f : Formula (Fin ap)) (hn : NNF f) (ha : researchAdmitted f = true) :
    StoreValid (internComponent buchi s f).1 := by
  unfold internComponent
  cases lookupComponent (!buchi) f s with
  | some l => exact hs
  | none =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hs e he
    · have he' := List.mem_singleton.mp he
      subst e
      exact freshComponent_valid f hn ha

theorem internComponent_represents (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) :
    LiteralRepresents (internComponent buchi s f).1 (internComponent buchi s f).2 f := by
  unfold internComponent
  cases hl : lookupComponent (!buchi) f s with
  | some l => exact lookupComponent_represents s (!buchi) f l hl
  | none =>
    refine ⟨freshComponent f, ?_, ?_⟩
    · simp
    · cases hp : classTag .pi2 f <;>
        simp [complemented, freshComponent, orientedFormula, hp]

theorem internComponent_bound (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) :
    (internComponent buchi s f).2.index < (internComponent buchi s f).1.length := by
  obtain ⟨_, he, _⟩ := internComponent_represents buchi s f
  exact (List.getElem?_eq_some_iff.mp he).choose

theorem internComponent_buchi_positive (s : ComponentStore ap) (f : Formula (Fin ap))
    (hp : classTag .pi2 f = true) : (internComponent true s f).2.complement = false := by
  unfold internComponent
  simp only [Bool.not_true]
  cases hl : lookupComponent false f s with
  | some l => exact lookupComponent_positive s f l hl
  | none => simp [complemented, hp]

/-- Executable fixed-coordinate product colours, with false outside the store. -/
def storeColours (s : ComponentStore ap) (w : Word (Fin ap)) (n i : Nat) : Bool :=
  match s[i]? with
  | none => false
  | some e => marks e.formula w n

noncomputable def storeTruth (s : ComponentStore ap) (w : Word (Fin ap)) (i : Nat) : Bool :=
  @decide (Inf (fun n => storeColours s w n i)) (Classical.propDecidable _)

theorem storeColour_language (s : ComponentStore ap) (hs : StoreValid s)
    (i : Nat) (e : StoredComponent ap) (he : s[i]? = some e) (w : Word (Fin ap)) :
    Inf (fun n => storeColours s w n i) ↔ Sat none w e.formula 0 := by
  have hv := hs e (List.mem_of_getElem? he)
  simpa only [storeColours, he] using pi2_language e.formula hv.1 hv.2.1 w

theorem class_language {f g : Formula (Fin ap)}
    (he : Class.ofFormula f = Class.ofFormula g) (w : Word (Fin ap)) (j : Nat) :
    Sat none w f j ↔ Sat none w g j := by
  rw [← ofFormula_holds f, ← ofFormula_holds g, he]

/-- Any literal in a valid store, including a cached-dual hit, denotes the
input language on the store's complete runs. -/
theorem literal_language (s : ComponentStore ap) (hs : StoreValid s)
    (l : ColourLiteral) (f : Formula (Fin ap)) (hl : LiteralRepresents s l f)
    (w : Word (Fin ap)) : l.eval (storeTruth s w) = true ↔ Sat none w f 0 := by
  classical
  obtain ⟨e, he, hc⟩ := hl
  have hv := hs e (List.mem_of_getElem? he)
  have ht := storeColour_language s hs l.index e he w
  cases hb : l.complement with
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hc
    simpa only [ColourLiteral.eval, hb, Bool.false_eq_true, ↓reduceIte,
      storeTruth, decide_eq_true_eq, ht] using class_language hc w 0
  | true =>
    simp only [hb, ↓reduceIte] at hc
    have hd : Sat none w e.cachedDual 0 ↔ ¬Sat none w e.formula 0 := by
      rcases hv.2.2.2 with h | h
      · exact (class_language h w 0).trans (dual_language e.formula w 0)
      · have hh := (class_language h w 0).trans (dual_language e.cachedDual w 0)
        simpa only [Classical.not_not] using (not_congr hh).symm
    simpa only [ColourLiteral.eval, hb, ↓reduceIte, storeTruth,
      Bool.not_eq_true', decide_eq_false_iff_not, ht] using
      hd.symm.trans (class_language hc w 0)

theorem internComponent_language (buchi : Bool) (s : ComponentStore ap) (hs : StoreValid s)
    (f : Formula (Fin ap)) (hn : NNF f) (ha : researchAdmitted f = true)
    (w : Word (Fin ap)) :
    (internComponent buchi s f).2.eval (storeTruth (internComponent buchi s f).1 w) = true ↔
      Sat none w f 0 :=
  literal_language _ (internComponent_valid buchi s hs f hn ha) _ _
    (internComponent_represents buchi s f) w

/-- Existing literals keep both their coordinate and their entire colour
stream, rather than only an existentially equivalent language. -/
theorem internComponent_preserves_colours (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) (w : Word (Fin ap)) (i : Nat) (hi : i < s.length) (n : Nat) :
    storeColours (internComponent buchi s f).1 w n i = storeColours s w n i := by
  simp only [storeColours, internComponent_preserves_index buchi s f i hi]

theorem internComponent_preserves_literal (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) (w : Word (Fin ap)) (l : ColourLiteral) (hl : l.index < s.length) :
    l.eval (storeTruth (internComponent buchi s f).1 w) = l.eval (storeTruth s w) := by
  have he : storeTruth (internComponent buchi s f).1 w l.index = storeTruth s w l.index := by
    unfold storeTruth
    congr 2
    funext n
    exact internComponent_preserves_colours buchi s f w l.index hl n
  simp only [ColourLiteral.eval, he]

theorem StoreExtends.literal {s t : ComponentStore ap} (h : StoreExtends s t)
    (w : Word (Fin ap)) (l : ColourLiteral) (hl : l.index < s.length) :
    l.eval (storeTruth t w) = l.eval (storeTruth s w) := by
  have he : storeTruth t w l.index = storeTruth s w l.index := by
    unfold storeTruth
    congr 2
    funext n
    simp only [storeColours, h.index l.index hl]
  simp only [ColourLiteral.eval, he]

def storeClasses (s : ComponentStore ap) (i : Fin s.length) : Class ap :=
  Class.ofFormula s[i.val].formula

theorem storeTruth_componentTruth (s : ComponentStore ap) (hs : StoreValid s)
    (w : Word (Fin ap)) (i : Fin s.length) :
    storeTruth s w i.val = componentTruth (storeClasses s) w i := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [storeTruth, componentTruth, decide_eq_true_eq]
  exact (storeColour_language s hs i.val s[i.val] (List.getElem?_eq_getElem i.isLt) w).trans
    (ofFormula_holds _).symm

theorem store_productColours (s : ComponentStore ap) (w : Word (Fin ap))
    (n : Nat) (i : Fin s.length) :
    productColours (storeClasses s) w n i = storeColours s w n i.val := by
  rw [product_colour]
  simp only [storeColours, List.getElem?_eq_getElem i.isLt, storeClasses, marks_exact]

end Tlsf.Dpa.Impl
