import TlsfProofs.Dpa.Impl.Dual

/-! Uncached component coordinates for the reference construction.
Every occurrence appends a fresh, Π₂-oriented component. The append lemmas
justify the indices in the compiled Boolean acceptance; they assert no C
allocation, cache, lookup, or call-order correspondence. -/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

structure StoredComponent (ap : Nat) where
  formula : Formula (Fin ap)
  dualFormula : Formula (Fin ap)
  deriving DecidableEq

abbrev ComponentStore (ap : Nat) := List (StoredComponent ap)

def StoredComponent.Valid (e : StoredComponent ap) : Prop :=
  NNF e.formula ∧ classTag .pi2 e.formula = true ∧ NNF e.dualFormula ∧
    (Class.ofFormula e.dualFormula = Class.ofFormula (dual e.formula) ∨
      Class.ofFormula e.formula = Class.ofFormula (dual e.dualFormula))

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

def freshComponent (f : Formula (Fin ap)) : StoredComponent ap :=
  ⟨orientedFormula f, if classTag .pi2 f then dual f else f⟩

def appendComponent (_buchi : Bool) (s : ComponentStore ap) (f : Formula (Fin ap)) :
    ComponentStore ap × ColourLiteral :=
  (s ++ [freshComponent f], ⟨s.length, complemented f⟩)

/-- Canonical class relation returned by the fresh occurrence, with its index. -/
def LiteralRepresents (s : ComponentStore ap) (l : ColourLiteral)
    (f : Formula (Fin ap)) : Prop :=
  ∃ e, s[l.index]? = some e ∧
    Class.ofFormula (if l.complement then e.dualFormula else e.formula) = Class.ofFormula f

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
theorem appendComponent_prefix (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) : ∃ added, (appendComponent buchi s f).1 = s ++ added := by
  exact ⟨[freshComponent f], rfl⟩

theorem appendComponent_preserves_index (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) (i : Nat) (hi : i < s.length) :
    (appendComponent buchi s f).1[i]? = s[i]? := by
  obtain ⟨added, he⟩ := appendComponent_prefix buchi s f
  rw [he, List.getElem?_append_left hi]

theorem appendComponent_valid (buchi : Bool) (s : ComponentStore ap) (hs : StoreValid s)
    (f : Formula (Fin ap)) (hn : NNF f) (ha : researchAdmitted f = true) :
    StoreValid (appendComponent buchi s f).1 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hs e he
  · have he' := List.mem_singleton.mp he
    subst e
    exact freshComponent_valid f hn ha

theorem appendComponent_represents (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) :
    LiteralRepresents (appendComponent buchi s f).1 (appendComponent buchi s f).2 f := by
  refine ⟨freshComponent f, ?_, ?_⟩
  · simp [appendComponent]
  · cases hp : classTag .pi2 f <;>
      simp [appendComponent, complemented, freshComponent, orientedFormula, hp]

theorem appendComponent_bound (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) :
    (appendComponent buchi s f).2.index < (appendComponent buchi s f).1.length := by
  obtain ⟨_, he, _⟩ := appendComponent_represents buchi s f
  exact (List.getElem?_eq_some_iff.mp he).choose

theorem appendComponent_buchi_positive (s : ComponentStore ap) (f : Formula (Fin ap))
    (hp : classTag .pi2 f = true) : (appendComponent true s f).2.complement = false := by
  simp [appendComponent, complemented, hp]

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

/-- Any literal in a valid store, including a dual orientation, denotes the
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
    have hd : Sat none w e.dualFormula 0 ↔ ¬Sat none w e.formula 0 := by
      rcases hv.2.2.2 with h | h
      · exact (class_language h w 0).trans (dual_language e.formula w 0)
      · have hh := (class_language h w 0).trans (dual_language e.dualFormula w 0)
        simpa only [Classical.not_not] using (not_congr hh).symm
    simpa only [ColourLiteral.eval, hb, ↓reduceIte, storeTruth,
      Bool.not_eq_true', decide_eq_false_iff_not, ht] using
      hd.symm.trans (class_language hc w 0)

theorem appendComponent_language (buchi : Bool) (s : ComponentStore ap) (hs : StoreValid s)
    (f : Formula (Fin ap)) (hn : NNF f) (ha : researchAdmitted f = true)
    (w : Word (Fin ap)) :
    (appendComponent buchi s f).2.eval (storeTruth (appendComponent buchi s f).1 w) = true ↔
      Sat none w f 0 :=
  literal_language _ (appendComponent_valid buchi s hs f hn ha) _ _
    (appendComponent_represents buchi s f) w

/-- Existing literals keep both their coordinate and their entire colour
stream, rather than only an existentially equivalent language. -/
theorem appendComponent_preserves_colours (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) (w : Word (Fin ap)) (i : Nat) (hi : i < s.length) (n : Nat) :
    storeColours (appendComponent buchi s f).1 w n i = storeColours s w n i := by
  simp only [storeColours, appendComponent_preserves_index buchi s f i hi]

theorem appendComponent_preserves_literal (buchi : Bool) (s : ComponentStore ap)
    (f : Formula (Fin ap)) (w : Word (Fin ap)) (l : ColourLiteral) (hl : l.index < s.length) :
    l.eval (storeTruth (appendComponent buchi s f).1 w) = l.eval (storeTruth s w) := by
  have he : storeTruth (appendComponent buchi s f).1 w l.index = storeTruth s w l.index := by
    unfold storeTruth
    congr 2
    funext n
    exact appendComponent_preserves_colours buchi s f w l.index hl n
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
