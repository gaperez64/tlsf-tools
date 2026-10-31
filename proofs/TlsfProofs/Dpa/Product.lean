import TlsfProofs.Dpa.Component

/-! # STAGE2 §4: the fixed complete Boolean product.
There is one permanent coordinate per component. No coordinate, including a
sink, is removed, and the acceptance function never changes.
-/
namespace Tlsf.Dpa
variable {ap m : Nat}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Skeleton (m : Nat) := (Fin m → Bool) → Bool

def productRun (xs : Fin m → Class ap) (w : Word (Fin ap)) : Nat → (Fin m → Pair ap)
  | 0 => fun i => initial (xs i)
  | n+1 => fun i => (transition (w n) (productRun xs w n i)).target

def productColours (xs : Fin m → Class ap) (w : Word (Fin ap)) (n : Nat) : Fin m → Bool :=
  fun i => (transition (w n) (productRun xs w n i)).mark

theorem product_projection (xs : Fin m → Class ap) (w : Word (Fin ap)) (n : Nat) (i : Fin m) :
    productRun xs w n i = run (xs i) w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [productRun, run, ih]

theorem product_colour (xs : Fin m → Class ap) (w : Word (Fin ap)) (n : Nat) (i : Fin m) :
    productColours xs w n i = marks (xs i) w n := by
  simp only [productColours, product_projection, marks]

/-- The set S of infinitely recurring colours, as a finite Boolean vector. -/
def recurrentColours (colours : Nat → Fin m → Bool) : Fin m → Bool :=
  fun i => decide (Inf (fun n => colours n i))

/-- `α = β(Inf(i))`, for a fixed Boolean function β, including negation. -/
def EmersonLei (β : Skeleton m) (colours : Nat → Fin m → Bool) : Prop :=
  β (recurrentColours colours) = true

def componentTruth (xs : Fin m → Class ap) (w : Word (Fin ap)) : Fin m → Bool :=
  fun i => decide (Holds w 0 (xs i))

/-- STAGE2 §4: complete per-component equalities suffice for every Boolean
skeleton. A one-sided inclusion is deliberately not a hypothesis here. -/
theorem product_language (xs : Fin m → Class ap) (β : Skeleton m) (w : Word (Fin ap))
    (h : ∀ i, Inf (marks (xs i) w) ↔ Holds w 0 (xs i)) :
    EmersonLei β (productColours xs w) ↔ β (componentTruth xs w) = true := by
  have he : recurrentColours (productColours xs w) = componentTruth xs w := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [recurrentColours, componentTruth, decide_eq_true_eq, product_colour]
    exact h i
  unfold EmersonLei
  rw [he]

/-- Complemented coordinates have exactly Fin(0) truth on the same run. -/
theorem product_complement (xs : Fin m → Class ap) (w : Word (Fin ap)) (i : Fin m) :
    recurrentColours (productColours xs w) i = false ↔ FinMarks (marks (xs i) w) := by
  simp only [recurrentColours, product_colour, decide_eq_false_iff_not, complete_complement]

end
end Tlsf.Dpa
