import Init

namespace Tlsf
abbrev Letter (α : Type) := α → Bool
abbrev Word (α : Type) := Nat → Letter α

def InRange (len : Option Nat) (j : Nat) : Prop :=
  match len with | none => True | some n => j < n

inductive Formula (α : Type) where
  | tt | ff | ap (a : α)
  | neg (f : Formula α)
  | conj (f g : Formula α) | disj (f g : Formula α)
  | impl (f g : Formula α) | equiv (f g : Formula α)
  | next (f : Formula α) | strongNext (f : Formula α)
  | eventually (f : Formula α) | globally (f : Formula α)
  | until (f g : Formula α) | release (f g : Formula α)
  | weakUntil (f g : Formula α) | strongRelease (f g : Formula α)
  deriving DecidableEq

open Formula

def Formula.atoms : Formula α → List α
  | .tt | .ff => []
  | .ap a => [a]
  | .neg f | .next f | .strongNext f | .eventually f | .globally f => f.atoms
  | .conj f g | .disj f g | .impl f g | .equiv f g
  | .until f g | .release f g | .weakUntil f g | .strongRelease f g =>
      f.atoms ++ g.atoms

def AllFuture (len : Option Nat) (j : Nat) (p : Nat → Prop) : Prop :=
  ∀ k, j ≤ k → InRange len k → p k

def UntilAt (len : Option Nat) (j : Nat) (p q : Nat → Prop) : Prop :=
  ∃ k, j ≤ k ∧ InRange len k ∧ q k ∧ ∀ i, j ≤ i → i < k → p i

-- Every formula is false outside the word; recursive queries stay in range.
def Sat (len : Option Nat) (w : Word α) : Formula α → Nat → Prop
  | f, j => InRange len j ∧ match f with
    | .tt => True
    | .ff => False
    | .ap a => w j a = true
    | .neg f => ¬Sat len w f j
    | .conj f g => Sat len w f j ∧ Sat len w g j
    | .disj f g => Sat len w f j ∨ Sat len w g j
    | .impl f g => Sat len w f j → Sat len w g j
    | .equiv f g => Sat len w f j ↔ Sat len w g j
    | .next f => ¬InRange len (j+1) ∨ Sat len w f (j+1)
    | .strongNext f => InRange len (j+1) ∧ Sat len w f (j+1)
    | .eventually f => ∃ k, j ≤ k ∧ InRange len k ∧ Sat len w f k
    | .globally f => AllFuture len j (Sat len w f)
    | .until f g => UntilAt len j (Sat len w f) (Sat len w g)
    | .release f g => ¬UntilAt len j (fun k => ¬Sat len w f k) (fun k => ¬Sat len w g k)
    | .weakUntil f g => UntilAt len j (Sat len w f) (Sat len w g) ∨ AllFuture len j (Sat len w f)
    | .strongRelease f g => ¬(UntilAt len j (fun k => ¬Sat len w f k) (fun k => ¬Sat len w g k) ∨ AllFuture len j (fun k => ¬Sat len w f k))

theorem sat_inRange (h : Sat len w f j) : InRange len j := by
  cases f <;> exact h.1

theorem range_down {len : Option Nat} {i k : Nat} (hik : i ≤ k)
    (hk : InRange len k) : InRange len i := by
  cases len <;> simp_all [InRange]; omega

theorem future_congr {p q : Nat → Prop}
    (h : ∀ k, j ≤ k → InRange len k → (p k ↔ q k)) :
    AllFuture len j p ↔ AllFuture len j q := by
  constructor <;> intro hp k hj hk
  · exact (h k hj hk).mp (hp k hj hk)
  · exact (h k hj hk).mpr (hp k hj hk)

theorem until_congr {p q p' q' : Nat → Prop}
    (hp : ∀ k, j ≤ k → InRange len k → (p k ↔ p' k))
    (hq : ∀ k, j ≤ k → InRange len k → (q k ↔ q' k)) :
    UntilAt len j p q ↔ UntilAt len j p' q' := by
  constructor <;> rintro ⟨k, hj, hk, hqk, hi⟩
  · exact ⟨k, hj, hk, (hq k hj hk).mp hqk, fun i hji hik =>
      (hp i hji (range_down (Nat.le_of_lt hik) hk)).mp (hi i hji hik)⟩
  · exact ⟨k, hj, hk, (hq k hj hk).mpr hqk, fun i hji hik =>
      (hp i hji (range_down (Nat.le_of_lt hik) hk)).mpr (hi i hji hik)⟩

theorem sat_locality (f : Formula α) {len : Option Nat} {w v : Word α} {j : Nat}
    (h : ∀ k, j ≤ k → InRange len k → ∀ a, a ∈ f.atoms → w k a = v k a) :
    Sat len w f j ↔ Sat len v f j := by
  induction f generalizing j with
  | tt => rfl
  | ff => rfl
  | ap a =>
    simp only [Sat]; by_cases hj : InRange len j
    · rw [h j (Nat.le_refl j) hj a (by simp [Formula.atoms])]
    · simp [hj]
  | neg f ih =>
    simp only [Sat]; rw [ih (by simpa [Formula.atoms] using h)]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    have hf := ihf (fun k hj hk a ha => h k hj hk a (by simp [Formula.atoms, ha]))
    have hg := ihg (fun k hj hk a ha => h k hj hk a (by simp [Formula.atoms, ha]))
    simp only [Sat]; rw [hf, hg]
  | next f ih | strongNext f ih =>
    have hf := ih (j := j+1) (fun k hj hk a ha => h k (by omega) hk a ha)
    simp only [Sat]; rw [hf]
  | eventually f ih =>
    simp only [Sat]
    have hf : ∀ k, j ≤ k → InRange len k → (Sat len w f k ↔ Sat len v f k) :=
      fun k hj _ => ih (fun i hki hi a ha => h i (Nat.le_trans hj hki) hi a ha)
    constructor <;> rintro ⟨hj, k, hkj, hk, hs⟩
    · exact ⟨hj, k, hkj, hk, (hf k hkj hk).mp hs⟩
    · exact ⟨hj, k, hkj, hk, (hf k hkj hk).mpr hs⟩
  | globally f ih =>
    simp only [Sat]; apply and_congr_right; intro _
    exact future_congr (fun k hj _ => ih (fun i hki hi a ha => h i (Nat.le_trans hj hki) hi a ha))
  | «until» f g ihf ihg | release f g ihf ihg | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    have hf : ∀ k, j ≤ k → InRange len k → (Sat len w f k ↔ Sat len v f k) :=
      fun k hj _ => ihf (fun i hki hi a ha => h i (Nat.le_trans hj hki) hi a (by simp [Formula.atoms, ha]))
    have hg : ∀ k, j ≤ k → InRange len k → (Sat len w g k ↔ Sat len v g k) :=
      fun k hj _ => ihg (fun i hki hi a ha => h i (Nat.le_trans hj hki) hi a (by simp [Formula.atoms, ha]))
    have hu := until_congr hf hg
    have hn := until_congr (fun k hj hk => not_congr (hf k hj hk)) (fun k hj hk => not_congr (hg k hj hk))
    have hall := future_congr hf
    have halln := future_congr (fun k hj hk => not_congr (hf k hj hk))
    simp only [Sat]; first | rw [hu, hall] | rw [hn, halln] | rw [hu] | rw [hn]

def Boolean : Formula α → Prop
  | .tt | .ff | .ap _ => True
  | .neg f => Boolean f
  | .conj f g | .disj f g | .impl f g | .equiv f g => Boolean f ∧ Boolean g
  | _ => False

def evalBool (v : Letter α) : Formula α → Bool
  | .tt => true | .ff => false | .ap a => v a
  | .neg f => !(evalBool v f)
  | .conj f g => evalBool v f && evalBool v g
  | .disj f g => evalBool v f || evalBool v g
  | .impl f g => !(evalBool v f) || evalBool v g
  | .equiv f g => evalBool v f == evalBool v g
  | _ => false

theorem boolean_sat (h : Boolean f) (hj : InRange len j) :
    Sat len w f j ↔ evalBool (w j) f = true := by
  induction f with
  | tt | ff | ap a => simp [Sat, evalBool, hj]
  | neg f ih => simpa [Sat, evalBool, hj] using not_congr (ih h)
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [Boolean] at h
    simp only [Sat, hj, true_and, evalBool, ihf h.1, ihg h.2]
    cases evalBool (w j) f <;> cases evalBool (w j) g <;> decide
  | _ => contradiction

theorem evalBool_congr (f : Formula α) (v w : Letter α)
    (h : ∀ a, a ∈ f.atoms → v a = w a) : evalBool v f = evalBool w f := by
  induction f with
  | tt | ff => rfl
  | ap a => exact h a (by simp [Formula.atoms])
  | neg f ih => simp only [evalBool]; rw [ih h]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    have hf := ihf (fun a ha => h a (by simp [Formula.atoms, ha]))
    have hg := ihg (fun a ha => h a (by simp [Formula.atoms, ha]))
    simp only [evalBool]; rw [hf, hg]
  | _ => rfl

def subst [DecidableEq α] (d : α) (θ : Formula α) : Formula α → Formula α
  | .tt => .tt | .ff => .ff | .ap a => if a = d then θ else .ap a
  | .neg f => .neg (subst d θ f)
  | .conj f g => .conj (subst d θ f) (subst d θ g)
  | .disj f g => .disj (subst d θ f) (subst d θ g)
  | .impl f g => .impl (subst d θ f) (subst d θ g)
  | .equiv f g => .equiv (subst d θ f) (subst d θ g)
  | .next f => .next (subst d θ f)
  | .strongNext f => .strongNext (subst d θ f)
  | .eventually f => .eventually (subst d θ f)
  | .globally f => .globally (subst d θ f)
  | .until f g => .until (subst d θ f) (subst d θ g)
  | .release f g => .release (subst d θ f) (subst d θ g)
  | .weakUntil f g => .weakUntil (subst d θ f) (subst d θ g)
  | .strongRelease f g => .strongRelease (subst d θ f) (subst d θ g)

def setLetter [DecidableEq α] (d : α) (θ : Formula α) (v : Letter α) : Letter α :=
  fun a => if a = d then evalBool v θ else v a

def setWord [DecidableEq α] (d : α) (θ : Formula α) (w : Word α) : Word α :=
  fun j => setLetter d θ (w j)

theorem sat_subst [DecidableEq α] (hθ : Boolean θ) (f : Formula α) :
    Sat len w (subst d θ f) j ↔ Sat len (setWord d θ w) f j := by
  induction f generalizing j with
  | tt | ff => rfl
  | ap a =>
    by_cases ha : a = d
    · subst a; simp only [subst, ↓reduceIte, Sat, setWord, setLetter]
      by_cases hj : InRange len j
      · simp [hj, boolean_sat hθ hj]
      · simp only [hj, false_and, iff_false]; intro hs; exact hj (sat_inRange hs)
    · simp [subst, ha, Sat, setWord, setLetter]
  | neg f ih => simp only [subst, Sat]; rw [ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [subst, Sat]; rw [ihf, ihg]
  | next f ih | strongNext f ih => simp only [subst, Sat]; rw [ih]
  | eventually f ih => simp only [subst, Sat]; simp only [ih]
  | globally f ih => simp only [subst, Sat, AllFuture]; simp only [ih]
  | «until» f g ihf ihg | release f g ihf ihg | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    simp only [subst, Sat, UntilAt, AllFuture]; simp only [ihf, ihg]

theorem subst_absent [DecidableEq α] {f θ : Formula α} {d : α} (h : d ∉ f.atoms) : subst d θ f = f := by
  induction f with
  | tt | ff => rfl
  | ap a => simp_all [Formula.atoms, subst, eq_comm]
  | neg f ih | next f ih | strongNext f ih | eventually f ih | globally f ih =>
    simp_all [Formula.atoms, subst]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg
  | «until» f g ihf ihg | release f g ihf ihg | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    simp_all [Formula.atoms, subst]
end Tlsf
