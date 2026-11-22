import TlsfProofs.Objective

namespace Tlsf.Restriction

variable {α : Type} {θ : α → Formula α}

def mapWord (E : Letter α → Letter α) (w : Word α) : Word α :=
  fun n => E (w n)

def decode (θ : α → Formula α) (v : Letter α) : Letter α :=
  fun a => evalBool v (θ a)

-- Replacement formulas are inserted once, without substituting inside them.
def substAll (θ : α → Formula α) : Formula α → Formula α
  | .tt => .tt | .ff => .ff | .ap a => θ a
  | .neg f => .neg (substAll θ f)
  | .conj f g => .conj (substAll θ f) (substAll θ g)
  | .disj f g => .disj (substAll θ f) (substAll θ g)
  | .impl f g => .impl (substAll θ f) (substAll θ g)
  | .equiv f g => .equiv (substAll θ f) (substAll θ g)
  | .next f => .next (substAll θ f)
  | .strongNext f => .strongNext (substAll θ f)
  | .eventually f => .eventually (substAll θ f)
  | .globally f => .globally (substAll θ f)
  | .until f g => .until (substAll θ f) (substAll θ g)
  | .release f g => .release (substAll θ f) (substAll θ g)
  | .weakUntil f g => .weakUntil (substAll θ f) (substAll θ g)
  | .strongRelease f g => .strongRelease (substAll θ f) (substAll θ g)

theorem substAll_sat (hθ : ∀ a, Boolean (θ a)) (f : Formula α) :
    Sat len w (substAll θ f) j ↔ Sat len (mapWord (decode θ) w) f j := by
  induction f generalizing j with
  | tt | ff => rfl
  | ap a =>
    by_cases hj : InRange len j
    · simpa [substAll, Sat, mapWord, decode, hj] using boolean_sat (w := w) (hθ a) hj
    · simp only [substAll, Sat, hj, false_and, iff_false]
      exact fun hs => hj (sat_inRange hs)
  | neg f ih => simp only [substAll, Sat]; rw [ih]
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    simp only [substAll, Sat]; rw [ihf, ihg]
  | next f ih | strongNext f ih => simp only [substAll, Sat]; rw [ih]
  | eventually f ih => simp only [substAll, Sat]; simp only [ih]
  | globally f ih => simp only [substAll, Sat, AllFuture]; simp only [ih]
  | «until» f g ihf ihg | release f g ihf ihg
  | weakUntil f g ihf ihg | strongRelease f g ihf ihg =>
    simp only [substAll, Sat, UntilAt, AllFuture]; simp only [ihf, ihg]

example : substAll (fun a : Bool => if a then .ff else .ap true) (.ap false) =
    .ap true := rfl

structure InputDecoder (isIn : α → Bool) (E : Letter α → Letter α) : Prop where
  outputs_fixed : ∀ v a, isIn a = false → E v a = v a
  input_causal : ∀ v w, mask isIn v = mask isIn w →
    mask isIn (E v) = mask isIn (E w)

-- The simulated system sees its own decoded inputs and reconstructed history.
def restrictSystem (isIn : α → Bool) (E : Letter α → Letter α)
    (s : Strategy α) : Strategy α :=
  fun h i => s (replay isIn s (h.map E)) (mask isIn (E i))

variable {isIn : α → Bool} {E : Letter α → Letter α}

theorem replay_decode_history (D : InputDecoder isIn E) (s t : Strategy α)
    (i : Word α) (n : Nat) :
    replay isIn s ((history isIn t i n).map E) =
      history isIn s (mapWord E i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, List.map_cons, replay, ih, mapWord]
    exact congrArg (fun l => l :: history isIn s (mapWord E i) n)
      (move_mask (D.input_causal _ _ mask_move))

theorem play_input_decoder (D : InputDecoder isIn E) (s : Strategy α) (i : Word α) :
    mapWord E (play isIn (restrictSystem isIn E s) i) =
      play isIn s (mapWord E i) := by
  have hm : ∀ v, mask isIn (E (mask isIn v)) = mask isIn (E v) :=
    fun _ => D.input_causal _ _ mask_mask
  funext n a
  cases ha : isIn a with
  | false =>
    rw [mapWord, D.outputs_fixed _ _ ha]
    simp only [play, move, ha, Bool.false_eq_true, ↓reduceIte, restrictSystem,
      replay_decode_history D, hm]
    rfl
  | true =>
    have hi := congrFun (D.input_causal
      (play isIn (restrictSystem isIn E s) i n) (i n) mask_move) a
    simpa only [mask, ha, ↓reduceIte, mapWord, play, move] using hi

theorem realizable_input_restriction (hθ : ∀ a, Boolean (θ a))
    (D : InputDecoder isIn (decode θ)) :
    Realizable isIn f → Realizable isIn (substAll θ f) := by
  rintro ⟨s, hs⟩
  refine ⟨restrictSystem isIn (decode θ) s, fun i => ?_⟩
  apply (substAll_sat hθ f).mpr
  rw [play_input_decoder D]
  exact hs (mapWord (decode θ) i)

theorem unrealizable_input_restriction (hθ : ∀ a, Boolean (θ a))
    (D : InputDecoder isIn (decode θ)) :
    ¬Realizable isIn (substAll θ f) → ¬Realizable isIn f :=
  fun h hf => h (realizable_input_restriction hθ D hf)

theorem realizable_output_restriction (hθ : ∀ a, Boolean (θ a))
    (hT : KeepsInputs isIn (decode θ)) :
    Realizable isIn (substAll θ f) → Realizable isIn f := by
  rintro ⟨s, hs⟩
  refine ⟨decorate isIn (decode θ) s, fun i => ?_⟩
  rw [play_decorate hT]
  exact (substAll_sat hθ f).mp (hs i)

-- In particular, an AP representative has the same ownership as its source.
def OwnershipPreserving (isIn : α → Bool) (θ : α → Formula α) : Prop :=
  ∀ a b, b ∈ (θ a).atoms → isIn b = isIn a

theorem input_decoder (hfixed : ∀ a, isIn a = false → θ a = .ap a)
    (howner : OwnershipPreserving isIn θ) : InputDecoder isIn (decode θ) := by
  constructor
  · intro v a ha; simp [decode, hfixed a ha, evalBool]
  · intro v w h
    funext a
    cases ha : isIn a with
    | false => simp [mask, ha]
    | true =>
      simp only [mask, ha, ↓reduceIte, decode]
      apply evalBool_congr
      intro b hb
      have hi : isIn b = true := (howner a b hb).trans ha
      have hm := congrFun h b
      simpa [mask, hi] using hm

def identify (S : α → Bool) (r : α) : α → Formula α :=
  fun a => if S a then .ap r else .ap a

theorem identify_boolean : ∀ a, Boolean (identify S r a) := by
  intro a; cases ha : S a <;> simp [identify, ha, Boolean]

theorem identify_ownership (hS : ∀ a, S a = true → isIn a = owner)
    (hr : S r = true) : OwnershipPreserving isIn (identify S r) := by
  intro a b hb
  cases ha : S a with
  | false => have he : b = a := by simpa [identify, ha, Formula.atoms] using hb
             subst b; rfl
  | true => have he : b = r := by simpa [identify, ha, Formula.atoms] using hb
            subst b; rw [hS r hr, hS a ha]

theorem input_identification_decoder (hS : ∀ a, S a = true → isIn a = true)
    (hr : S r = true) : InputDecoder isIn (decode (identify S r)) := by
  apply input_decoder _ (identify_ownership hS hr)
  intro a ha
  have hn : S a = false := by cases h : S a <;> simp_all
  simp [identify, hn]

theorem output_identification_decoder (hS : ∀ a, S a = true → isIn a = false)
    (hr : S r = true) :
    KeepsInputs isIn (decode (identify S r)) ∧
      OwnershipPreserving isIn (identify S r) := by
  refine ⟨?_, identify_ownership hS hr⟩
  intro v a ha
  have hn : S a = false := by cases h : S a <;> simp_all
  simp [decode, identify, hn, evalBool]

def constants (S : α → Bool) (c : α → Bool) : α → Formula α :=
  fun a => if S a then (if c a then .tt else .ff) else .ap a

theorem constants_boolean : ∀ a, Boolean (constants S c a) := by
  intro a; cases hs : S a <;> cases hc : c a <;> simp [constants, hs, hc, Boolean]

theorem constants_ownership : OwnershipPreserving isIn (constants S c) := by
  intro a b hb
  cases hs : S a <;> cases hc : c a <;> simp [constants, hs, hc, Formula.atoms] at hb
  all_goals subst b; rfl

theorem constant_input_decoder (hS : ∀ a, S a = true → isIn a = true) :
    InputDecoder isIn (decode (constants S c)) := by
  apply input_decoder _ constants_ownership
  intro a ha
  have hn : S a = false := by cases h : S a <;> simp_all
  simp [constants, hn]

theorem constant_output_decoder (hO : ∀ a, O a = true → isIn a = false) :
    KeepsInputs isIn (decode (constants O c)) := by
  intro v a ha
  have hn : O a = false := by cases h : O a <;> simp_all
  simp [decode, constants, hn, evalBool]

theorem substAll_objective_sat (hθ : ∀ a, Boolean (θ a)) (h0 : InRange len 0) :
    Sat len w (substAll θ (objectiveFormula strict es)) 0 ↔
      Objective strict es len (mapWord (decode θ) w) := by
  rw [substAll_sat hθ, objective_sat h0]

theorem objective_input_restriction (hθ : ∀ a, Boolean (θ a))
    (D : InputDecoder isIn (decode θ)) :
    ¬Realizable isIn (substAll θ (objectiveFormula strict es)) →
      ¬Realizable isIn (objectiveFormula strict es) :=
  unrealizable_input_restriction hθ D

theorem objective_output_restriction (hθ : ∀ a, Boolean (θ a))
    (hT : KeepsInputs isIn (decode θ)) :
    Realizable isIn (substAll θ (objectiveFormula strict es)) →
      Realizable isIn (objectiveFormula strict es) :=
  realizable_output_restriction hθ hT

-- Polarity cannot be swapped: identifying two inputs makes p ↔ q tautological,
-- while the original environment can choose p=false, q=true. Conversely,
-- fixing a controllable p to false destroys realizability of the objective p.
theorem input_identification_polarity :
    let isIn : Bool → Bool := fun _ => true
    let θ := identify (fun _ => true) false
    let f : Formula Bool := .equiv (.ap false) (.ap true)
    InputDecoder isIn (decode θ) ∧
      Realizable isIn (substAll θ f) ∧ ¬Realizable isIn f := by
  dsimp only
  refine ⟨input_identification_decoder (fun _ _ => rfl) rfl, ?_, ?_⟩
  · refine ⟨fun _ _ _ => false, fun i => ?_⟩
    simp [substAll, identify, Sat, InRange]
  · rintro ⟨s, hs⟩
    have h := hs (fun _ a => a)
    simp [Sat, InRange, play, move] at h

theorem output_constant_polarity :
    let isIn : Bool → Bool := fun _ => false
    let θ := constants (fun _ => true) (fun _ => false)
    KeepsInputs isIn (decode θ) ∧ Realizable isIn (.ap false) ∧
      ¬Realizable isIn (substAll θ (.ap false)) := by
  dsimp only
  refine ⟨constant_output_decoder (fun _ _ => rfl), ?_, ?_⟩
  · refine ⟨fun _ _ _ => true, fun i => ?_⟩
    simp [Sat, InRange, play, move]
  · rintro ⟨s, hs⟩
    have h := hs (fun _ _ => false)
    simp [substAll, constants, Sat, InRange] at h

end Tlsf.Restriction
