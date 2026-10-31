import TlsfProofs.Game

namespace Tlsf
inductive Role where
  | initially | preset | require | assume | assert | guarantee
  deriving DecidableEq, Repr

def Env : Role → Prop
  | .initially | .require | .assume => True
  | _ => False
instance (r : Role) : Decidable (Env r) := by cases r <;> simp [Env] <;> infer_instance

def covers (strict : Bool) (use defRole : Role) : Prop :=
  use = defRole ∨ defRole = .preset ∨ (use = .guarantee ∧ defRole = .assert) ∨
    (strict = false ∧ use = .assert ∧ defRole = .guarantee)
instance (s : Bool) (u d : Role) : Decidable (covers s u d) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem covers_refl : covers s r r := Or.inl rfl

theorem covers_trans (s : Bool) (u d e : Role) :
    covers s u d → covers s d e → covers s u e := by
  cases s <;> cases u <;> cases d <;> cases e <;> decide

structure Entry (α : Type) where
  role : Role
  formula : Formula α

open Formula

def Section (es : List (Entry α)) (r : Role) (len : Option Nat) (w : Word α) (j : Nat) : Prop :=
  ∀ e, e ∈ es → e.role = r → Sat len w e.formula j

def Initial (es : List (Entry α)) (len : Option Nat) (w : Word α) : Prop :=
  Section es .initially len w 0

def Environment (es : List (Entry α)) (len : Option Nat) (w : Word α) : Prop :=
  AllFuture len 0 (Section es .require len w) ∧ Section es .assume len w 0

-- An obligation position includes the initial condition and section guards.
def Enabled (strict : Bool) (es : List (Entry α)) (len : Option Nat)
    (w : Word α) (r : Role) (j : Nat) : Prop :=
  InRange len j ∧ Initial es len w ∧ match r with
    | .preset => j = 0
    | .assert => if strict then (∀ k, k ≤ j → Section es .require len w k)
        else Environment es len w
    | .guarantee => j = 0 ∧ Environment es len w
    | _ => False

def Objective (strict : Bool) (es : List (Entry α)) (len : Option Nat) (w : Word α) : Prop :=
  ∀ e, e ∈ es → ¬Env e.role → ∀ j, Enabled strict es len w e.role j → Sat len w e.formula j

theorem enabled_cover (hc : covers strict use defRole) (hd : ¬Env defRole)
    (hu : Enabled strict es len w use j) :
    ∃ k, k ≤ j ∧ Enabled strict es len w defRole k := by
  rcases hu with ⟨hj, hi, hu⟩
  rcases hc with he | he | ⟨he, hd'⟩ | ⟨hs, he, hd'⟩
  · subst defRole; exact ⟨j, Nat.le_refl _, hj, hi, hu⟩
  · subst defRole; exact ⟨0, Nat.zero_le _, range_down (Nat.zero_le _) hj, hi, rfl⟩
  · subst use; subst defRole
    rcases hu with ⟨rfl, hreq, ha⟩
    refine ⟨0, Nat.le_refl _, hj, hi, ?_⟩
    cases strict with
    | false => exact ⟨hreq, ha⟩
    | true => exact fun k hk => hreq k (Nat.zero_le _) (range_down hk hj)
  · subst strict; subst use; subst defRole
    exact ⟨0, Nat.zero_le _, range_down (Nat.zero_le _) hj, hi, rfl, hu⟩

-- Environment sections are the only source of section guards.
def SameEnvironment (es fs : List (Entry α)) (len : Option Nat) (w v : Word α) : Prop :=
  ∀ r, Env r → ∀ j, Section es r len w j ↔ Section fs r len v j

theorem enabled_congr (he : SameEnvironment es fs len w v) :
    Enabled s es len w r j ↔ Enabled s fs len v r j := by
  have hi := he .initially (by trivial) 0
  have hr := he .require (by trivial)
  have ha := he .assume (by trivial) 0
  unfold Enabled Initial Environment AllFuture
  cases r <;> cases s <;> simp only [hi, hr, ha]

def sectionFormula (es : List (Entry α)) (r : Role) : Formula α :=
  es.foldr (fun e f => if e.role = r then .conj e.formula f else f) .tt

theorem section_sat (hj : InRange len j) :
    Sat len w (sectionFormula es r) j ↔ Section es r len w j := by
  induction es with
  | nil => simp [sectionFormula, Sat, hj, Section]
  | cons e es ih =>
    change Sat len w (if e.role = r then .conj e.formula (sectionFormula es r)
      else sectionFormula es r) j ↔ _
    by_cases he : e.role = r
    · simp only [he, ↓reduceIte, Sat, hj, true_and, ih]
      simp [Section, he]
    · simp only [he, ↓reduceIte, ih]
      simp [Section, he]

def objectiveFormula (strict : Bool) (es : List (Entry α)) : Formula α :=
  let i := sectionFormula es .initially
  let p := sectionFormula es .preset
  let req := sectionFormula es .require
  let a := sectionFormula es .assume
  let asrt := sectionFormula es .assert
  let gu := sectionFormula es .guarantee
  let env := conj (globally req) a
  impl i (if strict then conj p (conj (weakUntil asrt (neg req)) (impl env gu))
    else conj p (impl env (conj (globally asrt) gu)))

theorem exists_least_nat {p : Nat → Prop} (h : ∃ n, p n) :
    ∃ n, p n ∧ ∀ k, k < n → ¬p k := by
  classical
  obtain ⟨n, hn⟩ := h
  have aux : ∀ n, (∃ k, k ≤ n ∧ p k) → ∃ k, p k ∧ ∀ i, i < k → ¬p i := by
    intro n; induction n with
    | zero => rintro ⟨k, hk, hp⟩; exact ⟨k, hp, fun i hi => by omega⟩
    | succ n ih =>
      intro hex
      by_cases old : ∃ k, k ≤ n ∧ p k
      · exact ih old
      · obtain ⟨k, hk, hp⟩ := hex
        refine ⟨k, hp, fun i hi hpi => old ⟨i, ?_, hpi⟩⟩
        omega
  exact aux n ⟨n, Nat.le_refl _, hn⟩

theorem weakUntil_guard (hj : InRange len 0) :
    Sat len w (.weakUntil f (.neg g)) 0 ↔
      ∀ j, InRange len j → (∀ k, k ≤ j → Sat len w g k) → Sat len w f j := by
  classical
  simp only [Sat, hj, true_and, UntilAt, AllFuture]
  constructor
  · intro h j hr hg
    rcases h with ⟨k, _, hk, hng, hf⟩ | hf
    · by_cases hkj : k ≤ j
      · exact False.elim (hng.2 (hg k hkj))
      · exact hf j (Nat.zero_le _) (by omega)
    · exact hf j (Nat.zero_le _) hr
  · intro h
    by_cases bad : ∃ k, InRange len k ∧ ¬Sat len w g k
    · obtain ⟨k, hk, hmin⟩ := exists_least_nat bad
      refine Or.inl ⟨k, Nat.zero_le _, hk.1, ⟨hk.1, hk.2⟩, ?_⟩
      intro j _ hjk
      apply h j (range_down (Nat.le_of_lt hjk) hk.1)
      intro i hij
      by_cases hn : Sat len w g i
      · exact hn
      · exact False.elim (hmin i (by omega) ⟨range_down hij (range_down (Nat.le_of_lt hjk) hk.1), hn⟩)
    · apply Or.inr
      intro j _ hr
      exact h j hr (fun k hk => by
        by_cases hn : Sat len w g k
        · exact hn
        · exact False.elim (bad ⟨k, range_down hk hr, hn⟩))

-- This identity connects the obligation model to the literal TLSF objective.
theorem objective_sat (h0 : InRange len 0) :
    Sat len w (objectiveFormula strict es) 0 ↔ Objective strict es len w := by
  have weak := weakUntil_guard (w := w) (f := sectionFormula es .assert)
    (g := sectionFormula es .require) h0
  have req : Sat len w (.globally (sectionFormula es .require)) 0 ↔
      AllFuture len 0 (Section es .require len w) := by
    simp only [Sat, h0, true_and]
    exact future_congr (fun _ _ hk => section_sat hk)
  have asrt : Sat len w (.globally (sectionFormula es .assert)) 0 ↔
      AllFuture len 0 (Section es .assert len w) := by
    simp only [Sat, h0, true_and]
    exact future_congr (fun _ _ hk => section_sat hk)
  have weak' : Sat len w (.weakUntil (sectionFormula es .assert)
      (.neg (sectionFormula es .require))) 0 ↔
      ∀ j, InRange len j → (∀ k, k ≤ j → Section es .require len w k) →
        Section es .assert len w j := by
    rw [weak]
    constructor <;> intro h j hj hs
    · exact (section_sat hj).mp (h j hj (fun k hk => (section_sat (range_down hk hj)).mpr (hs k hk)))
    · exact (section_sat hj).mpr (h j hj (fun k hk => (section_sat (range_down hk hj)).mp (hs k hk)))
  have hc : ∀ f g : Formula _, Sat len w (.conj f g) 0 ↔ Sat len w f 0 ∧ Sat len w g 0 :=
    fun _ _ => by simp only [Sat, h0, true_and]
  have himp : ∀ f g : Formula _, Sat len w (.impl f g) 0 ↔ (Sat len w f 0 → Sat len w g 0) :=
    fun _ _ => by simp only [Sat, h0, true_and]
  unfold objectiveFormula
  cases strict <;>
    simp only [Bool.false_eq_true, ↓reduceIte, himp, hc, section_sat h0, req, asrt, weak']
  all_goals
    constructor
    · intro h e he henv j hen
      cases er : e.role <;> simp only [er, Env, not_true_eq_false] at henv
      all_goals try contradiction
      · have hh : InRange len j ∧ Initial es len w ∧ j = 0 := by simpa [Enabled, er] using hen
        rcases hh with ⟨_, hi, rfl⟩
        exact (h hi).1 e he er
      · have hh := hen
        simp only [Enabled, er, Bool.false_eq_true, ↓reduceIte] at hh
        rcases hh with ⟨hj, hi, hs⟩
        first
        | exact ((h hi).2 hs).1 j (Nat.zero_le _) hj e he er
        | exact (h hi).2.1 j hj hs e he er
      · have hh : InRange len j ∧ Initial es len w ∧ j = 0 ∧ Environment es len w := by simpa [Enabled, er] using hen
        rcases hh with ⟨_, hi, rfl, hs⟩
        first | exact ((h hi).2 hs).2 e he er | exact (h hi).2.2 hs e he er
    · intro h hi
      refine ⟨?_, ?_⟩
      · intro e he er
        apply h e he (by simp [er, Env]) 0
        rw [er]; exact ⟨h0, hi, rfl⟩
      · first
        | intro hs
          constructor
          · intro j _ hj e he er
            apply h e he (by simp [er, Env]) j
            rw [er]; exact ⟨hj, hi, hs⟩
          · intro e he er
            apply h e he (by simp [er, Env]) 0
            rw [er]; exact ⟨h0, hi, rfl, hs⟩
        | constructor
          · intro j hj hs e he er
            apply h e he (by simp [er, Env]) j
            rw [er]; exact ⟨hj, hi, hs⟩
          · intro hs e he er
            apply h e he (by simp [er, Env]) 0
            rw [er]; exact ⟨h0, hi, rfl, hs⟩
end Tlsf
