import TlsfProofs.Objective

namespace Tlsf
structure Definition (α : Type) where
  name : α
  value : Formula α
  role : Role
  flip : Bool

def Definition.entry (e : Definition α) : Entry α :=
  ⟨e.role, .globally (if e.flip then .equiv e.value (.ap e.name)
    else .equiv (.ap e.name) e.value)⟩

variable [DecidableEq α]
variable {ds es : List (Definition α)} {e : Definition α} {v w : Letter α}
  {rank : α → Nat} {a : α} {f : Formula α}

-- The C loop substitutes in list order. Letter composition therefore runs
-- from the tail to the head, as required by the substitution identity.
def substPass (ds : List (Definition α)) (f : Formula α) : Formula α :=
  match ds with
  | [] => f
  | e :: es => substPass es (subst e.name e.value f)

def letterPass (ds : List (Definition α)) (v : Letter α) : Letter α :=
  match ds with
  | [] => v
  | e :: es => setLetter e.name e.value (letterPass es v)

def substPasses (ds : List (Definition α)) : Nat → Formula α → Formula α
  | 0, f => f
  | n+1, f => substPasses ds n (substPass ds f)

def normalize (ds : List (Definition α)) : Nat → Letter α → Letter α
  | 0, v => v
  | n+1, v => letterPass ds (normalize ds n v)

def residual (ds : List (Definition α)) (passes : Nat) (kept : List (Entry α)) : List (Entry α) :=
  kept.map (fun e => ⟨e.role, substPasses ds passes e.formula⟩)

def original (kept : List (Entry α)) (ds : List (Definition α)) : List (Entry α) :=
  kept ++ ds.map Definition.entry

theorem sat_substPass {w : Word α} (hb : ∀ e ∈ ds, Boolean e.value) :
    Sat len w (substPass ds f) j ↔ Sat len (fun k => letterPass ds (w k)) f j := by
  induction ds generalizing f w with
  | nil => rfl
  | cons e es ih =>
    rw [substPass, ih (fun x hx => hb x (by simp [hx])), sat_subst (hb e (by simp))]
    rfl

theorem sat_substPasses {w : Word α} (hb : ∀ e ∈ ds, Boolean e.value) :
    Sat len w (substPasses ds passes f) j ↔
      Sat len (fun k => normalize ds passes (w k)) f j := by
  induction passes generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [substPasses, ih, sat_substPass hb]
    rfl

def Defined (ds : List (Definition α)) (a : α) : Prop := ∃ e ∈ ds, e.name = a

def Agrees (p : α → Prop) (v w : Letter α) : Prop := ∀ a, p a → v a = w a

def Below (ds : List (Definition α)) (rank : α → Nat) (t : Nat) (a : α) : Prop :=
  ¬Defined ds a ∨ rank a < t

theorem pass_untouched (h : ¬Defined ds a) : letterPass ds v a = v a := by
  induction ds with
  | nil => rfl
  | cons e es ih =>
    have hn : a ≠ e.name := fun he => h ⟨e, by simp, he.symm⟩
    simp only [letterPass, setLetter, hn, ↓reduceIte]
    exact ih (fun ⟨d, hd, ha⟩ => h ⟨d, by simp [hd], ha⟩)

theorem pass_congr_on (p : α → Prop)
    (hc : ∀ e ∈ es, p e.name → ∀ a, a ∈ e.value.atoms → p a)
    (ha : Agrees p v w) : Agrees p (letterPass es v) (letterPass es w) := by
  induction es with
  | nil => exact ha
  | cons e es ih =>
    have hs := ih (fun d hd => hc d (by simp [hd]))
    intro a hp
    by_cases he : a = e.name
    · subst a
      simp only [letterPass, setLetter, ↓reduceIte]
      exact evalBool_congr _ _ _ (fun b hb => hs b (hc e (by simp) hp b hb))
    · simpa only [letterPass, setLetter, he, ↓reduceIte] using hs a hp

theorem pass_preserves_on (p : α → Prop)
    (hc : ∀ e ∈ es, p e.name → ∀ a, a ∈ e.value.atoms → p a)
    (heq : ∀ e ∈ es, p e.name → v e.name = evalBool v e.value)
    (ha : Agrees p w v) : Agrees p (letterPass es w) v := by
  induction es with
  | nil => exact ha
  | cons e es ih =>
    have hs := ih (fun d hd => hc d (by simp [hd])) (fun d hd => heq d (by simp [hd]))
    intro a hp
    by_cases he : a = e.name
    · subst a
      simp only [letterPass, setLetter, ↓reduceIte]
      rw [heq e (by simp) hp]
      exact evalBool_congr _ _ _ (fun b hb => hs b (hc e (by simp) hp b hb))
    · simpa only [letterPass, setLetter, he, ↓reduceIte] using hs a hp

-- The rank condition is used only for dependencies that are also eliminated.
def Ranked (ds : List (Definition α)) (rank : α → Nat) : Prop :=
  ∀ e ∈ ds, ∀ d ∈ ds, d.name ∈ e.value.atoms → rank d.name < rank e.name

omit [DecidableEq α] in
theorem below_closed (hr : Ranked ds rank) (he : e ∈ ds)
    (hp : Below ds rank t e.name) (ha : a ∈ e.value.atoms) : Below ds rank t a := by
  rcases hp with hn | hp
  · exact False.elim (hn ⟨e, he, rfl⟩)
  · by_cases hd : Defined ds a
    · obtain ⟨d, hd, rfl⟩ := hd
      exact Or.inr (Nat.lt_trans (hr e he d hd ha) hp)
    · exact Or.inl hd

theorem pass_improves (hr : Ranked ds rank) (ha : Agrees (Below ds rank t) v w) :
    Agrees (Below ds rank (t+1)) (letterPass ds v) (letterPass ds w) := by
  have hc : ∀ e ∈ ds, Below ds rank t e.name → ∀ a, a ∈ e.value.atoms → Below ds rank t a :=
    fun e he hp a hm => below_closed hr he hp hm
  have hit : ∀ es : List (Definition α), (∀ e ∈ es, e ∈ ds) →
      ∀ a, Defined es a → rank a < t+1 → letterPass es v a = letterPass es w a := by
    intro es; induction es with
    | nil => intro _ a hh; obtain ⟨_, hh, _⟩ := hh; contradiction
    | cons e es ih =>
      intro sub a hh hrt
      have sub' : ∀ d ∈ es, d ∈ ds := fun d hd => sub d (by simp [hd])
      have hs := pass_congr_on (Below ds rank t) (fun d hd => hc d (sub' d hd)) ha
      by_cases he : a = e.name
      · subst a
        simp only [letterPass, setLetter, ↓reduceIte]
        apply evalBool_congr
        intro b hb
        apply hs b
        by_cases hd : Defined ds b
        · obtain ⟨d, hd, rfl⟩ := hd
          exact Or.inr (by have := hr e (sub e (by simp)) d hd hb; omega)
        · exact Or.inl hd
      · have hm : Defined es a := by
          obtain ⟨d, hd, hda⟩ := hh
          rcases List.mem_cons.mp hd with rfl | hd
          · exact False.elim (he hda.symm)
          · exact ⟨d, hd, hda⟩
        simpa only [letterPass, setLetter, he, ↓reduceIte] using ih sub' a hm hrt
  intro a hp
  rcases hp with hn | hrank
  · rw [pass_untouched hn, pass_untouched hn]; exact ha a (Or.inl hn)
  · by_cases hd : Defined ds a
    · exact hit ds (fun _ h => h) a hd hrank
    · rw [pass_untouched hd, pass_untouched hd]; exact ha a (Or.inl hd)

theorem normalize_contraction (hr : Ranked ds rank)
    (ha : ∀ a, ¬Defined ds a → v a = w a) :
    Agrees (Below ds rank n) (normalize ds n v) (normalize ds n w) := by
  induction n with
  | zero => intro a hp; rcases hp with h | h
            · exact ha a h
            · omega
  | succ n ih => exact pass_improves hr ih

theorem normalize_commute : normalize ds n (letterPass ds v) = letterPass ds (normalize ds n v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [normalize, ih]

theorem normalize_fixed (hr : Ranked ds rank) (bound : ∀ e ∈ ds, rank e.name < passes) :
    letterPass ds (normalize ds passes v) = normalize ds passes v := by
  rw [← normalize_commute]
  have ha := normalize_contraction (v := letterPass ds v) (w := v) (n := passes) hr
    (fun a hn => pass_untouched hn)
  funext a
  apply ha a
  by_cases hd : Defined ds a
  · obtain ⟨e, he, rfl⟩ := hd; exact Or.inr (bound e he)
  · exact Or.inl hd

theorem pass_fixed_equations (hn : (ds.map Definition.name).Nodup)
    (hf : letterPass ds v = v) : ∀ e ∈ ds, v e.name = evalBool v e.value := by
  induction ds with
  | nil => simp
  | cons e es ih =>
    have hn' := List.nodup_cons.mp hn
    have untouched : ¬Defined es e.name := by
      rintro ⟨d, hd, he⟩
      exact hn'.1 (List.mem_map.mpr ⟨d, hd, he⟩)
    have tail : letterPass es v = v := by
      funext a
      by_cases he : a = e.name
      · subst a; exact pass_untouched untouched
      · have := congrFun hf a
        simpa only [letterPass, setLetter, he, ↓reduceIte] using this
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · have hh := congrFun hf d.name
      simpa only [letterPass, tail, setLetter, ↓reduceIte] using hh.symm
    · exact ih hn'.2 tail d hd

theorem normalize_definitions (hr : Ranked ds rank)
    (bound : ∀ e ∈ ds, rank e.name < passes) (hn : (ds.map Definition.name).Nodup) :
    ∀ e ∈ ds, normalize ds passes v e.name = evalBool (normalize ds passes v) e.value :=
  pass_fixed_equations hn (normalize_fixed hr bound)
end Tlsf
