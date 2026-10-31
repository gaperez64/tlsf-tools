import TlsfProofs.Examples

namespace Tlsf.Rewrites
open Formula

-- The expanded LTL syntax is called Formula in the existing core.
abbrev Ltl := Formula

def Exact (fin : Bool) (f g : Ltl α) : Prop :=
  ∀ len, (fin = true ∨ len = none) → ∀ w j, InRange len j →
    (Sat len w f j ↔ Sat len w g j)

theorem Exact.refl (f : Ltl α) : Exact fin f f := fun _ _ _ _ _ => Iff.rfl
theorem Exact.symm (h : Exact fin f g) : Exact fin g f :=
  fun len hl w j hj => (h len hl w j hj).symm
theorem Exact.trans (h : Exact fin f g) (h' : Exact fin g k) : Exact fin f k :=
  fun len hl w j hj => (h len hl w j hj).trans (h' len hl w j hj)

def map_children (tr : Ltl α → Ltl α) : Ltl α → Ltl α
  | .neg f => .neg (tr f)
  | .conj f g => .conj (tr f) (tr g)
  | .disj f g => .disj (tr f) (tr g)
  | .impl f g => .impl (tr f) (tr g)
  | .equiv f g => .equiv (tr f) (tr g)
  | .next f => .next (tr f)
  | .strongNext f => .strongNext (tr f)
  | .eventually f => .eventually (tr f)
  | .globally f => .globally (tr f)
  | .until f g => .until (tr f) (tr g)
  | .release f g => .release (tr f) (tr g)
  | .weakUntil f g => .weakUntil (tr f) (tr g)
  | .strongRelease f g => .strongRelease (tr f) (tr g)
  | f => f

-- Congruence comes before any transformation soundness theorem. The premise
-- only needs the immediate children, so it is usable as an induction step.
theorem exact_congr (f : Ltl α) (tr : Ltl α → Ltl α)
    (h : ∀ c, c ∈ (match f with
      | .neg a | .next a | .strongNext a | .eventually a | .globally a => [a]
      | .conj a b | .disj a b | .impl a b | .equiv a b | .until a b
      | .release a b | .weakUntil a b | .strongRelease a b => [a,b]
      | _ => []) → Exact fin c (tr c)) : Exact fin f (map_children tr f) := by
  intro len hl w j hj
  have hc : ∀ c, c ∈ (match f with
      | .neg a | .next a | .strongNext a | .eventually a | .globally a => [a]
      | .conj a b | .disj a b | .impl a b | .equiv a b | .until a b
      | .release a b | .weakUntil a b | .strongRelease a b => [a,b]
      | _ => []) → ∀ k, InRange len k → (Sat len w c k ↔ Sat len w (tr c) k) :=
    fun c hm k hk => h c hm len hl w k hk
  cases f with
  | tt | ff | ap _ => rfl
  | neg a => simp only [map_children, Sat]; rw [hc a (by simp) j hj]
  | conj a b | disj a b | impl a b | equiv a b =>
    simp only [map_children, Sat]
    rw [hc a (by simp) j hj, hc b (by simp) j hj]
  | next a | strongNext a =>
    simp only [map_children, Sat]
    by_cases hk : InRange len (j+1)
    · rw [hc a (by simp) (j+1) hk]
    · have h₁ : ¬Sat len w a (j+1) := fun hs => hk (sat_inRange hs)
      have h₂ : ¬Sat len w (tr a) (j+1) := fun hs => hk (sat_inRange hs)
      simp [hk, h₁, h₂]
  | eventually a =>
    simp only [map_children, Sat]
    exact and_congr Iff.rfl (exists_congr fun k => and_congr_right fun _ =>
      and_congr_right fun hk => hc a (by simp) k hk)
  | globally a =>
    simp only [map_children, Sat]
    exact and_congr Iff.rfl (future_congr fun k _ hk => hc a (by simp) k hk)
  | «until» a b | release a b | weakUntil a b | strongRelease a b =>
    have ha := fun k (_ : j ≤ k) hk => hc a (by simp) k hk
    have hb := fun k (_ : j ≤ k) hk => hc b (by simp) k hk
    have hu := until_congr ha hb
    have hn := until_congr (fun k h hk => not_congr (ha k h hk))
      (fun k h hk => not_congr (hb k h hk))
    have hg := future_congr ha
    have hgn := future_congr (fun k h hk => not_congr (ha k h hk))
    simp only [map_children, Sat]
    first | rw [hu, hg] | rw [hn, hgn] | rw [hu] | rw [hn]

-- Substitution by formulas, with no Boolean restriction: this is a congruence
-- theorem, not substitution into a word by a causal decoder.
def bind (σ : α → Ltl β) : Ltl α → Ltl β
  | .tt => .tt
  | .ff => .ff
  | .ap a => σ a
  | .neg a => .neg (bind σ a)
  | .conj a b => .conj (bind σ a) (bind σ b)
  | .disj a b => .disj (bind σ a) (bind σ b)
  | .impl a b => .impl (bind σ a) (bind σ b)
  | .equiv a b => .equiv (bind σ a) (bind σ b)
  | .next a => .next (bind σ a)
  | .strongNext a => .strongNext (bind σ a)
  | .eventually a => .eventually (bind σ a)
  | .globally a => .globally (bind σ a)
  | .until a b => .until (bind σ a) (bind σ b)
  | .release a b => .release (bind σ a) (bind σ b)
  | .weakUntil a b => .weakUntil (bind σ a) (bind σ b)
  | .strongRelease a b => .strongRelease (bind σ a) (bind σ b)

theorem bind_exact (σ τ : α → Ltl β) (h : ∀ a, Exact fin (σ a) (τ a))
    (f : Ltl α) : Exact fin (bind σ f) (bind τ f) := by
  intro len hl w j hj
  induction f generalizing j with
  | tt | ff => exact Iff.rfl
  | ap a => exact h a len hl w j hj
  | neg a ih => simp only [bind, Sat]; rw [ih j hj]
  | conj a b iha ihb | disj a b iha ihb | impl a b iha ihb | equiv a b iha ihb =>
    simp only [bind, Sat]; rw [iha j hj, ihb j hj]
  | next a ih | strongNext a ih =>
    simp only [bind, Sat]
    by_cases hk : InRange len (j+1)
    · rw [ih (j+1) hk]
    · have h₁ : ¬Sat len w (bind σ a) (j+1) := fun hs => hk (sat_inRange hs)
      have h₂ : ¬Sat len w (bind τ a) (j+1) := fun hs => hk (sat_inRange hs)
      simp [hk, h₁, h₂]
  | eventually a ih =>
    simp only [bind, Sat]
    exact and_congr Iff.rfl (exists_congr fun k => and_congr_right fun _ =>
      and_congr_right fun hk => ih k hk)
  | globally a ih =>
    simp only [bind, Sat]
    exact and_congr Iff.rfl (future_congr fun k _ hk => ih k hk)
  | «until» a b iha ihb | release a b iha ihb | weakUntil a b iha ihb | strongRelease a b iha ihb =>
    have ha := fun k (_ : j ≤ k) hk => iha (j := k) hk
    have hb := fun k (_ : j ≤ k) hk => ihb (j := k) hk
    have hu := until_congr ha hb
    have hn := until_congr (fun k h hk => not_congr (ha k h hk))
      (fun k h hk => not_congr (hb k h hk))
    have hg := future_congr ha
    have hgn := future_congr (fun k h hk => not_congr (ha k h hk))
    simp only [bind, Sat]
    first | rw [hu, hg] | rw [hn, hgn] | rw [hu] | rw [hn]

-- An atom `none` is a hole; `some a` is an ordinary atom. In particular this
-- includes every one-hole context, even under negation or implication.
abbrev Context (α : Type) := Ltl (Option α)

def Context.fill (c : Context α) (f : Ltl α) : Ltl α :=
  bind (fun a => match a with | none => f | some a => .ap a) c

theorem context_exact (c : Context α) (h : Exact fin f g) :
    Exact fin (c.fill f) (c.fill g) := by
  apply bind_exact
  intro a; cases a with
  | none => exact h
  | some a => exact Exact.refl _

theorem not_until_dual {p q : Nat → Prop} :
    (¬UntilAt len j (fun k => ¬p k) (fun k => ¬q k)) ↔
      UntilAt len j q (fun k => p k ∧ q k) ∨ AllFuture len j q := by
  classical
  constructor
  · intro h
    by_cases hp : ∃ k, j ≤ k ∧ InRange len k ∧ p k
    · obtain ⟨k, ⟨hjk, hk, hpk⟩, hmin⟩ := exists_least_nat hp
      have hq : ∀ i, j ≤ i → i ≤ k → q i := by
        intro i hji hik
        apply Classical.byContradiction; intro hn
        exact h ⟨i, hji, range_down hik hk, hn, fun t hjt hti hpt =>
          hmin t (by omega) ⟨hjt, range_down (by omega) hk, hpt⟩⟩
      exact Or.inl ⟨k, hjk, hk, ⟨hpk, hq k hjk (Nat.le_refl _)⟩,
        fun i hji hik => hq i hji (Nat.le_of_lt hik)⟩
    · apply Or.inr
      intro k hjk hk
      apply Classical.byContradiction; intro hn
      exact h ⟨k, hjk, hk, hn, fun i hji hik hpi =>
        hp ⟨i, hji, range_down (Nat.le_of_lt hik) hk, hpi⟩⟩
  · rintro (⟨k, hjk, hk, ⟨hpk, hqk⟩, hq⟩ | hq) ⟨t, hjt, ht, hnqt, hnp⟩
    · by_cases htk : t < k
      · exact hnqt (hq t hjt htk)
      · by_cases hkt : k < t
        · exact hnp k hjk hkt hpk
        · have he : t = k := by omega
          exact hnqt (he ▸ hqk)
    · exact hnqt (hq t hjt ht)

theorem not_weakUntil_dual {p q : Nat → Prop} :
    (¬(UntilAt len j (fun k => ¬p k) (fun k => ¬q k) ∨
      AllFuture len j (fun k => ¬p k))) ↔
      UntilAt len j q (fun k => p k ∧ q k) := by
  classical
  constructor
  · intro h
    have hr := not_until_dual.mp (fun hu => h (Or.inl hu))
    rcases hr with hu | hg
    · exact hu
    · have hp : ∃ k, j ≤ k ∧ InRange len k ∧ p k := by
        apply Classical.byContradiction; intro hn
        apply h; right
        intro k hjk hk hpk
        exact hn ⟨k, hjk, hk, hpk⟩
      obtain ⟨k, hjk, hk, hpk⟩ := hp
      exact ⟨k, hjk, hk, ⟨hpk, hg k hjk hk⟩,
        fun i hji hik => hg i hji (range_down (Nat.le_of_lt hik) hk)⟩
  · intro hu h
    rcases h with hn | hn
    · exact (not_until_dual.mpr (Or.inl hu)) hn
    · obtain ⟨k, hjk, hk, ⟨hpk, _⟩, _⟩ := hu
      exact hn k hjk hk hpk

theorem release_eq (hj : InRange len j) :
    Sat len w (release a b) j ↔
      Sat len w (weakUntil b (conj a b)) j := by
  have hu := until_congr (len := len) (j := j)
    (p := Sat len w b) (q := fun k => Sat len w a k ∧ Sat len w b k)
    (p' := Sat len w b) (q' := Sat len w (conj a b))
    (fun _ _ _ => Iff.rfl) (fun _ _ hk => by simp [Sat, hk])
  simp only [Sat, hj, true_and]
  rw [not_until_dual]
  exact or_congr (by simpa only [Sat] using hu) Iff.rfl

theorem strongRelease_eq (hj : InRange len j) :
    Sat len w (strongRelease a b) j ↔
      Sat len w («until» b (conj a b)) j := by
  simp only [Sat, hj, true_and]
  rw [not_weakUntil_dual]
  exact until_congr (fun _ _ _ => Iff.rfl) (fun _ _ hk => by simp [hk])

theorem eventually_idem (hj : InRange len j) :
    Sat len w (eventually (eventually a)) j ↔ Sat len w (eventually a) j := by
  simp only [Sat, hj, true_and]
  constructor
  · rintro ⟨k, hjk, _, _, t, hkt, ht, ha⟩
    exact ⟨t, Nat.le_trans hjk hkt, ht, ha⟩
  · rintro ⟨k, hjk, hk, ha⟩
    exact ⟨j, Nat.le_refl _, hj, hj, k, hjk, hk, ha⟩

theorem globally_idem (hj : InRange len j) :
    Sat len w (globally (globally a)) j ↔ Sat len w (globally a) j := by
  simp only [Sat, hj, true_and, AllFuture]
  constructor
  · intro h k hjk hk; exact (h j (Nat.le_refl _) hj).2 k hjk hk
  · intro h k hjk hk; exact ⟨hk, fun t hkt ht => h t (Nat.le_trans hjk hkt) ht⟩

theorem until_false_left (hj : InRange len j) :
    Sat len w («until» ff b) j ↔ Sat len w b j := by
  simp only [Sat, hj, true_and, UntilAt]
  constructor
  · rintro ⟨k, hjk, _, hb, hp⟩
    have he : j = k := by
      apply Classical.byContradiction; intro hn
      exact (hp j (Nat.le_refl _) (by omega)).2
    exact he ▸ hb
  · intro hb; exact ⟨j, Nat.le_refl _, hj, hb, fun i hji hik => by omega⟩

theorem until_true_left (hj : InRange len j) :
    Sat len w («until» tt b) j ↔ Sat len w (eventually b) j := by
  simp only [Sat, hj, true_and, UntilAt]
  constructor
  · rintro ⟨k, hjk, hk, hb, _⟩; exact ⟨k, hjk, hk, hb⟩
  · rintro ⟨k, hjk, hk, hb⟩
    exact ⟨k, hjk, hk, hb, fun i _ hik => ⟨range_down (Nat.le_of_lt hik) hk, trivial⟩⟩

theorem until_true_right (hj : InRange len j) :
    Sat len w («until» a tt) j :=
  ⟨hj, j, Nat.le_refl _, hj, ⟨hj, trivial⟩, fun i hji hik => by omega⟩

theorem until_false_right : ¬Sat len w («until» a ff) j := by
  rintro ⟨_, k, _, _, hk, _⟩; exact hk.2

theorem globally_false (hj : InRange len j) : ¬Sat len w (globally ff) j := by
  intro h; exact (h.2 j (Nat.le_refl _) hj).2

theorem globally_true {w : Word α} (hj : InRange len j) : Sat len w (globally (tt : Ltl α)) j :=
  ⟨hj, fun _ _ hk => ⟨hk, trivial⟩⟩

theorem eventually_true {w : Word α} (hj : InRange len j) : Sat len w (eventually (tt : Ltl α)) j :=
  ⟨hj, j, Nat.le_refl _, hj, ⟨hj, trivial⟩⟩

theorem eventually_false {w : Word α} : ¬Sat len w (eventually (ff : Ltl α)) j := by
  rintro ⟨_, k, _, _, hk⟩; exact hk.2

theorem route_push_g_in (hj : InRange len j) :
    Sat len w (globally (conj a b)) j ↔
      Sat len w (conj (globally a) (globally b)) j := by
  simp only [Sat, hj, true_and, AllFuture]
  constructor
  · intro h; exact ⟨fun k hjk hk => (h k hjk hk).2.1,
      fun k hjk hk => (h k hjk hk).2.2⟩
  · rintro ⟨ha, hb⟩ k hjk hk; exact ⟨hk, ha k hjk hk, hb k hjk hk⟩

theorem push_f_in (hj : InRange len j) :
    Sat len w (eventually (disj a b)) j ↔
      Sat len w (disj (eventually a) (eventually b)) j := by
  simp only [Sat, hj, true_and]
  constructor
  · rintro ⟨k, hjk, hk, _, ha | hb⟩
    · exact Or.inl ⟨k, hjk, hk, ha⟩
    · exact Or.inr ⟨k, hjk, hk, hb⟩
  · rintro (⟨k, hjk, hk, ha⟩ | ⟨k, hjk, hk, hb⟩)
    · exact ⟨k, hjk, hk, hk, Or.inl ha⟩
    · exact ⟨k, hjk, hk, hk, Or.inr hb⟩

theorem route_push_x_in (hj : InRange len j) :
    Sat len w (next (conj a b)) j ↔
      Sat len w (conj (next a) (next b)) j := by
  classical
  by_cases hk : InRange len (j+1) <;> simp [Sat, hj, hk]

theorem route_push_strong_x_in (hj : InRange len j) :
    Sat len w (strongNext (conj a b)) j ↔
      Sat len w (conj (strongNext a) (strongNext b)) j := by
  by_cases hk : InRange len (j+1) <;> simp [Sat, hj, hk]

theorem push_x_or (hj : InRange len j) :
    Sat len w (next (disj a b)) j ↔
      Sat len w (disj (next a) (next b)) j := by
  classical
  by_cases hk : InRange len (j+1) <;> simp [Sat, hj, hk]

def to_nnf (f : Ltl α) (polarity finite : Bool) : Ltl α :=
  match f with
  | .tt => if polarity then .tt else .ff
  | .ff => if polarity then .ff else .tt
  | .ap a => if polarity then .ap a else .neg (.ap a)
  | .neg a => to_nnf a (!polarity) finite
  | .conj a b => if polarity then
      .conj (to_nnf a polarity finite) (to_nnf b polarity finite) else
      .disj (to_nnf a polarity finite) (to_nnf b polarity finite)
  | .disj a b => if polarity then
      .disj (to_nnf a polarity finite) (to_nnf b polarity finite) else
      .conj (to_nnf a polarity finite) (to_nnf b polarity finite)
  | .impl a b => if polarity then
      .disj (to_nnf a (!polarity) finite) (to_nnf b polarity finite) else
      .conj (to_nnf a (!polarity) finite) (to_nnf b polarity finite)
  | .equiv a b => if polarity then
      .conj (.disj (to_nnf a false finite) (to_nnf b true finite))
            (.disj (to_nnf b false finite) (to_nnf a true finite)) else
      .disj (.conj (to_nnf a true finite) (to_nnf b false finite))
            (.conj (to_nnf b true finite) (to_nnf a false finite))
  | .next a => if polarity || !finite then .next (to_nnf a polarity finite)
      else .strongNext (to_nnf a polarity finite)
  | .strongNext a => if polarity then .strongNext (to_nnf a polarity finite)
      else .next (to_nnf a polarity finite)
  | .globally a => if polarity then .globally (to_nnf a polarity finite)
      else .eventually (to_nnf a polarity finite)
  | .eventually a => if polarity then .eventually (to_nnf a polarity finite)
      else .globally (to_nnf a polarity finite)
  | .until a b => if polarity then
      .until (to_nnf a polarity finite) (to_nnf b polarity finite) else
      .release (to_nnf a polarity finite) (to_nnf b polarity finite)
  | .release a b => if polarity then
      .release (to_nnf a polarity finite) (to_nnf b polarity finite) else
      .until (to_nnf a polarity finite) (to_nnf b polarity finite)
  | .weakUntil a b => if polarity then
      .weakUntil (to_nnf a polarity finite) (to_nnf b polarity finite) else
      .strongRelease (to_nnf a polarity finite) (to_nnf b polarity finite)
  | .strongRelease a b => if polarity then
      .strongRelease (to_nnf a polarity finite) (to_nnf b polarity finite) else
      .weakUntil (to_nnf a polarity finite) (to_nnf b polarity finite)

theorem nnf_sat (hl : fin = true ∨ len = none) (f : Ltl α) (pol : Bool)
    (w : Word α) (hj : InRange len j) :
    Sat len w (to_nnf f pol fin) j ↔ (if pol then Sat len w f j else ¬Sat len w f j) := by
  classical
  induction f generalizing j pol with
  | tt | ff | ap _ => cases pol <;> simp [to_nnf, Sat, hj]
  | neg a ih => cases pol <;> simp [to_nnf, Sat, hj, ih]
  | conj a b iha ihb | disj a b iha ihb | impl a b iha ihb | equiv a b iha ihb =>
    cases pol <;> simp [to_nnf, Sat, hj, iha, ihb]
    all_goals grind
  | next a ih | strongNext a ih =>
    have hnone : fin = false → len = none := by intro hf; rcases hl with h | h; simp_all; exact h
    cases pol <;> cases fin <;> by_cases hk : InRange len (j+1)
    all_goals simp_all [to_nnf, Sat, InRange]
  | globally a ih | eventually a ih =>
    have hf (p : Bool) := future_congr (j := j) (fun k _ hk => ih (j := k) p hk)
    have he (p : Bool) :
        (∃ k, j ≤ k ∧ InRange len k ∧ Sat len w (to_nnf a p fin) k) ↔
        ∃ k, j ≤ k ∧ InRange len k ∧ (if p then Sat len w a k else ¬Sat len w a k) :=
      exists_congr fun k => and_congr_right fun _ => and_congr_right fun hk => ih p hk
    cases pol <;> simp only [to_nnf, Bool.false_eq_true, ↓reduceIte, Sat, hj, true_and]
    all_goals simp only [hf, he]
    all_goals simp [AllFuture]
  | «until» a b iha ihb | release a b iha ihb | weakUntil a b iha ihb | strongRelease a b iha ihb =>
    have hu (p : Bool) := until_congr (j := j)
      (fun k _ hk => iha (j := k) p hk) (fun k _ hk => ihb (j := k) p hk)
    have hn (p : Bool) := until_congr (j := j)
      (fun k (_ : j ≤ k) hk => not_congr (iha (j := k) p hk))
      (fun k (_ : j ≤ k) hk => not_congr (ihb (j := k) p hk))
    have hg (p : Bool) := future_congr (j := j) (fun k _ hk => iha (j := k) p hk)
    have hgn (p : Bool) := future_congr (j := j)
      (fun k (_ : j ≤ k) hk => not_congr (iha (j := k) p hk))
    cases pol <;> simp [to_nnf, Sat, hj, hu, hn, hg, hgn]
    all_goals grind

theorem nnf_exact (f : Ltl α) (fin : Bool) :
    Exact fin (to_nnf f true fin) f ∧ Exact fin (to_nnf f false fin) (neg f) := by
  constructor
  · intro len hl w j hj; simpa using nnf_sat hl f true w hj
  · intro len hl w j hj; simpa [Sat, hj] using nnf_sat hl f false w hj

theorem nnf_infinite_mode_finite_failure (w : Word Examples.Signal) :
    ¬(Sat (some 1) w (to_nnf (neg (next Examples.P)) true false) 0 ↔
      Sat (some 1) w (neg (next Examples.P)) 0) := by
  have h := Examples.issue85_negation w
  simpa [to_nnf] using (show ¬(Sat (some 1) w (next (neg Examples.P)) 0 ↔
    Sat (some 1) w (neg (next Examples.P)) 0) from fun he => h.1 (he.mp h.2))

theorem release_false_right (hj : InRange len j) : ¬Sat len w (release a ff) j := by
  intro h
  exact h.2 ⟨j, Nat.le_refl _, hj, (fun hf => hf.2), fun i hji hij => by omega⟩

theorem release_true_right (hj : InRange len j) : Sat len w (release a tt) j := by
  refine ⟨hj, ?_⟩
  rintro ⟨k, _, hk, hn, _⟩; exact hn ⟨hk, trivial⟩

theorem release_false_left (hj : InRange len j) :
    Sat len w (release ff b) j ↔ Sat len w (globally b) j := by
  classical
  simp only [Sat, hj, true_and, UntilAt, AllFuture]
  constructor
  · intro h k hjk hk
    apply Classical.byContradiction; intro hn
    exact h ⟨k, hjk, hk, hn, fun _ _ _ hf => hf.2⟩
  · intro h ⟨k, hjk, hk, hn, _⟩; exact hn (h k hjk hk)

theorem release_true_left (hj : InRange len j) :
    Sat len w (release tt b) j ↔ Sat len w b j := by
  classical
  simp only [Sat, hj, true_and, UntilAt]
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    exact h ⟨j, Nat.le_refl _, hj, hn, fun i hji hij => by omega⟩
  · intro hb ⟨k, hjk, hk, hn, hp⟩
    by_cases he : j = k
    · exact hn (he ▸ hb)
    · exact hp j (Nat.le_refl _) (by omega) ⟨hj, trivial⟩

theorem weakUntil_false_left (hj : InRange len j) :
    Sat len w (weakUntil ff b) j ↔ Sat len w b j := by
  have hu := until_false_left (w := w) (b := b) hj
  have hg := globally_false (w := w) hj
  simp only [Sat, hj, true_and] at hu hg ⊢
  rw [hu]
  simpa only [and_false] using or_iff_left hg

def simplify_weak_local [DecidableEq α] (f : Ltl α) (finite : Bool) : Ltl α :=
  match f with
  | .neg a => if a = .tt then .ff else if a = .ff then .tt else
      match a with | .neg b => b | _ => f
  | .conj a b => if a = .ff ∨ b = .ff then .ff else
      if a = .tt then b else if b = .tt then a else if a = b then a else f
  | .disj a b => if a = .tt ∨ b = .tt then .tt else
      if a = .ff then b else if b = .ff then a else if a = b then a else f
  | .impl a b => if a = .ff ∨ b = .tt then .tt else
      if a = .tt then b else if b = .ff then .neg a else f
  | .equiv a b => if a = .tt then b else if b = .tt then a else
      if a = .ff then .neg b else if b = .ff then .neg a else
      if a = b then .tt else f
  | .next a => if a = .tt then .tt else if !finite ∧ a = .ff then .ff else f
  | .strongNext a => if a = .ff then .ff else f
  | .eventually a => if a = .tt then .tt else if a = .ff then .ff else
      match a with | .eventually _ => a | _ => f
  | .globally a => if a = .tt then .tt else if a = .ff then .ff else
      match a with | .globally _ => a | _ => f
  | .until a b => if b = .tt then .tt else if b = .ff then .ff else
      if a = .ff then b else if a = .tt then .eventually b else f
  | .release a b => if b = .ff then .ff else if b = .tt then .tt else
      if a = .ff then .globally b else if a = .tt then b else f
  | .weakUntil a b => if a = .tt then .tt else if b = .tt then .tt else
      if a = .ff then b else if b = .ff then .globally a else f
  | .strongRelease a b => if b = .ff then .ff else if a = .ff then .ff else
      if b = .tt then .eventually a else if a = .tt then b else f
  | _ => f

theorem simplify_exact [DecidableEq α] (f : Ltl α) :
    Exact fin (simplify_weak_local f fin) f := by
  classical
  intro len hl w j hj
  cases f with
  | tt | ff | ap _ => rfl
  | neg a => cases a <;> simp [simplify_weak_local, Sat, hj]
  | conj a b | disj a b | impl a b | equiv a b =>
    simp only [simplify_weak_local]
    repeat (any_goals split)
    all_goals simp_all only [Sat, true_and, not_false_eq_true]
    all_goals grind [Sat]
  | next a =>
    simp only [simplify_weak_local]
    repeat (any_goals split)
    all_goals simp_all [Sat, InRange]
    all_goals grind
  | strongNext a =>
    simp only [simplify_weak_local]; split
    · subst a; simp [Sat, hj]
    · rfl
  | eventually a | globally a =>
    cases a <;> simp only [simplify_weak_local]
    all_goals simp only [reduceCtorEq, ↓reduceIte, eventually_true hj, eventually_false,
      globally_true hj, globally_false hj, eventually_idem hj, globally_idem hj]
    all_goals simp [Sat, hj]
  | «until» a b =>
    simp only [simplify_weak_local]
    repeat (any_goals split)
    all_goals simp_all only [until_true_right hj, until_false_right, until_false_left hj,
      until_true_left hj]
    all_goals simp [Sat, hj]
  | release a b =>
    simp only [simplify_weak_local]
    repeat (any_goals split)
    all_goals simp_all only [release_false_right hj, release_true_right hj,
      release_false_left hj, release_true_left hj]
    all_goals simp [Sat, hj]
  | weakUntil a b =>
    simp only [simplify_weak_local]
    repeat (any_goals split)
    all_goals simp_all only [weakUntil_false_left hj]
    all_goals simp_all only [Sat, UntilAt, AllFuture]
    all_goals simp_all
    all_goals grind [range_down]
  | strongRelease a b =>
    simp only [simplify_weak_local]
    repeat (any_goals split)
    all_goals simp_all only [Sat, UntilAt, AllFuture]
    all_goals simp_all
    all_goals grind [range_down]

structure Flags where
  nnf : Bool := false
  noWeakUntil : Bool := false
  noRelease : Bool := false
  noStrongRelease : Bool := false
  noFinally : Bool := false
  noGlobally : Bool := false
  pushGIn : Bool := false
  pushFIn : Bool := false
  pushXIn : Bool := false
  pullGOut : Bool := false
  pullFOut : Bool := false
  pullXOut : Bool := false
  simplifyWeak : Bool := false
  finite : Bool := false
  deriving DecidableEq

def apply_local [DecidableEq α] (f : Ltl α) (flags : Flags) : Ltl α :=
  match f, flags.noWeakUntil with
  | .weakUntil a b, true => .disj (.until a b) (.globally a)
  | _, _ =>
    match f, flags.noRelease with
    | .release a b, true => .weakUntil b (.conj a b)
    | _, _ =>
      match f, flags.noStrongRelease with
      | .strongRelease a b, true => .until b (.conj a b)
      | _, _ =>
        match f, flags.noFinally with
        | .eventually a, true => .until .tt a
        | _, _ =>
          match f, flags.noGlobally with
          | .globally a, true => .release .ff a
          | _, _ =>
            match f, flags.pushGIn with
            | .globally (.conj a b), true => .conj (.globally a) (.globally b)
            | _, _ =>
              match f, flags.pushFIn with
              | .eventually (.disj a b), true => .disj (.eventually a) (.eventually b)
              | _, _ =>
                match f, flags.pushXIn with
                | .next (.conj a b), true => .conj (.next a) (.next b)
                | _, _ =>
                  match f, flags.pushXIn with
                  | .next (.disj a b), true => .disj (.next a) (.next b)
                  | _, _ =>
                    match f, flags.pullGOut with
                    | .conj (.globally a) (.globally b), true => .globally (.conj a b)
                    | _, _ =>
                      match f, flags.pullFOut with
                      | .disj (.eventually a) (.eventually b), true => .eventually (.disj a b)
                      | _, _ =>
                        match f, flags.pullXOut with
                        | .conj (.next a) (.next b), true => .next (.conj a b)
                        | _, _ =>
                          match f, flags.pullXOut with
                          | .disj (.next a) (.next b), true => .next (.disj a b)
                          | _, _ =>
                            if flags.simplifyWeak then simplify_weak_local f flags.finite else f

theorem weakUntil_eq (hj : InRange len j) :
    Sat len w (weakUntil a b) j ↔
      Sat len w (disj («until» a b) (globally a)) j := by simp [Sat, hj]

theorem apply_local_exact [DecidableEq α] (f : Ltl α) (flags : Flags) :
    Exact flags.finite (apply_local f flags) f := by
  intro len hl w j hj
  unfold apply_local
  split
  · try simp_all only
    exact (weakUntil_eq hj).symm
  · 
    split
    · try simp_all only
      exact (release_eq hj).symm
    · 
      split
      · try simp_all only
        exact (strongRelease_eq hj).symm
      · 
        split
        · try simp_all only
          exact until_true_left hj
        · 
          split
          · try simp_all only
            exact release_false_left hj
          · 
            split
            · try simp_all only
              exact (route_push_g_in hj).symm
            · 
              split
              · try simp_all only
                exact (push_f_in hj).symm
              · 
                split
                · try simp_all only
                  exact (route_push_x_in hj).symm
                · 
                  split
                  · try simp_all only
                    exact (push_x_or hj).symm
                  · 
                    split
                    · try simp_all only
                      exact route_push_g_in hj
                    · 
                      split
                      · try simp_all only
                        exact push_f_in hj
                      · 
                        split
                        · try simp_all only
                          exact route_push_x_in hj
                        · 
                          split
                          · try simp_all only
                            exact push_x_or hj
                          · 
                            split
                            · exact simplify_exact _ len hl w j hj
                            · exact Iff.rfl

-- Atoms return immediately in the C traversal.
def bottom_up (tr : Ltl α → Ltl α) : Ltl α → Ltl α
  | .tt => .tt
  | .ff => .ff
  | .ap a => .ap a
  | .neg a => tr (.neg (bottom_up tr a))
  | .next a => tr (.next (bottom_up tr a))
  | .strongNext a => tr (.strongNext (bottom_up tr a))
  | .eventually a => tr (.eventually (bottom_up tr a))
  | .globally a => tr (.globally (bottom_up tr a))
  | .conj a b => tr (.conj (bottom_up tr a) (bottom_up tr b))
  | .disj a b => tr (.disj (bottom_up tr a) (bottom_up tr b))
  | .impl a b => tr (.impl (bottom_up tr a) (bottom_up tr b))
  | .equiv a b => tr (.equiv (bottom_up tr a) (bottom_up tr b))
  | .until a b => tr (.until (bottom_up tr a) (bottom_up tr b))
  | .release a b => tr (.release (bottom_up tr a) (bottom_up tr b))
  | .weakUntil a b => tr (.weakUntil (bottom_up tr a) (bottom_up tr b))
  | .strongRelease a b => tr (.strongRelease (bottom_up tr a) (bottom_up tr b))

theorem bottom_up_exact (tr : Ltl α → Ltl α) (h : ∀ a, Exact fin (tr a) a)
    (f : Ltl α) : Exact fin (bottom_up tr f) f := by
  induction f with
  | tt | ff | ap _ => exact Exact.refl _
  | neg a ih | next a ih | strongNext a ih | eventually a ih | globally a ih =>
    apply (h _).trans
    apply Exact.symm
    apply exact_congr
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c; exact ih.symm
  | conj a b iha ihb | disj a b iha ihb | impl a b iha ihb | equiv a b iha ihb
  | «until» a b iha ihb | release a b iha ihb | weakUntil a b iha ihb | strongRelease a b iha ihb =>
    apply (h _).trans
    apply Exact.symm
    apply exact_congr
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact iha.symm
    · exact ihb.symm

def rw_pass [DecidableEq α] (f : Ltl α) (flags : Flags) : Ltl α :=
  bottom_up (fun a => apply_local a flags) f

theorem rw_pass_exact [DecidableEq α] (f : Ltl α) (flags : Flags) :
    Exact flags.finite (rw_pass f flags) f :=
  bottom_up_exact _ (fun a => apply_local_exact a flags) f

def RW_FIXPOINT_CAP : Nat := 200

def rewrite_loop [DecidableEq α] : Nat → Ltl α → Flags → Ltl α
  | 0, f, _ => f
  | n+1, f, flags =>
      let next := rw_pass f flags
      if next = f then next else rewrite_loop n next flags

def Flags.has_local (flags : Flags) : Bool :=
  flags.noWeakUntil || flags.noRelease || flags.noStrongRelease ||
  flags.noFinally || flags.noGlobally || flags.pushGIn || flags.pushFIn ||
  flags.pushXIn || flags.pullGOut || flags.pullFOut || flags.pullXOut || flags.simplifyWeak

def apply_rewrites [DecidableEq α] (f : Ltl α) (flags : Flags) : Ltl α :=
  if flags = {} then f else
    let root := if flags.nnf then to_nnf f true flags.finite else f
    if !flags.has_local then root else rewrite_loop RW_FIXPOINT_CAP root flags

theorem rewrite_loop_exact [DecidableEq α] (fuel : Nat) (f : Ltl α) (flags : Flags) :
    Exact flags.finite (rewrite_loop fuel f flags) f := by
  induction fuel generalizing f with
  | zero => exact Exact.refl _
  | succ fuel ih =>
    simp only [rewrite_loop]
    split
    · exact rw_pass_exact f flags
    · exact (ih _).trans (rw_pass_exact f flags)

theorem apply_rewrites_exact [DecidableEq α] (f : Ltl α) (flags : Flags) :
    Exact flags.finite (apply_rewrites f flags) f := by
  by_cases hf : flags = {}
  · simp only [apply_rewrites, hf, ↓reduceIte]; exact Exact.refl _
  · have hn : Exact flags.finite (if flags.nnf then to_nnf f true flags.finite else f) f := by
      split
      · exact (nnf_exact f flags.finite).1
      · exact Exact.refl _
    cases hc : flags.has_local with
    | false => simpa [apply_rewrites, hf, hc] using hn
    | true => simpa [apply_rewrites, hf, hc] using
        (rewrite_loop_exact RW_FIXPOINT_CAP _ flags).trans hn

-- pre_weak intentionally has fewer local folds than simplify_weak_local.
def pre_local [DecidableEq α] (f : Ltl α) (finite : Bool) : Ltl α :=
  match f with
  | .neg _ | .conj _ _ | .disj _ _ => simplify_weak_local f finite
  | .impl a b => if a = .ff ∨ b = .tt then .tt else if a = .tt then b else f
  | .equiv _ _ => f
  | .globally a => if a = .tt then .tt else if a = .ff then .ff else f
  | .eventually a => if a = .tt then .tt else if a = .ff then .ff else f
  | .next a => if !finite ∧ a = .ff then .ff else f
  | _ => f

-- The default C branch leaves strongNext intact, including its operand.
def pre_walk (tr : Ltl α → Ltl α) : Ltl α → Ltl α
  | .tt => .tt
  | .ff => .ff
  | .ap a => .ap a
  | .strongNext a => .strongNext a
  | .neg a => tr (.neg (pre_walk tr a))
  | .conj a b => tr (.conj (pre_walk tr a) (pre_walk tr b))
  | .disj a b => tr (.disj (pre_walk tr a) (pre_walk tr b))
  | .impl a b => tr (.impl (pre_walk tr a) (pre_walk tr b))
  | .equiv a b => tr (.equiv (pre_walk tr a) (pre_walk tr b))
  | .globally a => tr (.globally (pre_walk tr a))
  | .eventually a => tr (.eventually (pre_walk tr a))
  | .next a => tr (.next (pre_walk tr a))
  | .until a b => tr (.until (pre_walk tr a) (pre_walk tr b))
  | .release a b => tr (.release (pre_walk tr a) (pre_walk tr b))
  | .weakUntil a b => tr (.weakUntil (pre_walk tr a) (pre_walk tr b))
  | .strongRelease a b => tr (.strongRelease (pre_walk tr a) (pre_walk tr b))

def pre_weak [DecidableEq α] (f : Ltl α) (finite : Bool) : Ltl α :=
  pre_walk (fun a => pre_local a finite) f

theorem pre_local_exact [DecidableEq α] (f : Ltl α) : Exact fin (pre_local f fin) f := by
  classical
  intro len hl w j hj
  cases f with
  | neg a => exact simplify_exact (neg a) len hl w j hj
  | conj a b => exact simplify_exact (conj a b) len hl w j hj
  | disj a b => exact simplify_exact (disj a b) len hl w j hj
  | impl a b =>
    simp only [pre_local]
    repeat (any_goals split)
    all_goals simp_all only [Sat]
    all_goals grind [Sat]
  | globally a | eventually a =>
    simp only [pre_local]
    repeat (any_goals split)
    all_goals simp_all only [globally_true hj, globally_false hj,
      eventually_true hj, eventually_false]
    all_goals simp [Sat, hj]
  | next a =>
    simp only [pre_local]
    split
    · simp_all [Sat, InRange]
    · rfl
  | _ => rfl

theorem pre_walk_exact (tr : Ltl α → Ltl α) (h : ∀ a, Exact fin (tr a) a)
    (f : Ltl α) : Exact fin (pre_walk tr f) f := by
  induction f with
  | tt | ff | ap _ | strongNext a _ => exact Exact.refl _
  | neg a ih | next a ih | eventually a ih | globally a ih =>
    apply (h _).trans
    apply Exact.symm
    apply exact_congr
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c; exact ih.symm
  | conj a b iha ihb | disj a b iha ihb | impl a b iha ihb | equiv a b iha ihb
  | «until» a b iha ihb | release a b iha ihb | weakUntil a b iha ihb | strongRelease a b iha ihb =>
    apply (h _).trans
    apply Exact.symm
    apply exact_congr
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact iha.symm
    · exact ihb.symm

theorem pre_weak_exact [DecidableEq α] (f : Ltl α) : Exact fin (pre_weak f fin) f :=
  pre_walk_exact _ (fun a => pre_local_exact a) f

def rewrite_decompose : Ltl α → List (Ltl α)
  | .conj a b => rewrite_decompose a ++ rewrite_decompose b
  | .globally a => (rewrite_decompose a).map .globally
  | .next a => (rewrite_decompose a).map .next
  | .strongNext a => (rewrite_decompose a).map .strongNext
  | f => [f]

def PartsSat (len : Option Nat) (w : Word α) (j : Nat) (ps : List (Ltl α)) : Prop :=
  ∀ p, p ∈ ps → Sat len w p j

def conjoin (ps : List (Ltl α)) : Ltl α := ps.foldr .conj .tt

theorem conjoin_sat (hj : InRange len j) :
    Sat len w (conjoin ps) j ↔ PartsSat len w j ps := by
  induction ps with
  | nil => simp [conjoin, PartsSat, Sat, hj]
  | cons p ps ih =>
    change Sat len w (conj p (conjoin ps)) j ↔ _
    simp only [Sat, hj, true_and, ih, PartsSat, List.mem_cons]
    grind

theorem parts_append : PartsSat len w j (ps ++ qs) ↔
    PartsSat len w j ps ∧ PartsSat len w j qs := by
  simp only [PartsSat, List.mem_append]; grind

theorem parts_globally (hj : InRange len j) :
    PartsSat len w j (ps.map globally) ↔ AllFuture len j (fun k => PartsSat len w k ps) := by
  simp only [PartsSat, List.forall_mem_map, Sat, hj, true_and, AllFuture]
  constructor
  · intro h k hjk hk p hp; exact h p hp k hjk hk
  · intro h p hp k hjk hk; exact h k hjk hk p hp

theorem parts_next (hj : InRange len j) :
    PartsSat len w j (ps.map next) ↔ ¬InRange len (j+1) ∨ PartsSat len w (j+1) ps := by
  classical
  by_cases hk : InRange len (j+1) <;>
    simp [PartsSat, Sat, hj, hk]

theorem parts_strongNext (hj : InRange len j) (hne : ∃ p, p ∈ ps) :
    PartsSat len w j (ps.map strongNext) ↔ InRange len (j+1) ∧ PartsSat len w (j+1) ps := by
  simp only [PartsSat, List.forall_mem_map, Sat, hj, true_and]
  constructor
  · intro h
    obtain ⟨p, hp⟩ := hne
    exact ⟨(h p hp).1, fun p hp => (h p hp).2⟩
  · rintro ⟨hk, h⟩ p hp; exact ⟨hk, h p hp⟩

theorem decompose_has_part (f : Ltl α) : ∃ p, p ∈ rewrite_decompose f := by
  induction f with
  | conj a b iha _ =>
    obtain ⟨p, hp⟩ := iha
    exact ⟨p, List.mem_append_left _ hp⟩
  | globally a ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨globally p, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
  | next a ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨next p, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
  | strongNext a ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨strongNext p, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
  | _ => exact ⟨_, List.mem_cons_self⟩

theorem decompose_sat (f : Ltl α) (hj : InRange len j) :
    Sat len w f j ↔ PartsSat len w j (rewrite_decompose f) := by
  induction f generalizing j with
  | conj a b iha ihb =>
    rw [rewrite_decompose, parts_append, ←iha hj, ←ihb hj]
    simp [Sat, hj]
  | globally a ih =>
    rw [rewrite_decompose, parts_globally hj]
    simp only [Sat, hj, true_and]
    exact future_congr fun _ _ hk => ih hk
  | next a ih =>
    rw [rewrite_decompose, parts_next hj]
    simp only [Sat, hj, true_and]
    by_cases hk : InRange len (j+1)
    · rw [ih hk]
    · simp [hk]
  | strongNext a ih =>
    rw [rewrite_decompose, parts_strongNext hj (decompose_has_part a)]
    simp only [Sat, hj, true_and]
    by_cases hk : InRange len (j+1)
    · rw [ih hk]
    · simp [hk]
  | _ => simp [rewrite_decompose, PartsSat]

theorem decompose_exact (f : Ltl α) :
    Exact fin (conjoin (rewrite_decompose f)) f := by
  intro len _ w j hj
  exact (conjoin_sat hj).trans (decompose_sat f hj).symm

-- On the expanded core, prenorm_spine and decomp_append have identical cases.
def pre_spine_split (f : Ltl α) : List (Ltl α) := rewrite_decompose f

theorem pre_spine_split_exact (f : Ltl α) :
    Exact fin (conjoin (pre_spine_split f)) f := decompose_exact f

theorem or_to_impl (hj : InRange len j) :
    Sat len w (disj (neg r) g) j ↔ Sat len w (impl r g) j := by
  classical
  simp only [Sat, hj, true_and]; grind

theorem or_to_guarded_next_impl (hj : InRange len j) :
    Sat len w (disj (neg r) (next a)) j ↔ Sat len w (impl r (next a)) j := or_to_impl hj

theorem or_to_guarded_strong_next_impl (hj : InRange len j) :
    Sat len w (disj (neg r) (strongNext a)) j ↔
      Sat len w (impl r (strongNext a)) j := or_to_impl hj

theorem or_to_response_impl (hj : InRange len j) :
    Sat len w (disj (neg r) (eventually a)) j ↔
      Sat len w (impl r (eventually a)) j := or_to_impl hj

-- Indexed-next identities on their expanded weak-next interpretation. The
-- high-level NODE_NEXT_N representation itself remains outside Formula.
def next_power : Nat → Ltl α → Ltl α
  | 0, a => a
  | n+1, a => next (next_power n a)

theorem pre_x0 (a : Ltl α) : next_power 0 a = a := rfl

theorem pre_xn_flatten (m n : Nat) (a : Ltl α) :
    next_power m (next_power n a) = next_power (m+n) a := by
  induction m with
  | zero => simp [next_power]
  | succ m ih => simp only [next_power, ih, Nat.succ_add]

theorem pre_xn_bool_distribute (n : Nat) (a b : Ltl α) :
    Exact fin (next_power n (conj a b)) (conj (next_power n a) (next_power n b)) := by
  induction n with
  | zero => exact Exact.refl _
  | succ n ih =>
    intro len hl w j hj
    have hnext : Sat len w (next (next_power n (conj a b))) j ↔
        Sat len w (next (conj (next_power n a) (next_power n b))) j := by
      simp only [Sat, hj, true_and]
      by_cases hk : InRange len (j+1)
      · rw [ih len hl w (j+1) hk]
        simp only [Sat, hk, true_and]
      · simp [hk]
    exact hnext.trans (route_push_x_in hj)

-- This is the Boolean projection of normalize.c's admission check; phase and
-- growth restrictions can only cause additional rejection.
def finite_rule_allowed (finite equivalence_finite : Bool) : Bool :=
  !(finite && !equivalence_finite)

inductive SickertRule where
  | limitLift | gfW | fgU
  deriving DecidableEq

def SickertRule.equivalence_finite : SickertRule → Bool
  | .limitLift => false
  | .gfW => false
  | .fgU => false

theorem sickert_rules_refused (r : SickertRule) :
    finite_rule_allowed true r.equivalence_finite = false := by cases r <;> rfl

theorem sickert_limit_lift_refused :
    finite_rule_allowed true SickertRule.limitLift.equivalence_finite = false := rfl

theorem sickert_gf_w_refused :
    finite_rule_allowed true SickertRule.gfW.equivalence_finite = false := rfl

theorem sickert_fg_u_refused :
    finite_rule_allowed true SickertRule.fgU.equivalence_finite = false := rfl

-- The requested counterexample to the unrestricted context equation uses
-- C[z] = G(!z). It does not satisfy Sickert's positive-context precondition.
def sickert_context (f : Ltl Unit) : Ltl Unit := globally (neg f)
def sickert_word : Word Unit := fun _ _ => true

theorem sickert_finite_counterexample :
    ¬(Sat (some 1) sickert_word (sickert_context (globally (eventually (ap ())))) 0 ↔
      Sat (some 1) sickert_word
        (disj (conj (globally (eventually (ap ()))) (sickert_context tt))
          (sickert_context ff)) 0) := by
  have hj : InRange (some 1) 0 := by simp [InRange]
  have hgf : Sat (some 1) sickert_word (globally (eventually (ap ()))) 0 :=
    ⟨hj, fun k _ hk => ⟨hk, k, Nat.le_refl _, hk, ⟨hk, rfl⟩⟩⟩
  have hleft : ¬Sat (some 1) sickert_word
      (sickert_context (globally (eventually (ap ())))) 0 := by
    intro h
    exact (h.2 0 (Nat.le_refl _) hj).2 hgf
  have hright : Sat (some 1) sickert_word
      (disj (conj (globally (eventually (ap ()))) (sickert_context tt))
        (sickert_context ff)) 0 := by
    exact ⟨hj, Or.inr ⟨hj, fun _ _ hk => ⟨hk, fun hf => hf.2⟩⟩⟩
  intro he; exact hleft (he.mpr hright)

end Tlsf.Rewrites
