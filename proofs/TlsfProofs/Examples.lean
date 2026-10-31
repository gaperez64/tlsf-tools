import TlsfProofs.Pruning

namespace Tlsf.Examples
open Formula
inductive Signal where
  | q | p | r
  deriving DecidableEq, Repr

def isInput : Signal → Bool | .q => true | _ => false
abbrev P : Formula Signal := ap .p
abbrev Q : Formula Signal := ap .q
abbrev R : Formula Signal := ap .r
abbrev GF (f : Formula Signal) := globally (eventually f)
abbrev FG (f : Formula Signal) := eventually (globally f)
def zero : Letter Signal := fun _ => false

theorem recurrence_conflict (a : Signal) (w : Word Signal) :
    ¬Sat none w (conj (GF (ap a)) (FG (neg (ap a)))) 0 := by
  intro hs
  have h : (∀ k, ∃ m, k ≤ m ∧ w m a = true) ∧
      ∃ k, ∀ m, k ≤ m → w m a ≠ true := by
    simpa [Sat, AllFuture, InRange, GF, FG] using hs
  obtain ⟨k, hk⟩ := h.2
  obtain ⟨m, hm, hp⟩ := h.1 k
  exact hk m hm hp

theorem issue79_original :
    Realizable isInput (impl (conj (GF Q) (FG (neg Q))) (conj (GF P) (FG (neg P)))) := by
  refine ⟨fun _ _ => zero, fun i => ⟨trivial, fun h => ?_⟩⟩
  exact False.elim (recurrence_conflict .q _ h)

theorem issue79_pruned : ¬Realizable isInput (conj (GF P) (FG (neg P))) := by
  rintro ⟨s, hs⟩
  exact recurrence_conflict .p _ (hs (fun _ => zero))

def issue79Kept : List (Entry Signal) :=
  [⟨.guarantee, conj (GF P) (FG (neg P))⟩]

def issue79Dropped : List (Entry Signal) :=
  [⟨.assume, conj (GF Q) (FG (neg Q))⟩]

theorem issue79_env_unsat : ¬EnvSat issue79Dropped := by
  rintro ⟨d, _, _, ha⟩
  exact recurrence_conflict .q d
    (ha ⟨.assume, conj (GF Q) (FG (neg Q))⟩ (by simp [issue79Dropped]) rfl)

-- Without EnvSat the other pruning hypotheses hold, but the verdict changes
-- for either ordinary or strict semantics.
theorem pruning_without_envSat_changes_verdict (s : Bool) :
    ∃ K D : List (Entry Signal), Prunable isInput K D ∧ ¬EnvSat D ∧
      Realizable isInput (objectiveFormula s (K ++ D)) ∧
      ¬Realizable isInput (objectiveFormula s K) := by
  refine ⟨issue79Kept, issue79Dropped, ?_, issue79_env_unsat, ?_, ?_⟩
  · constructor
    · intro e he
      simp only [issue79Dropped, List.mem_singleton] at he
      subst e
      trivial
    · intro e he a ha
      simp only [issue79Dropped, List.mem_singleton] at he
      subst e
      have hq : a = .q := by simpa [Formula.atoms] using ha
      subst a
      rfl
    · intro e he a ha
      simp only [issue79Kept, List.mem_singleton] at he
      subst e
      simp only [Formula.atoms, List.mem_append, List.mem_singleton, or_self] at ha
      subst a
      simp [DroppedAtom, issue79Dropped, Formula.atoms]
  · rw [objective_inf]
    refine ⟨fun _ _ => zero, fun i e he hn j hj => ?_⟩
    simp only [issue79Kept, issue79Dropped, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have hh : j = 0 ∧ Environment (issue79Kept ++ issue79Dropped) none
          (play isInput (fun _ _ => zero) i) := hj.2.2
      exact False.elim (recurrence_conflict .q _
        (hh.2.2 ⟨.assume, conj (GF Q) (FG (neg Q))⟩
          (by simp [issue79Kept, issue79Dropped]) rfl))
    · exact False.elim (hn trivial)
  · rw [objective_inf]
    rintro ⟨σ, hσ⟩
    exact recurrence_conflict .p _
      (hσ (fun _ => zero) ⟨.guarantee, conj (GF P) (FG (neg P))⟩
        (by simp [issue79Kept]) (by simp [Env]) 0
        (by simp [Enabled, Initial, Environment, Section, issue79Kept, AllFuture,
          InRange]))

def decoder (role : Role := .guarantee) (value : Formula Signal := Q) : Definition Signal :=
  ⟨.p, value, role, false⟩

def kept84 : List (Entry Signal) := [⟨.assume, globally P⟩, ⟨.guarantee, ff⟩]

theorem issue84_original :
    Realizable isInput (impl (globally P) (conj (globally (equiv P Q)) ff)) := by
  refine ⟨fun _ _ => zero, fun i => ⟨trivial, fun hp => ?_⟩⟩
  have hh := hp.2 0 (Nat.zero_le _) trivial
  have : False := by simp [Sat, play, move, isInput, zero] at hh
  exact False.elim this

theorem issue84_residual : ¬Realizable isInput (impl (globally Q) ff) := by
  rintro ⟨s, hs⟩
  let i : Word Signal := fun _ _ => true
  have hq : Sat none (play isInput s i) (globally Q) 0 := by
    refine ⟨trivial, fun k _ _ => ⟨trivial, ?_⟩⟩
    exact play_input (by rfl)
  exact ((hs i).2 hq).2

theorem issue84_rejected : ¬Admissible isInput strict kept84 [decoder] passes := by
  intro h
  have hh := h.occurrences ⟨.assume, globally P⟩ (by simp [original, kept84])
    decoder (by simp) (by simp [decoder, Formula.atoms])
  exact hh.1 trivial

def kept86 : List (Entry Signal) := [⟨.preset, P⟩, ⟨.assume, ff⟩]

theorem issue86_original :
    Realizable isInput (conj P (impl ff (globally (equiv P Q)))) := by
  refine ⟨fun _ _ _ => true, fun _ => ?_⟩
  simp [Sat, InRange, play, move, isInput]

theorem input_q_unrealizable : ¬Realizable isInput Q := by
  rintro ⟨s, hs⟩
  have hq := (hs (fun _ => zero)).2
  have hf : play isInput s (fun _ => zero) 0 .q = false := play_input (by rfl)
  simp_all

theorem issue86_rejected : ¬Admissible isInput strict kept86 [decoder] passes := by
  intro h
  have hh := h.occurrences ⟨.preset, P⟩ (by simp [original, kept86])
    decoder (by simp) (by simp [decoder, Formula.atoms])
  have hc : covers strict .preset .guarantee := hh.2
  cases strict <;> simp [covers] at hc

-- Both input words share the first move. The second move is chosen after the
-- controller's first answer has been calculated.
theorem issue91_noncausal : ¬Realizable isInput (globally (equiv P (eventually Q))) := by
  rintro ⟨s, hs⟩
  let first := play isInput s (fun _ => zero) 0 .p
  let i : Word Signal := fun n a => match a with
    | .q => if first then false else decide (n = 1)
    | _ => false
  have hi0 : i 0 = zero := by
    funext a; cases a <;> simp [i, zero]
  have hp0 : play isInput s i 0 .p = first := by
    change move isInput s [] (i 0) .p = first
    rw [hi0]; rfl
  have he := ((hs i).2 0 (Nat.zero_le _) trivial).2
  change (Sat none (play isInput s i) P 0 ↔ Sat none (play isInput s i) (eventually Q) 0) at he
  cases hb : first with
  | false =>
    have hq : Sat none (play isInput s i) (eventually Q) 0 := by
      refine ⟨trivial, 1, by omega, trivial, ⟨trivial, ?_⟩⟩
      rw [play_input (by rfl)]
      simp [i, hb]
    have hp := (he.mpr hq).2
    rw [hp0, hb] at hp
    contradiction
  | true =>
    have hp : Sat none (play isInput s i) P 0 := ⟨trivial, hp0.trans hb⟩
    obtain ⟨k, _, _, hq⟩ := (he.mp hp).2
    have hval := hq.2
    have hi : play isInput s i k .q = false := by
      rw [play_input (by rfl)]; simp [i, hb]
    rw [hi] at hval
    contradiction

theorem issue91_rejected :
    ¬Admissible isInput strict kept [decoder .guarantee (eventually Q)] passes := by
  intro h
  have hh := h.boolean (decoder .guarantee (eventually Q)) (by simp)
  exact hh

theorem issue85_weak_next (w : Word Signal) :
    Sat (some 1) w (next ff) 0 ∧ ¬Sat (some 1) w ff 0 := by
  simp [Sat, InRange]

theorem issue85_negation (w : Word Signal) :
    ¬Sat (some 1) w (neg (next P)) 0 ∧ Sat (some 1) w (next (neg P)) 0 := by
  simp [Sat, InRange]

theorem next_neg_dual (hj : InRange len j) :
    Sat len w (neg (next f)) j ↔ Sat len w (strongNext (neg f)) j := by
  classical
  by_cases hk : InRange len (j+1) <;> simp [Sat, hj, hk]

theorem strong_next_neg_dual (hj : InRange len j) :
    Sat len w (neg (strongNext f)) j ↔ Sat len w (next (neg f)) j := by
  classical
  by_cases hk : InRange len (j+1) <;> simp [Sat, hj, hk]

theorem issue85_finite_realizable : FinRealizable isInput (next ff) := by
  refine ⟨fun _ _ => zero, fun _ => ⟨0, ?_⟩⟩
  simp [Sat, InRange]

theorem false_finite_unrealizable : ¬FinRealizable isInput ff := by
  rintro ⟨s, hs⟩
  obtain ⟨n, hn⟩ := hs (fun _ => zero)
  exact hn.2

def short : Formula Signal := conj P (neg (strongNext tt))
def long : Formula Signal := conj R (strongNext tt)

theorem finite_short_realizable : FinRealizable isInput short := by
  refine ⟨fun _ _ _ => true, fun _ => ⟨0, ?_⟩⟩
  simp [short, P, Sat, InRange, play, move, isInput]

theorem finite_long_realizable : FinRealizable isInput long := by
  refine ⟨fun _ _ _ => true, fun _ => ⟨1, ?_⟩⟩
  simp [long, R, Sat, InRange, play, move, isInput]

theorem finite_split_fails : ¬FinRealizable isInput (conj short long) := by
  rintro ⟨s, hs⟩
  obtain ⟨n, hn⟩ := hs (fun _ => zero)
  exact hn.2.1.2.2.2 hn.2.2.2.2

-- A concrete accepted Boolean fixture, including both orientations.
theorem boolean_fixture (flip : Bool) :
    Admissible isInput strict [⟨.guarantee, P⟩] [⟨.p, Q, .guarantee, flip⟩] 2 := by
  constructor
  · intro e he; simp only [List.mem_singleton] at he; subst e; rfl
  · intro e he; simp only [List.mem_singleton] at he; subst e; trivial
  · simp
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro e he d hd ha
      simp only [List.mem_singleton] at he hd
      subst e; subst d
      simp [Formula.atoms] at ha
    · intro e he; simp only [List.mem_singleton] at he; subst e; exact Nat.zero_lt_succ 1
  · intro x hx e he _ha
    simp only [List.mem_singleton] at he
    subst e
    simp only [original, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨by simp [Env], covers_refl⟩
    · exact ⟨by simp [Definition.entry, Env], covers_refl⟩

-- With this order one pass reads the old p when assigning r. Two passes
-- establish r=q. C uses the extra third pass for two eliminations.
theorem pass_order (v : Letter Signal) :
    normalize [decoder, ⟨.r, P, .guarantee, false⟩] 1 v .r = v .p ∧
    normalize [decoder, ⟨.r, P, .guarantee, false⟩] 3 v .r = v .q := by
  simp [normalize, letterPass, decoder, setLetter, evalBool, P, Q]
end Tlsf.Examples
