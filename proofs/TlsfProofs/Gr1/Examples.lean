import TlsfProofs.Gr1.Region

set_option warningAsError true

namespace Tlsf.Gr1.Examples

/-- Two alternating goals, no fairness assumptions. Safety requires the
control to echo the current input, so the witness uses Mealy order. -/
def alternating : Arena where
  states := 2
  inputs := 1
  controls := 1
  ngoals := 2
  goals_pos := by decide
  nfair := 0
  reset := 0
  step := fun s _ _ => if s.val = 0 then 1 else 0
  Bad := fun _ u v => v 0 ≠ u 0
  goal := fun j s => decide (s.val = j.val)
  fairness := fun i => Fin.elim0 i

def alternatingCertificate : RegionCertificate alternating where
  W := fun _ => True
  goal := alternating.goal
  levels := fun _ => 1
  levels_pos := fun _ => by decide
  X := fun _ _ _ _ => True
  Y := fun _ _ _ => True

theorem alternating_conditions : RegionConditions alternating alternatingCertificate where
  goal_eq := fun _ _ => rfl
  y_union := fun _ _ _ => ⟨fun _ => ⟨⟨0, by decide⟩, trivial⟩, fun _ => trivial⟩
  y_mono := fun _ _ _ _ _ _ => trivial
  reset_mem := trivial
  coverage := fun j _ _ => ⟨⟨0, alternatingCertificate.levels_pos j⟩, ⟨0, by decide⟩, trivial⟩
  goal_total := fun _ _ _ _ u => ⟨u, (fun hn => hn rfl), trivial⟩
  rank_total := by
    intro m k i s hl u
    refine ⟨u, ⟨(fun hn => hn rfl), trivial⟩, Or.inl ?_⟩
    have hg := hl.2.1
    let j := active alternating m
    have hj : j.val < 2 := j.isLt
    have hs : s.val < 2 := s.isLt
    have hne : s.val ≠ j.val := by
      intro he
      have ht : alternating.goal j s = true := by simp [alternating, he]
      exact Bool.noConfusion (hg.symm.trans ht)
    change decide ((if s.val = 0 then (1 : Fin 2) else 0).val = j.val) = true
    simp only [decide_eq_true_eq]
    split <;> simp only [Fin.val_one, Fin.val_zero] <;> omega

theorem alternating_wins :
    ∃ strat : Strategy (Signal alternating), ∀ env,
      SafePlay alternating strat env ∧
        (FairPlay alternating strat env → AllGoalsInfinitelyOften alternating strat env) :=
  region_conditions_sound alternating_conditions

/-- Input sampling supplies both the justice and fairness latch. -/
def sampled : Arena where
  states := 2
  inputs := 1
  controls := 1
  ngoals := 1
  goals_pos := by decide
  nfair := 1
  reset := 0
  step := fun _ u _ => if u 0 then 1 else 0
  Bad := fun _ u v => v 0 ≠ u 0
  goal := fun _ s => decide (s.val = 1)
  fairness := fun _ s => decide (s.val = 1)

def sampledCertificate : RegionCertificate sampled where
  W := fun _ => True
  goal := sampled.goal
  levels := fun _ => 1
  levels_pos := fun _ => by decide
  X := fun _ _ _ _ => True
  Y := fun _ _ _ => True

theorem sampled_conditions : RegionConditions sampled sampledCertificate where
  goal_eq := fun _ _ => rfl
  y_union := fun _ _ _ => ⟨fun _ => ⟨⟨0, by decide⟩, trivial⟩, fun _ => trivial⟩
  y_mono := fun _ _ _ _ _ _ => trivial
  reset_mem := trivial
  coverage := fun j _ _ => ⟨⟨0, sampledCertificate.levels_pos j⟩, ⟨0, by decide⟩, trivial⟩
  goal_total := fun _ _ _ _ u => ⟨u, (fun hn => hn rfl), trivial⟩
  rank_total := by
    intro m k i s _ u
    refine ⟨u, ⟨(fun hn => hn rfl), trivial⟩, ?_⟩
    cases hu : u (0 : Fin 1) <;>
      simp [Progress, sampled, sampledCertificate, Arena.fair, hu]

theorem sampled_wins :
    ∃ strat : Strategy (Signal sampled), ∀ env,
      SafePlay sampled strat env ∧
        (FairPlay sampled strat env → AllGoalsInfinitelyOften sampled strat env) :=
  region_conditions_sound sampled_conditions

/-- Goal 0 follows two waiting phases: 3 waits for input 1, then 2 descends
to 1, which waits for input 0. Each phase can stutter only unfairly.
Fairness holds at 3 and 1 respectively, so neither predicate is the goal. -/
def ranked : Arena where
  states := 4
  inputs := 2
  controls := 2
  ngoals := 1
  goals_pos := by decide
  nfair := 2
  reset := 3
  step := fun s u _ =>
    if s.val = 0 then 3 else
    if s.val = 1 then (if u 0 then 0 else 1) else
    if s.val = 2 then 1 else (if u 1 then 2 else 3)
  Bad := fun _ u v => v ≠ u
  goal := fun _ s => decide (s.val = 0)
  fairness := fun i s => decide (s.val = 0 ∨ s.val = (if i.val = 0 then 3 else 1))

/-- At level 0 both lanes contain {0,1}; at level 1 lane 0 is {2} and
lane 1 is universal. Thus 3→2 changes the least lane, and 2→1 requires
lower Y. Selecting lane 1 at state 1 would forbid its unfair stutter. -/
def rankedCertificate : RegionCertificate ranked where
  W := fun _ => True
  goal := ranked.goal
  levels := fun _ => 2
  levels_pos := fun _ => by decide
  X := fun _ k i s =>
    if k.val = 0 then s.val ≤ 1 else if i.val = 0 then s.val = 2 else True
  Y := fun _ k s => if k.val = 0 then s.val ≤ 1 else True

theorem ranked_conditions : RegionConditions ranked rankedCertificate where
  goal_eq := fun _ _ => rfl
  y_union := by
    intro j k s
    by_cases hk : k.val = 0
    · simp only [rankedCertificate, hk, ↓reduceIte]
      exact ⟨fun hs => ⟨(0 : Fin 2), hs⟩, fun ⟨_, hs⟩ => hs⟩
    · constructor
      · intro _; exact ⟨(1 : Fin 2), by simp [rankedCertificate, hk]⟩
      · intro _; simp [rankedCertificate, hk]
  y_mono := by
    intro j k l hkl s _
    have hl : l.val ≠ 0 := by omega
    simp [rankedCertificate, hl]
  reset_mem := trivial
  coverage := fun _ _ _ => ⟨(1 : Fin 2), (1 : Fin 2), trivial⟩
  goal_total := fun _ _ _ _ u => ⟨u, (fun hn => hn rfl), trivial⟩
  rank_total := by
    intro m k i s hl u
    have hk : k = (0 : Fin 2) ∨ k = (1 : Fin 2) := by
      have := k.isLt
      change k.val < 2 at this
      have : k.val = 0 ∨ k.val = 1 := by omega
      exact this.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
    have hi : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
      have := i.isLt
      change i.val < 2 at this
      have : i.val = 0 ∨ i.val = 1 := by omega
      exact this.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
    rcases hk with rfl | rfl <;> rcases hi with rfl | rfl
    · refine ⟨u, ⟨(fun hn => hn rfl), trivial⟩, ?_⟩
      have hs : s.val = 1 := by
        have hg := hl.2.1
        have hx := hl.2.2.1
        simp [ranked, rankedCertificate] at hg hx
        omega
      cases hu : u (0 : Fin 2) <;>
        simp [Progress, ranked, rankedCertificate, Arena.fair, hs, hu]
    · exact False.elim (hl.2.2.2 (0 : Fin 2) (0 : Fin 2)
        (Or.inr ⟨rfl, by decide⟩) hl.2.2.1)
    · have hs : s.val = 2 := by simpa [rankedCertificate] using hl.2.2.1
      refine ⟨u, ⟨(fun hn => hn rfl), trivial⟩,
        Or.inr (Or.inl ⟨by change 0 < (1 : Nat); decide, ?_⟩)⟩
      simp [ranked, rankedCertificate, hs]
    · have hs : s.val = 3 := by
        have hlow := hl.2.2.2 (0 : Fin 2) (0 : Fin 2)
          (Or.inl (by change (0 : Nat) < 1; decide))
        have hfirst := hl.2.2.2 (1 : Fin 2) (0 : Fin 2) (Or.inr ⟨rfl, by decide⟩)
        have hb := s.isLt
        simp [rankedCertificate] at hlow hfirst
        change s.val < 4 at hb
        omega
      refine ⟨u, ⟨(fun hn => hn rfl), trivial⟩, Or.inr (Or.inr ⟨trivial, ?_⟩)⟩
      cases hu : u (1 : Fin 2) <;> simp [ranked, Arena.fair, hs, hu] <;> decide

theorem ranked_wins :
    ∃ strat : Strategy (Signal ranked), ∀ env,
      SafePlay ranked strat env ∧
        (FairPlay ranked strat env → AllGoalsInfinitelyOften ranked strat env) :=
  region_conditions_sound ranked_conditions

end Tlsf.Gr1.Examples
