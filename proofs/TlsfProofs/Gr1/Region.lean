import TlsfProofs.Game
import TlsfProofs.Dpa.Stage1

set_option warningAsError true

/-! Mathematical port of the system region check in src/lib/gr1_check.c.
The supplied arena is already acceptance-sampled. Parsing, BDD/AIG semantics,
and the TLSF-to-arena reduction are explicit trust boundaries. -/
namespace Tlsf.Gr1
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure Arena where
  states : Nat
  inputs : Nat
  controls : Nat
  ngoals : Nat
  goals_pos : 0 < ngoals
  nfair : Nat
  reset : Fin states
  step : Fin states → Letter (Fin inputs) → Letter (Fin controls) → Fin states
  Bad : Fin states → Letter (Fin inputs) → Letter (Fin controls) → Prop
  goal : Fin ngoals → Fin states → Bool
  fairness : Fin nfair → Fin states → Bool

abbrev Arena.State (a : Arena) := Fin a.states
abbrev Arena.Goal (a : Arena) := Fin a.ngoals
abbrev Arena.Input (a : Arena) := Letter (Fin a.inputs)
abbrev Arena.Control (a : Arena) := Letter (Fin a.controls)
def Arena.lanes (a : Arena) : Nat := max a.nfair 1
abbrev Arena.Lane (a : Arena) := Fin a.lanes

/-- C:4489 and 3245–3254: no fairness means one synthetic true lane. -/
def Arena.fair (a : Arena) (i : a.Lane) (s : a.State) : Bool :=
  if h : a.nfair = 0 then true else a.fairness ⟨i.val, by
    have := i.isLt; unfold Arena.lanes at this; omega⟩ s

/-- State-only by type: C:2330–2331, 2339–2357. Positive depths: C:1051–1054.
There is no input, control, or scheduler argument to W, X, or Y. -/
structure RegionCertificate (a : Arena) where
  W : a.State → Prop
  goal : a.Goal → a.State → Bool
  levels : a.Goal → Nat
  levels_pos : ∀ j, 0 < levels j
  X : (j : a.Goal) → Fin (levels j) → a.Lane → a.State → Prop
  Y : (j : a.Goal) → Fin (levels j) → a.State → Prop

/-- None is the all-zero reset mode; some j is one-hot j (C:3370–3377). -/
abbrev Mode (a : Arena) := Option a.Goal
def active (a : Arena) (m : Mode a) : a.Goal := m.getD ⟨0, a.goals_pos⟩

def nextGoal (a : Arena) (j : a.Goal) : a.Goal :=
  if h : j.val + 1 < a.ngoals then ⟨j.val + 1, h⟩ else ⟨0, a.goals_pos⟩

/-- Current-state justice sampling; after reset the encoding is one-hot.
This is the cyclic update specified at C:2932–2942. -/
def updateMode (a : Arena) (m : Mode a) (s : a.State) : Mode a :=
  some (if a.goal (active a m) s then nextGoal a (active a m) else active a m)

def Before {a : Arena} {c : RegionCertificate a} {j : a.Goal}
    (k' k : Fin (c.levels j)) (i' i : a.Lane) : Prop :=
  k'.val < k.val ∨ (k' = k ∧ i'.val < i.val)

/-- C:3228, 3236–3243, 3272: goal precedence and the least (k,i). -/
def Layer {a : Arena} (c : RegionCertificate a) (j : a.Goal)
    (k : Fin (c.levels j)) (i : a.Lane) (s : a.State) : Prop :=
  c.W s ∧ a.goal j s = false ∧ c.X j k i s ∧
    ∀ k' i', Before k' k i' i → ¬c.X j k' i' s

def SafeInv {a : Arena} (c : RegionCertificate a) (s : a.State)
    (u : a.Input) (v : a.Control) : Prop :=
  ¬a.Bad s u v ∧ c.W (a.step s u v)

/-- C:3197–3201, 3245–3257; the extra W on the goal disjunct is
redundant under SafeInv, exactly as in the documented formula. -/
def Progress {a : Arena} (c : RegionCertificate a) (j : a.Goal)
    (k : Fin (c.levels j)) (i : a.Lane) (s' : a.State) : Prop :=
  a.goal j s' = true ∨
    (∃ hk : 0 < k.val, c.Y j ⟨k.val - 1, by have := k.isLt; omega⟩ s') ∨
    (c.X j k i s' ∧ a.fair i s' = false)

structure RegionConditions (a : Arena) (c : RegionCertificate a) : Prop where
  /-- C:3322–3334, equality to the actual game justice on every state. -/
  goal_eq : ∀ j s, c.goal j s = a.goal j s
  /-- C:2349–2351, 2363–2378, equality on every state, including outside W. -/
  y_union : ∀ j k s, c.Y j k s ↔ ∃ i, c.X j k i s
  /-- C:2335, 2379–2401; the initial empty predecessor is automatic. -/
  y_mono : ∀ j (k l : Fin (c.levels j)), l.val = k.val + 1 →
    ∀ s, c.Y j k s → c.Y j l s
  /-- C:3336–3343 (constant reset evaluation at C:2408–2424). -/
  reset_mem : c.W a.reset
  /-- C:3344–3368, coverage even at goal states. -/
  coverage : ∀ j s, c.W s → ∃ k i, c.X j k i s
  /-- C:3135–3148, 3194–3196, 3228–3234, for each mode C:3373–3377. -/
  goal_total : ∀ m s, c.W s → a.goal (active a m) s = true →
    ∀ u, ∃ v, SafeInv c s u v
  /-- C:3135–3148, 3236–3274, for each mode C:3373–3377.
  ONE existential control follows the complete conjunction (C:3258). -/
  rank_total : ∀ m k i s, Layer c (active a m) k i s →
    ∀ u, ∃ v, SafeInv c s u v ∧ Progress c (active a m) k i (a.step s u v)

variable {a : Arena} {c : RegionCertificate a}

theorem exists_layer (h : RegionConditions a c) (j : a.Goal) (s : a.State)
    (hw : c.W s) (hg : a.goal j s = false) : ∃ k i, Layer c j k i s := by
  obtain ⟨k, i, hx⟩ := h.coverage j s hw
  obtain ⟨kv, ⟨hk, ihx⟩, hmin⟩ := exists_least_nat
    (show ∃ n, ∃ hn : n < c.levels j, ∃ i, c.X j ⟨n, hn⟩ i s from
      ⟨k.val, k.isLt, i, hx⟩)
  obtain ⟨iv, ⟨hi, hx⟩, imin⟩ := exists_least_nat
    (show ∃ n, ∃ hn : n < a.lanes, c.X j ⟨kv, hk⟩ ⟨n, hn⟩ s from
      let ⟨i, hx⟩ := ihx; ⟨i.val, i.isLt, hx⟩)
  refine ⟨⟨kv, hk⟩, ⟨iv, hi⟩, hw, hg, hx, ?_⟩
  intro k' i' hb hx'
  rcases hb with hb | ⟨he, hb⟩
  · exact hmin k'.val hb ⟨k'.isLt, i', hx'⟩
  · subst k'; exact imin i'.val hb ⟨i'.isLt, hx'⟩

structure Rank (c : RegionCertificate a) (j : a.Goal) where
  k : Fin (c.levels j)
  i : a.Lane

def rank (c : RegionCertificate a) (j : a.Goal) (s : a.State) : Rank c j :=
  if h : ∃ k i, Layer c j k i s then
    ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
  else ⟨⟨0, c.levels_pos j⟩, ⟨0, by unfold Arena.lanes; omega⟩⟩

theorem rank_layer (h : RegionConditions a c) (hw : c.W s)
    (hg : a.goal j s = false) : Layer c j (rank c j s).k (rank c j s).i s := by
  have he := exists_layer h j s hw hg
  simp only [rank, dite_eq_left he]
  exact Classical.choose_spec (Classical.choose_spec he)

theorem layer_le (hl : Layer c j k i s) (hx : c.X j l q s) :
    k.val < l.val ∨ (k = l ∧ i.val ≤ q.val) := by
  have hn := hl.2.2.2 l q
  by_cases hk : k.val < l.val
  · exact Or.inl hk
  · have hkl : k = l := Fin.ext (by
      apply Classical.byContradiction; intro he
      exact hn (Or.inl (by omega)) hx)
    exact Or.inr ⟨hkl, by
      apply Classical.byContradiction; intro he
      exact hn (Or.inr ⟨hkl.symm, by omega⟩) hx⟩

/-- A local obligation for the selected least layer; no liveness premise. -/
def Good (c : RegionCertificate a) (m : Mode a) (s : a.State)
    (u : a.Input) (v : a.Control) : Prop :=
  SafeInv c s u v ∧ (a.goal (active a m) s = false →
    Progress c (active a m) (rank c (active a m) s).k
      (rank c (active a m) s).i (a.step s u v))

theorem exists_good (h : RegionConditions a c) (hw : c.W s) (m : Mode a)
    (u : a.Input) : ∃ v, Good c m s u v := by
  cases hg : a.goal (active a m) s with
  | false =>
    obtain ⟨v, hs, hp⟩ := h.rank_total m _ _ s (rank_layer h hw hg) u
    exact ⟨v, hs, fun _ => hp⟩
  | true =>
    obtain ⟨v, hs⟩ := h.goal_total m s hw hg u
    exact ⟨v, hs, fun hf => Bool.noConfusion (hg.symm.trans hf)⟩

def control (h : RegionConditions a c) (m : Mode a) (s : a.State)
    (u : a.Input) : a.Control :=
  if hw : c.W s then Classical.choose (exists_good h hw m u) else fun _ => false

theorem control_good (h : RegionConditions a c) (hw : c.W s) :
    Good c m s u (control h m s u) := by
  simp only [control, dite_eq_left hw]
  exact Classical.choose_spec (exists_good h hw m u)

abbrev Signal (a : Arena) := Sum (Fin a.inputs) (Fin a.controls)
def isInput (a : Arena) : Signal a → Bool | .inl _ => true | .inr _ => false
def inputs (a : Arena) (l : Letter (Signal a)) : a.Input := fun i => l (.inl i)
def controls (a : Arena) (l : Letter (Signal a)) : a.Control := fun i => l (.inr i)

/-- Replay the actual joint letters, newest first, as in Game.history. -/
def memory (a : Arena) : List (Letter (Signal a)) → a.State × Mode a
  | [] => (a.reset, none)
  | l :: hs =>
    let old := memory a hs
    (a.step old.1 (inputs a l) (controls a l), updateMode a old.2 old.1)

def regionStrategy (h : RegionConditions a c) : Strategy (Signal a) :=
  fun hs l sig => match sig with
    | .inl i => l (.inl i)
    | .inr i => control h (memory a hs).2 (memory a hs).1 (inputs a l) i

def state (a : Arena) (strat : Strategy (Signal a)) (env : Word (Signal a))
    (n : Nat) : a.State := (memory a (history (isInput a) strat env n)).1
def mode (a : Arena) (strat : Strategy (Signal a)) (env : Word (Signal a))
    (n : Nat) : Mode a := (memory a (history (isInput a) strat env n)).2

theorem state_succ (strat : Strategy (Signal a)) (env : Word (Signal a)) (n : Nat) :
    state a strat env (n+1) = a.step (state a strat env n)
      (inputs a (play (isInput a) strat env n))
      (controls a (play (isInput a) strat env n)) := rfl

theorem mode_succ (strat : Strategy (Signal a)) (env : Word (Signal a)) (n : Nat) :
    mode a strat env (n+1) = updateMode a (mode a strat env n) (state a strat env n) := rfl

theorem strategy_controls (h : RegionConditions a c) (env : Word (Signal a)) (n : Nat) :
    controls a (play (isInput a) (regionStrategy h) env n) =
      control h (mode a (regionStrategy h) env n) (state a (regionStrategy h) env n)
        (inputs a (play (isInput a) (regionStrategy h) env n)) := by
  rfl

def SafePlay (a : Arena) (strat : Strategy (Signal a)) (env : Word (Signal a)) : Prop :=
  ∀ n, ¬a.Bad (state a strat env n) (inputs a (play (isInput a) strat env n))
    (controls a (play (isInput a) strat env n))
def FairPlay (a : Arena) (strat : Strategy (Signal a)) (env : Word (Signal a)) : Prop :=
  ∀ i, Dpa.Inf (fun n => a.fairness i (state a strat env n))
def AllGoalsInfinitelyOften (a : Arena) (strat : Strategy (Signal a))
    (env : Word (Signal a)) : Prop :=
  ∀ j, Dpa.Inf (fun n => a.goal j (state a strat env n))

theorem strategy_invariant (h : RegionConditions a c) (env : Word (Signal a)) :
    ∀ n, c.W (state a (regionStrategy h) env n) := by
  intro n; induction n with
  | zero => exact h.reset_mem
  | succ n ih =>
    rw [state_succ, strategy_controls]
    exact (control_good h ih).1.2

theorem strategy_good (h : RegionConditions a c) (env : Word (Signal a)) (n : Nat) :
    Good c (mode a (regionStrategy h) env n) (state a (regionStrategy h) env n)
      (inputs a (play (isInput a) (regionStrategy h) env n))
      (controls a (play (isInput a) (regionStrategy h) env n)) := by
  rw [strategy_controls]
  exact control_good h (strategy_invariant h env n)

theorem fair_lane_inf (hf : FairPlay a strat env) (i : a.Lane) :
    Dpa.Inf (fun n => a.fair i (state a strat env n)) := by
  by_cases hz : a.nfair = 0
  · intro N; exact ⟨N, Nat.le_refl _, by simp [Arena.fair, hz]⟩
  · simpa only [Arena.fair, dite_eq_right hz] using
      hf ⟨i.val, by have := i.isLt; unfold Arena.lanes at this; omega⟩

/-- A goal cannot be avoided forever: take the least visited k, then the
least visited i at that k. Lower-Y steps contradict minimality; stuttering
then fixes that layer and excludes its fairness lane forever. -/
theorem goal_eventually (h : RegionConditions a c) (s : Nat → a.State)
    (hw : ∀ n, c.W (s n)) (hf : ∀ i, Dpa.Inf (fun n => a.fair i (s n)))
    (j : a.Goal) (N : Nat)
    (hp : ∀ n, N ≤ n → a.goal j (s n) = false →
      Progress c j (rank c j (s n)).k (rank c j (s n)).i (s (n+1))) :
    ∃ n, N ≤ n ∧ a.goal j (s n) = true := by
  apply Classical.byContradiction; intro hno
  have hg : ∀ n, N ≤ n → a.goal j (s n) = false := by
    intro n hn
    exact Bool.eq_false_iff.mpr (fun ht => hno ⟨n, hn, ht⟩)
  let r := fun n => rank c j (s n)
  obtain ⟨kv, ⟨T₀, hNT₀, hk₀⟩, kmin⟩ := exists_least_nat
    (show ∃ k, ∃ t, N ≤ t ∧ (r t).k.val = k from ⟨(r N).k.val, N, Nat.le_refl _, rfl⟩)
  obtain ⟨iv, ⟨T, hNT, hkT, hiT⟩, imin⟩ := exists_least_nat
    (show ∃ i, ∃ t, N ≤ t ∧ (r t).k.val = kv ∧ (r t).i.val = i from
      ⟨(r T₀).i.val, T₀, hNT₀, hk₀, rfl⟩)
  have kb : ∀ n, N ≤ n → kv ≤ (r n).k.val := by
    intro n hn; apply Nat.le_of_not_gt; intro hl
    exact kmin _ hl ⟨n, hn, rfl⟩
  have ib : ∀ n, N ≤ n → (r n).k.val = kv → iv ≤ (r n).i.val := by
    intro n hn hk; apply Nat.le_of_not_gt; intro hl
    exact imin _ hl ⟨n, hn, hk, rfl⟩
  have force : ∀ n, N ≤ n → Progress c j (r T).k (r T).i (s n) →
      c.X j (r T).k (r T).i (s n) ∧ a.fair (r T).i (s n) = false := by
    intro n hn hp'
    rcases hp' with hit | ⟨hk, hy⟩ | hx
    · exact False.elim (Bool.noConfusion ((hg n hn).symm.trans hit))
    · obtain ⟨q, hx⟩ := (h.y_union j _ (s n)).mp hy
      have hl := layer_le (rank_layer h (hw n) (hg n hn)) hx
      have hb := kb n hn
      change (r n).k.val < (r T).k.val - 1 ∨
        ((r n).k = _ ∧ (r n).i.val ≤ q.val) at hl
      rcases hl with hl | ⟨hl, _⟩
      · omega
      · have he : (r n).k.val = (r T).k.val - 1 := congrArg Fin.val hl
        omega
    · exact hx
  have stable : ∀ d, (r (T+d)).k = (r T).k ∧ (r (T+d)).i = (r T).i := by
    intro d; induction d with
    | zero => exact ⟨rfl, rfl⟩
    | succ d ih =>
      have hnd : N ≤ T+d := by omega
      have hp' := hp (T+d) hnd (hg _ hnd)
      change Progress c j (r (T+d)).k (r (T+d)).i (s (T+d+1)) at hp'
      rw [ih.1, ih.2] at hp'
      have hx := (force _ (by omega) hp').1
      have hl := layer_le (rank_layer h (hw _) (hg _ (by omega))) hx
      change (r (T+d+1)).k.val < (r T).k.val ∨
        ((r (T+d+1)).k = (r T).k ∧ (r (T+d+1)).i.val ≤ (r T).i.val) at hl
      have hb := kb (T+d+1) (by omega)
      have he : (r (T+d+1)).k = (r T).k := by
        apply Fin.ext
        rcases hl with hl | ⟨hl, _⟩
        · omega
        · exact congrArg Fin.val hl
      have hi := ib (T+d+1) (by omega) (by rw [he]; exact hkT)
      change (r (T+d+1)).k = (r T).k ∧ (r (T+d+1)).i = (r T).i
      refine ⟨he, Fin.ext ?_⟩
      rcases hl with hl | ⟨_, hl⟩
      · have he' := congrArg Fin.val he; omega
      · omega
  obtain ⟨n, hn, ht⟩ := hf (r T).i (T+1)
  let d := n - (T+1)
  have en : T+d+1 = n := by dsimp [d]; omega
  have hp' := hp (T+d) (by omega) (hg _ (by omega))
  change Progress c j (r (T+d)).k (r (T+d)).i (s (T+d+1)) at hp'
  rw [(stable d).1, (stable d).2, en] at hp'
  exact Bool.noConfusion ((force n (by omega) hp').2.symm.trans ht)

def phase (a : Arena) (strat : Strategy (Signal a)) (env : Word (Signal a))
    (n : Nat) : a.Goal := active a (mode a strat env n)

theorem phase_succ (strat : Strategy (Signal a)) (env : Word (Signal a)) (n : Nat) :
    phase a strat env (n+1) =
      if a.goal (phase a strat env n) (state a strat env n) then
        nextGoal a (phase a strat env n) else phase a strat env n := rfl

/-- From any time, the current goal is served before its counter advances. -/
theorem current_goal_served (h : RegionConditions a c) (env : Word (Signal a))
    (hf : FairPlay a (regionStrategy h) env) (N : Nat) :
    ∃ n, N ≤ n ∧ phase a (regionStrategy h) env n = phase a (regionStrategy h) env N ∧
      a.goal (phase a (regionStrategy h) env n) (state a (regionStrategy h) env n) = true := by
  let s := state a (regionStrategy h) env
  let p := phase a (regionStrategy h) env
  apply Classical.byContradiction; intro hno
  have nohit : ∀ n, N ≤ n → p n = p N → a.goal (p N) (s n) = false := by
    intro n hn he
    exact Bool.eq_false_iff.mpr (fun ht => hno ⟨n, hn, he, by
      change a.goal (p n) (s n) = true
      rw [he]; exact ht⟩)
  have fixed : ∀ d, p (N+d) = p N := by
    intro d; induction d with
    | zero => rfl
    | succ d ih =>
      change phase a (regionStrategy h) env (N+d+1) = _
      rw [phase_succ]
      change (if a.goal (p (N+d)) (s (N+d)) then _ else p (N+d)) = _
      rw [ih, nohit (N+d) (by omega) ih]
      rfl
  have fixed' : ∀ n, N ≤ n → p n = p N := by
    intro n hn
    have he : N + (n-N) = n := by omega
    simpa only [he] using fixed (n-N)
  obtain ⟨n, hn, ht⟩ := goal_eventually h s (strategy_invariant h env)
    (fun i => fair_lane_inf hf i) (p N) N (by
      intro n hn hg
      have hp := (strategy_good h env n).2
      change a.goal (p n) (s n) = false →
        Progress c (p n) (rank c (p n) (s n)).k (rank c (p n) (s n)).i
          (a.step (s n) _ _) at hp
      rw [← state_succ] at hp
      change a.goal (p n) (s n) = false →
        Progress c (p n) (rank c (p n) (s n)).k (rank c (p n) (s n)).i (s (n+1)) at hp
      rw [fixed' n hn] at hp
      exact hp hg)
  exact Bool.noConfusion ((nohit n hn (fixed' n hn)).symm.trans ht)

/-- Number of counter advances to the target, before wraparound. -/
def distance (a : Arena) (j target : a.Goal) : Nat :=
  if j.val ≤ target.val then target.val - j.val else a.ngoals - j.val + target.val

theorem distance_decreases (j target : a.Goal) (hne : j ≠ target) :
    distance a (nextGoal a j) target < distance a j target := by
  have hj := j.isLt
  have ht := target.isLt
  have hval : j.val ≠ target.val := fun he => hne (Fin.ext he)
  unfold nextGoal distance
  split <;> split <;> split <;> simp_all <;> omega

theorem every_goal_eventually (h : RegionConditions a c) (env : Word (Signal a))
    (hf : FairPlay a (regionStrategy h) env) (target : a.Goal) (N : Nat) :
    ∃ n, N ≤ n ∧ a.goal target (state a (regionStrategy h) env n) = true := by
  have aux : ∀ d N, distance a (phase a (regionStrategy h) env N) target = d →
      ∃ n, N ≤ n ∧ a.goal target (state a (regionStrategy h) env n) = true := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro N hd
      obtain ⟨n, hn, he, ht⟩ := current_goal_served h env hf N
      by_cases hit : phase a (regionStrategy h) env N = target
      · exact ⟨n, hn, by simpa only [he, hit] using ht⟩
      · have hnxt : phase a (regionStrategy h) env (n+1) =
            nextGoal a (phase a (regionStrategy h) env N) := by
          rw [phase_succ, ht]; simp only [↓reduceIte, he]
        have hlt : distance a (phase a (regionStrategy h) env (n+1)) target < d := by
          rw [hnxt, ← hd]; exact distance_decreases _ _ hit
        obtain ⟨t, hnt, ht⟩ := ih _ hlt (n+1) rfl
        exact ⟨t, by omega, ht⟩
  exact aux _ N rfl

/-- Soundness of the mathematical region obligations, with an input-first
causal Mealy strategy from Game.lean and no restriction on environment words. -/
theorem region_conditions_sound (h : RegionConditions a c) :
    ∃ strat : Strategy (Signal a), ∀ env,
      SafePlay a strat env ∧ (FairPlay a strat env → AllGoalsInfinitelyOften a strat env) := by
  refine ⟨regionStrategy h, fun env => ⟨fun n => (strategy_good h env n).1.1, ?_⟩⟩
  intro hf j N
  exact every_goal_eventually h env hf j N

end
end Tlsf.Gr1
