import TlsfProofs.Cluster

namespace Tlsf

-- Only infinite-word satisfiability is used by the pruning rule.
def EnvSat (D : List (Entry α)) : Prop :=
  ∃ d : Word α, Initial D none d ∧ Environment D none d

-- The native witness checker certifies this conjunction on an infinite word.
-- A lasso denotes one such Word; no completeness of witness search is needed.
def environmentFormula (D : List (Entry α)) : Formula α :=
  .conj (sectionFormula D .initially)
    (.conj (.globally (sectionFormula D .require)) (sectionFormula D .assume))

theorem environment_sat_iff {D : List (Entry α)} {w : Word α} :
    Sat none w (environmentFormula D) 0 ↔
      Initial D none w ∧ Environment D none w := by
  have req : Sat none w (.globally (sectionFormula D .require)) 0 ↔
      AllFuture none 0 (Section D .require none w) := by
    simp only [Sat, InRange, true_and]
    exact future_congr (fun _ _ hk => section_sat hk)
  have hc : ∀ f g : Formula α, Sat none w (.conj f g) 0 ↔
      Sat none w f 0 ∧ Sat none w g 0 :=
    fun _ _ => by simp only [Sat, InRange, true_and]
  unfold environmentFormula
  rw [hc, hc, section_sat (by trivial), req, section_sat (by trivial)]
  rfl

theorem envSat_of_word {D : List (Entry α)} {w : Word α}
    (h : Sat none w (environmentFormula D) 0) : EnvSat D :=
  ⟨w, environment_sat_iff.mp h⟩

def DroppedAtom (D : List (Entry α)) (a : α) : Prop :=
  ∃ e ∈ D, a ∈ e.formula.atoms

structure Prunable (isIn : α → Bool) (K D : List (Entry α)) : Prop where
  environment : ∀ e ∈ D, Env e.role
  inputs : ∀ e ∈ D, ∀ a ∈ e.formula.atoms, isIn a = true
  disjoint : ∀ e ∈ K, ∀ a ∈ e.formula.atoms, ¬DroppedAtom D a

variable {α : Type} {K D : List (Entry α)} {isIn : α → Bool}

theorem section_append :
    Section (K ++ D) r len w j ↔ Section K r len w j ∧ Section D r len w j := by
  simp [Section, List.mem_append, or_imp, forall_and]

theorem enabled_append_left (h : Enabled s (K ++ D) len w r j) :
    Enabled s K len w r j := by
  have sec : ∀ r j, Section (K ++ D) r len w j → Section K r len w j :=
    fun _ _ hs => (section_append.mp hs).1
  rcases h with ⟨hj, hi, hr⟩
  refine ⟨hj, sec _ _ hi, ?_⟩
  cases r <;> cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
  all_goals first
    | exact hr
    | exact fun k hk => sec _ _ (hr k hk)
    | exact ⟨fun k hk hi => sec _ _ (hr.1 k hk hi), sec _ _ hr.2⟩
    | exact ⟨hr.1, fun k hk hi => sec _ _ (hr.2.1 k hk hi), sec _ _ hr.2.2⟩

theorem objective_add_environment (he : ∀ e ∈ D, Env e.role)
    (h : Objective s K len w) : Objective s (K ++ D) len w := by
  intro e hm hn j hj
  rcases List.mem_append.mp hm with hm | hm
  · exact h e hm hn j (enabled_append_left hj)
  · exact False.elim (hn (he e hm))

theorem enabled_append_of_environment
    (hd : Initial D none w ∧ Environment D none w)
    (h : Enabled s K none w r j) : Enabled s (K ++ D) none w r j := by
  have sec : ∀ r j, Section K r none w j → Section D r none w j →
      Section (K ++ D) r none w j := fun _ _ hk hd => section_append.mpr ⟨hk, hd⟩
  rcases h with ⟨hj, hi, hr⟩
  refine ⟨hj, sec _ _ hi hd.1, ?_⟩
  cases r <;> cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
  all_goals first
    | exact hr
    | exact fun k hk => sec _ _ (hr k hk) (hd.2.1 k (Nat.zero_le _) trivial)
    | exact ⟨fun k hk hi => sec _ _ (hr.1 k hk hi) (hd.2.1 k hk hi),
        sec _ _ hr.2 hd.2.2⟩
    | exact ⟨hr.1, fun k hk hi => sec _ _ (hr.2.1 k hk hi) (hd.2.1 k hk hi),
        sec _ _ hr.2.2 hd.2.2⟩

theorem objective_remove_environment
    (hd : Initial D none w ∧ Environment D none w)
    (h : Objective s (K ++ D) none w) : Objective s K none w := by
  intro e he hn j hj
  exact h e (List.mem_append_left _ he) hn j (enabled_append_of_environment hd hj)

-- Histories are newest first: h.length is the time of the head letter.
def pinLetter (drop : α → Bool) (d : Word α) (n : Nat) (v : Letter α) : Letter α :=
  fun a => if drop a then d n a else v a

def pinWord (drop : α → Bool) (d i : Word α) : Word α :=
  fun n => pinLetter drop d n (i n)

def pinHistory (drop : α → Bool) (d : Word α) : List (Letter α) → List (Letter α)
  | [] => []
  | l :: h => pinLetter drop d h.length l :: pinHistory drop d h

def pinStrategy (isIn drop : α → Bool) (d : Word α) (s : Strategy α) : Strategy α :=
  fun h i => s (replay isIn s (pinHistory drop d h))
    (mask isIn (pinLetter drop d h.length i))

theorem history_length : (history isIn s i n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

theorem pin_mask_move (hd : ∀ a, drop a = true → isIn a = true) :
    mask isIn (pinLetter drop d n (move isIn t h i)) =
      mask isIn (pinLetter drop d n i) := by
  funext a
  cases ha : drop a <;> cases hi : isIn a <;> simp_all [mask, pinLetter, move]

theorem replay_pin_history (hd : ∀ a, drop a = true → isIn a = true) :
    replay isIn s (pinHistory drop d (history isIn t i n)) =
      history isIn s (pinWord drop d i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, pinHistory, history_length, replay, ih]
    exact congrArg (fun l => l :: history isIn s (pinWord drop d i) n)
      (move_mask (pin_mask_move hd))

theorem play_pinStrategy (hd : ∀ a, drop a = true → isIn a = true) :
    pinWord drop d (play isIn (pinStrategy isIn drop d s) i) =
      play isIn s (pinWord drop d i) := by
  funext n a
  simp only [pinWord, pinLetter, play, move, pinStrategy, replay_pin_history hd,
    history_length]
  have hm : mask isIn (pinLetter drop d n (mask isIn (i n))) =
      mask isIn (pinLetter drop d n (i n)) := by
    funext b
    cases hb : drop b <;> cases hi : isIn b <;> simp [mask, pinLetter, hb, hi]
  rw [hm]
  cases ha : drop a with
  | true => simp only [↓reduceIte, hd a ha]
  | false =>
    cases isIn a <;> simp only [Bool.false_eq_true, ↓reduceIte]

-- Both ordinary (s=false) and strict (s=true) objective shapes are covered.
theorem prune_realizable (h : Prunable isIn K D) (sat : EnvSat D) :
    Realizable isIn (objectiveFormula s (K ++ D)) ↔
      Realizable isIn (objectiveFormula s K) := by
  classical
  rw [objective_inf, objective_inf]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨d, hd⟩ := sat
    let drop : α → Bool := fun a => decide (DroppedAtom D a)
    have hin : ∀ a, drop a = true → isIn a = true := by
      intro a ha
      obtain ⟨e, he, hm⟩ := of_decide_eq_true ha
      exact h.inputs e he a hm
    refine ⟨pinStrategy isIn drop d σ, fun i => ?_⟩
    let v := play isIn (pinStrategy isIn drop d σ) i
    let w := pinWord drop d v
    have hD : ∀ r j, Section D r none d j ↔ Section D r none w j := by
      intro r j
      have eqv : ∀ e ∈ D, Sat none d e.formula j ↔ Sat none w e.formula j := by
        intro e he
        apply sat_locality
        intro n _ _ a ha
        have hm : drop a = true := decide_eq_true (show DroppedAtom D a from ⟨e, he, ha⟩)
        simp [w, pinWord, pinLetter, hm]
      constructor <;> intro hs e he hr
      · exact (eqv e he).mp (hs e he hr)
      · exact (eqv e he).mpr (hs e he hr)
    have hw : Objective s K none w := by
      apply objective_remove_environment
        ⟨(hD _ _).mp hd.1,
          (fun n hn hi => (hD _ _).mp (hd.2.1 n hn hi)), (hD _ _).mp hd.2.2⟩
      change Objective s (K ++ D) none
        (pinWord drop d (play isIn (pinStrategy isIn drop d σ) i))
      rw [play_pinStrategy hin]
      exact hσ (pinWord drop d i)
    have hK : ∀ e ∈ K, ∀ j, Sat none w e.formula j ↔ Sat none v e.formula j := by
      intro e he j
      apply sat_locality
      intro n _ _ a ha
      have hm : drop a = false := by simpa [drop] using h.disjoint e he a ha
      simp [w, pinWord, pinLetter, hm]
    have henv : SameEnvironment K K none w v := by
      intro r _ j
      constructor <;> intro hs e he hr
      · exact (hK e he j).mp (hs e he hr)
      · exact (hK e he j).mpr (hs e he hr)
    intro e he hn j hj
    exact (hK e he j).mp (hw e he hn j ((enabled_congr henv).mpr hj))
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun i => objective_add_environment h.environment (hσ i)⟩

end Tlsf
