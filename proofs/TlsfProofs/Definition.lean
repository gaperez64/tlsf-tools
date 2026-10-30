import TlsfProofs.Passes

namespace Tlsf
variable [DecidableEq α]
variable {isIn : α → Bool} {kept : List (Entry α)} {ds : List (Definition α)}
  {e d : Definition α} {w : Word α} {v : Letter α}

structure Admissible (isIn : α → Bool) (strict : Bool) (kept : List (Entry α))
    (ds : List (Definition α)) (passes : Nat) : Prop where
  outputs : ∀ e ∈ ds, isIn e.name = false
  boolean : ∀ e ∈ ds, Boolean e.value
  distinct : (ds.map Definition.name).Nodup
  ranked : ∃ rank : α → Nat, Ranked ds rank ∧ ∀ e ∈ ds, rank e.name < passes
  occurrences : ∀ x ∈ original kept ds, ∀ e ∈ ds, e.name ∈ x.formula.atoms →
    ¬Env x.role ∧ covers strict x.role e.role

omit [DecidableEq α] in
theorem definition_self : e.name ∈ e.entry.formula.atoms := by
  cases hf : e.flip <;> simp [Definition.entry, Formula.atoms, hf]

omit [DecidableEq α] in
theorem definition_value (ha : a ∈ e.value.atoms) : a ∈ e.entry.formula.atoms := by
  cases hf : e.flip <;> simp [Definition.entry, Formula.atoms, hf, ha]

omit [DecidableEq α] in
theorem definition_sat (hb : Boolean e.value) (hj : InRange len j) :
    Sat len w e.entry.formula j ↔
      ∀ k, j ≤ k → InRange len k → w k e.name = evalBool (w k) e.value := by
  change (InRange len j ∧ AllFuture len j (Sat len w _)) ↔ _
  rw [and_iff_right hj]
  apply future_congr
  intro k _ hk
  cases hf : e.flip <;> simp only [Bool.false_eq_true, ↓reduceIte, Sat, hk, true_and, boolean_sat hb hk]
  all_goals cases w k e.name <;> cases evalBool (w k) e.value <;> decide

omit [DecidableEq α] in
theorem original_environment (hne : ∀ e ∈ ds, ¬Env e.role) :
    SameEnvironment (original kept ds) kept len w w := by
  intro r hr j
  constructor
  · intro h e he er; exact h e (List.mem_append_left _ he) er
  · intro h e he er
    rcases List.mem_append.mp he with he | he
    · exact h e he er
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      apply False.elim
      apply hne d hd
      change Env d.entry.role
      rw [er]; exact hr

omit [DecidableEq α] in
theorem Admissible.nonenv (h : Admissible isIn strict kept ds passes) (he : e ∈ ds) :
    ¬Env e.role :=
  (h.occurrences e.entry (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)) e he definition_self).1

omit [DecidableEq α] in
theorem Admissible.not_self (h : Admissible isIn strict kept ds passes) (he : e ∈ ds) :
    e.name ∉ e.value.atoms := by
  intro hm
  obtain ⟨rank, hr, _⟩ := h.ranked
  have := hr e he e he hm
  omega

theorem normalize_untouched (ha : ¬Defined ds a) : normalize ds n v a = v a := by
  induction n with
  | zero => rfl
  | succ n ih => exact (pass_untouched ha).trans ih

theorem normalize_inputs (h : Admissible isIn strict kept ds passes) :
    KeepsInputs isIn (normalize ds passes) := by
  intro v a ha
  apply normalize_untouched
  rintro ⟨d, hd, rfl⟩
  have := h.outputs d hd
  simp_all

theorem normalize_preserves_on (p : α → Prop)
    (hc : ∀ e ∈ ds, p e.name → ∀ a, a ∈ e.value.atoms → p a)
    (heq : ∀ e ∈ ds, p e.name → v e.name = evalBool v e.value) :
    Agrees p (normalize ds n v) v := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih => exact pass_preserves_on p hc heq ih

omit [DecidableEq α] in
theorem same_environment_trans {v : Word α} (h : SameEnvironment es fs len w v)
    (h' : SameEnvironment fs gs len v u) : SameEnvironment es gs len w u :=
  fun r hr j => (h r hr j).trans (h' r hr j)

theorem normalize_environment (h : Admissible isIn strict kept ds passes) :
    SameEnvironment kept kept len w (fun k => normalize ds passes (w k)) := by
  intro r hr j
  have sat : ∀ e ∈ kept, e.role = r →
      (Sat len w e.formula j ↔ Sat len (fun k => normalize ds passes (w k)) e.formula j) := by
    intro e he er
    apply sat_locality
    intro k _ _ a ha
    apply Eq.symm
    apply normalize_untouched
    rintro ⟨d, hd, hda⟩
    have hh := h.occurrences e (List.mem_append_left _ he) d hd (hda ▸ ha)
    exact hh.1 (er ▸ hr)
  constructor
  · intro hs e he er; exact (sat e he er).mp (hs e he er)
  · intro hs e he er; exact (sat e he er).mpr (hs e he er)

-- This support includes every untouched signal and precisely the definitions
-- whose section can supply equality to the current use.
def CoverSupport (strict : Bool) (ds : List (Definition α)) (use : Role) (a : α) : Prop :=
  ∀ d ∈ ds, d.name = a → covers strict use d.role

theorem normalize_kept (h : Admissible isIn strict kept ds passes)
    (hw : Objective strict (original kept ds) len w) (hx : x ∈ kept)
    (hen : Enabled strict (original kept ds) len w x.role j) :
    Sat len w x.formula j ↔ Sat len (fun k => normalize ds passes (w k)) x.formula j := by
  let p := CoverSupport strict ds x.role
  have closed : ∀ e ∈ ds, p e.name → ∀ a, a ∈ e.value.atoms → p a := by
    intro e he hp a ha d hd hda
    have hc := (h.occurrences e.entry
      (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)) d hd
      (definition_value (hda ▸ ha))).2
    exact covers_trans strict x.role e.role d.role (hp e he rfl) hc
  have eqs : ∀ i, j ≤ i → InRange len i → ∀ e ∈ ds,
      p e.name → w i e.name = evalBool (w i) e.value := by
    intro i hji hi e he hp
    obtain ⟨k, hkj, hk⟩ := enabled_cover (hp e he rfl) (h.nonenv he) hen
    have hs := hw e.entry (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩))
      (h.nonenv he) k hk
    exact (definition_sat (h.boolean e he) hk.1).mp hs i (Nat.le_trans hkj hji) hi
  apply sat_locality
  intro i hji hi a ha
  have hp : p a := by
    intro d hd hda
    exact (h.occurrences x (List.mem_append_left _ hx) d hd (hda ▸ ha)).2
  exact (normalize_preserves_on p closed (eqs i hji hi) a hp).symm

omit [DecidableEq α] in
theorem map_section {v : Word α} (F : Formula α → Formula α)
    (hs : ∀ e ∈ es, ∀ j, Sat len w (F e.formula) j ↔ Sat len v e.formula j) :
    Section (es.map (fun e => ⟨e.role, F e.formula⟩)) r len w j ↔ Section es r len v j := by
  constructor
  · intro h e he er
    apply (hs e he j).mp
    exact h _ (List.mem_map.mpr ⟨e, he, rfl⟩) er
  · intro h e he er
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact (hs x hx j).mpr (h x hx er)

omit [DecidableEq α] in
theorem map_objective {v : Word α} (F : Formula α → Formula α)
    (hs : ∀ e ∈ es, ∀ j, Sat len w (F e.formula) j ↔ Sat len v e.formula j) :
    Objective strict (es.map (fun e => ⟨e.role, F e.formula⟩)) len w ↔ Objective strict es len v := by
  have he : SameEnvironment (es.map (fun e => ⟨e.role, F e.formula⟩)) es len w v :=
    fun _ _ _ => map_section F hs
  constructor
  · intro h e hm hn j hj
    apply (hs e hm j).mp
    exact h _ (List.mem_map.mpr ⟨e, hm, rfl⟩) hn j ((enabled_congr he).mpr hj)
  · intro h e hm hn j hj
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    exact (hs x hx j).mpr (h x hx hn j ((enabled_congr he).mp hj))

theorem residual_objective (h : Admissible isIn strict kept ds passes) :
    Objective strict (residual ds passes kept) len w ↔
      Objective strict kept len (fun k => normalize ds passes (w k)) :=
  map_objective _ (fun _ _ _ => sat_substPasses h.boolean)

theorem elim_backward (h : Admissible isIn strict kept ds passes)
    (hw : Objective strict (original kept ds) len w) :
    Objective strict (residual ds passes kept) len w := by
  apply (residual_objective h).mpr
  have he := same_environment_trans (len := len) (original_environment (fun e he => h.nonenv he))
    (normalize_environment (w := w) h)
  intro x hx hn j hj
  have hen := (enabled_congr he).mpr hj
  exact (normalize_kept h hw hx hen).mp (hw x (List.mem_append_left _ hx) hn j hen)

theorem elim_forward (h : Admissible isIn strict kept ds passes)
    (hw : Objective strict (residual ds passes kept) len w) :
    Objective strict (original kept ds) len (fun k => normalize ds passes (w k)) := by
  have hk := (residual_objective h).mp hw
  have he := original_environment (kept := kept) (len := len) (w := fun k => normalize ds passes (w k)) (fun e he => h.nonenv he)
  intro x hx hn j hj
  rcases List.mem_append.mp hx with hx | hx
  · exact hk x hx hn j ((enabled_congr he).mp hj)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    apply (definition_sat (h.boolean d hd) hj.1).mpr
    intro k _ _
    obtain ⟨rank, hr, hb⟩ := h.ranked
    exact normalize_definitions hr hb h.distinct d hd

omit [DecidableEq α] in
theorem objective_inf : Realizable isIn (objectiveFormula strict es) ↔ InfWin isIn (Objective strict es) := by
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨s, fun i => (objective_sat (by trivial)).mp (hs i)⟩
  · exact ⟨s, fun i => (objective_sat (by trivial)).mpr (hs i)⟩

omit [DecidableEq α] in
theorem objective_fin : FinRealizable isIn (objectiveFormula strict es) ↔ FinWin isIn (Objective strict es) := by
  constructor <;> rintro ⟨s, hs⟩ <;> refine ⟨s, fun i => ?_⟩
  · obtain ⟨n, hn⟩ := hs i
    exact ⟨n, (objective_sat (by simp [InRange])).mp hn⟩
  · obtain ⟨n, hn⟩ := hs i
    exact ⟨n, (objective_sat (by simp [InRange])).mpr hn⟩

theorem elim_realizable_inf (h : Admissible isIn strict kept ds passes) :
    Realizable isIn (objectiveFormula strict (original kept ds)) ↔
      Realizable isIn (objectiveFormula strict (residual ds passes kept)) := by
  rw [objective_inf, objective_inf]
  exact transfer_inf (normalize_inputs h) (fun _ => elim_forward h) (fun _ => elim_backward h)

theorem elim_realizable_fin (h : Admissible isIn strict kept ds passes) :
    FinRealizable isIn (objectiveFormula strict (original kept ds)) ↔
      FinRealizable isIn (objectiveFormula strict (residual ds passes kept)) := by
  rw [objective_fin, objective_fin]
  exact transfer_fin (normalize_inputs h) (fun _ _ => elim_forward h) (fun _ _ => elim_backward h)
end Tlsf
