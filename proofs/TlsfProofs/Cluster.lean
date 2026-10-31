import TlsfProofs.Definition

namespace Tlsf
structure ClusterEntry (α κ : Type) where
  entry : Entry α
  key : κ

def whole (es : List (ClusterEntry α κ)) : List (Entry α) := es.map ClusterEntry.entry

def cluster [DecidableEq κ] (es : List (ClusterEntry α κ)) (k : κ) : List (Entry α) :=
  (es.filter (fun x => decide (Env x.entry.role ∨ x.key = k))).map ClusterEntry.entry

structure Clustered (isIn : α → Bool) (owner : α → κ) (es : List (ClusterEntry α κ)) : Prop where
  env_inputs : ∀ x ∈ es, Env x.entry.role → ∀ a ∈ x.entry.formula.atoms, isIn a = true
  sys_outputs : ∀ x ∈ es, ¬Env x.entry.role → ∀ a ∈ x.entry.formula.atoms,
    isIn a = false → owner a = x.key

variable [DecidableEq κ]
variable {es : List (ClusterEntry α κ)} {isIn : α → Bool} {owner : α → κ}
  {w v : Word α} {k : κ}

theorem mem_cluster : e ∈ cluster es k ↔ ∃ x ∈ es, x.entry = e ∧ (Env x.entry.role ∨ x.key = k) := by
  simp only [cluster, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hc⟩, he⟩; exact ⟨x, hx, he, hc⟩
  · rintro ⟨x, hx, he, hc⟩; exact ⟨x, ⟨hx, hc⟩, he⟩

theorem cluster_subset (he : e ∈ cluster es k) : e ∈ whole es := by
  obtain ⟨x, hx, rfl, _⟩ := mem_cluster.mp he
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem cluster_env_member (he : e ∈ whole es) (hr : Env e.role) : e ∈ cluster es k := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  exact mem_cluster.mpr ⟨x, hx, rfl, Or.inl hr⟩

theorem cluster_same_environment : SameEnvironment (whole es) (cluster es k) len w w := by
  intro r hr j
  constructor
  · intro h e he er; exact h e (cluster_subset he) er
  · intro h e he er; exact h e (cluster_env_member he (er ▸ hr)) er

theorem cluster_inputs_environment (h : Clustered isIn owner es)
    (ha : ∀ n a, isIn a = true → w n a = v n a) :
    SameEnvironment (whole es) (cluster es k) len w v := by
  have hw : SameEnvironment (whole es) (whole es) len w v := by
    intro r hr j
    have hs : ∀ e ∈ whole es, e.role = r → (Sat len w e.formula j ↔ Sat len v e.formula j) := by
      intro e he er
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      exact sat_locality _ (fun n _ _ a hm => ha n a (h.env_inputs x hx (er ▸ hr) a hm))
    constructor
    · intro hh e he er; exact (hs e he er).mp (hh e he er)
    · intro hh e he er; exact (hs e he er).mpr (hh e he er)
  exact same_environment_trans hw cluster_same_environment

theorem whole_implies_cluster (h : Objective strict (whole es) len w) :
    Objective strict (cluster es k) len w := by
  intro e he hn j hj
  exact h e (cluster_subset he) hn j ((enabled_congr cluster_same_environment).mpr hj)

omit [DecidableEq κ] in
theorem play_input (ha : isIn a = true) : play isIn s i n a = i n a := by
  simp [play, move, ha]

theorem cluster_product (h : Clustered isIn owner es) (ss : κ → Strategy α)
    (hs : ∀ k, ∀ i, Objective strict (cluster es k) len (play isIn (ss k) i)) (i : Word α) :
    Objective strict (whole es) len (play isIn (productStrategy isIn owner ss) i) := by
  let w := play isIn (productStrategy isIn owner ss) i
  intro e he hn j hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have heq : SameEnvironment (whole es) (cluster es x.key) len w (play isIn (ss x.key) i) :=
    cluster_inputs_environment h (fun n a ha => (play_input ha).trans (play_input ha).symm)
  have hsat := hs x.key i x.entry (mem_cluster.mpr ⟨x, hx, rfl, Or.inr rfl⟩)
    hn j ((enabled_congr heq).mp hj)
  apply (sat_locality x.entry.formula (w := w) (v := play isIn (ss x.key) i) ?_).mpr hsat
  intro n _ _ a ha
  cases hin : isIn a with
  | true => exact (play_input hin).trans (play_input hin).symm
  | false =>
    have ho := h.sys_outputs x hx hn a ha hin
    simpa only [w, ho] using product_plays (isIn := isIn) ss owner i a n

theorem clusters_realizable (h : Clustered isIn owner es) :
    Realizable isIn (objectiveFormula strict (whole es)) ↔
      ∀ k, Realizable isIn (objectiveFormula strict (cluster es k)) := by
  simp only [objective_inf]
  constructor
  · rintro ⟨s, hs⟩ k; exact ⟨s, fun i => whole_implies_cluster (hs i)⟩
  · intro hs
    classical
    let ss : κ → Strategy α := fun k => Classical.choose (hs k)
    have hh : ∀ k i, Objective strict (cluster es k) none (play isIn (ss k) i) :=
      fun k => Classical.choose_spec (hs k)
    exact ⟨productStrategy isIn owner ss, fun i => cluster_product h ss hh i⟩

-- The conservative fallback is one unchanged game, so it also works when
-- environments mention outputs or finite strategies choose ending positions.
theorem collapsed_cluster (hkey : ∀ x ∈ es, ¬Env x.entry.role → x.key = k) :
    cluster es k = whole es := by
  unfold cluster whole
  have hf : es.filter (fun x => decide (Env x.entry.role ∨ x.key = k)) = es := by
    apply List.filter_eq_self.mpr
    intro x hx
    apply decide_eq_true
    by_cases he : Env x.entry.role
    · exact Or.inl he
    · exact Or.inr (hkey x hx he)
  rw [hf]

theorem collapsed_cluster_realizable_fin
    (hkey : ∀ x ∈ es, ¬Env x.entry.role → x.key = k) :
    FinRealizable isIn (objectiveFormula strict (whole es)) ↔
      FinRealizable isIn (objectiveFormula strict (cluster es k)) := by
  rw [collapsed_cluster hkey]

theorem empty_cluster_objective (empty : ∀ x ∈ es, x.key = k → Env x.entry.role) :
    Objective strict (cluster es k) len w := by
  intro e he hn
  obtain ⟨x, hx, rfl, hc⟩ := mem_cluster.mp he
  rcases hc with hc | hc
  · exact False.elim (hn hc)
  · exact False.elim (hn (empty x hx hc))

theorem empty_cluster_realizable (empty : ∀ x ∈ es, x.key = k → Env x.entry.role) :
    Realizable isIn (objectiveFormula strict (cluster es k)) := by
  rw [objective_inf]
  exact ⟨fun _ _ _ => false, fun _ => empty_cluster_objective empty⟩
end Tlsf
