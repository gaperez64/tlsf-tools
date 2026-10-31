import TlsfProofs.Dpa.Classes

/-! # STAGE1 §§2,4–5: the complete component and its restricted languages.
The operational definitions also serve STAGE2 §2; Component.lean adds the
invariants. The row numbers below follow both Markdown transition tables.
-/
namespace Tlsf.Dpa
open Class
variable {ap : Nat}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure Pair (ap : Nat) where
  all : Class ap
  rejecting : Class ap

structure Edge (ap : Nat) where
  target : Pair ap
  mark : Bool

def initial (x : Class ap) : Pair ap :=
  if HasTag safety (U x) ∨ HasTag cosafety (U x) then ⟨U x, Class.bot⟩
  else ⟨U x, rho x⟩

/-- STAGE1 §2 / STAGE2 §2: the ordered table, with transition mark 0. -/
def transition (v : Letter (Fin ap)) (s : Pair ap) : Edge ap :=
  let a := D v s.all
  let next := U a
  let r := U (D v s.rejecting)
  if next = Class.bot then ⟨⟨Class.bot, Class.bot⟩, false⟩ -- 1
  else if next = Class.top then ⟨⟨Class.top, Class.bot⟩, true⟩ -- 2
  else if HasTag safety next then ⟨⟨next, Class.bot⟩, true⟩ -- 3
  else if HasTag cosafety next then ⟨⟨next, Class.bot⟩, false⟩ -- 4
  else if r = Class.bot then ⟨⟨next, rho a⟩, false⟩ -- 5
  else if HasTag finite r then
    let q := meet r (rho a)
    if q = Class.bot then ⟨⟨Class.bot, Class.bot⟩, false⟩
    else ⟨⟨next, q⟩, true⟩ -- 6: retain the finite remainder
  else ⟨⟨next, r⟩, false⟩ -- 7

def run (x : Class ap) (w : Word (Fin ap)) : Nat → Pair ap
  | 0 => initial x
  | n+1 => (transition (w n) (run x w n)).target

def marks (x : Class ap) (w : Word (Fin ap)) (n : Nat) : Bool :=
  (transition (w n) (run x w n)).mark

def Inf (m : Nat → Bool) : Prop := ∀ N, ∃ n, N ≤ n ∧ m n = true
def FinMarks (m : Nat → Bool) : Prop := ∃ N, ∀ n, N ≤ n → m n = false

theorem not_inf_iff_fin (m : Nat → Bool) : ¬Inf m ↔ FinMarks m := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := Classical.not_forall.mp h
    exact ⟨N, fun n hn => Bool.eq_false_iff.mpr (fun ht => hN ⟨n, hn, ht⟩)⟩
  · rintro ⟨N, hN⟩ hi
    obtain ⟨n, hn, ht⟩ := hi N
    exact Bool.noConfusion ((hN n hn).symm.trans ht)

/-- Complementing a complete run uses Fin(0), with no change of states. -/
theorem complete_complement (m : Nat → Bool) : FinMarks m ↔ ¬Inf m :=
  (not_inf_iff_fin m).symm

def Simple (x : Class ap) : Prop := HasTag safety x ∨ HasTag cosafety x

theorem simple_step (v : Letter (Fin ap)) (h : Simple x) : Simple (U (D v x)) :=
  h.elim (fun hs => Or.inl (U_safety (D_safety v hs)))
    (fun hc => Or.inr (U_cosafety (D_cosafety v hc)))

theorem simple_transition (v : Letter (Fin ap)) (s : Pair ap) (h : Simple s.all) :
    (transition v s).target.all = U (D v s.all) ∧
    (transition v s).target.rejecting = Class.bot := by
  have ht := simple_step v h
  simp only [transition]
  split
  · rename_i he; exact ⟨he.symm, rfl⟩
  · split
    · rename_i he; exact ⟨he.symm, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · rename_i hsa hco
          exact False.elim (ht.elim hsa hco)

theorem simple_run (x : Class ap) (w : Word (Fin ap)) (h : Simple x) (n : Nat) :
    (run x w n).all = derivatives w 0 n x ∧
    (run x w n).rejecting = Class.bot ∧ Simple (run x w n).all := by
  induction n with
  | zero =>
    have hu : Simple (U x) := h.elim (fun hs => Or.inl (U_safety hs)) (fun hc => Or.inr (U_cosafety hc))
    have hu' : HasTag safety (U x) ∨ HasTag cosafety (U x) := hu
    simp only [run, initial, hu', ↓reduceIte, derivatives]
    exact ⟨trivial, trivial, hu⟩
  | succ n ih =>
    have ht := simple_transition (w n) (run x w n) ih.2.2
    have hs := simple_step (w n) ih.2.2
    refine ⟨?_, ht.2, ?_⟩
    · change (transition (w n) (run x w n)).target.all = _
      rw [ht.1, ih.1, derivatives_snoc, Nat.zero_add]
    · change Simple (transition (w n) (run x w n)).target.all
      rwa [ht.1]

theorem false_transition (v : Letter (Fin ap)) (s : Pair ap) (h : s.all = Class.bot) :
    (transition v s).target.all = Class.bot ∧ (transition v s).mark = false := by
  have hd : D v Class.bot = (Class.bot : Class ap) := by apply Class.ext; intro σ; rfl
  have hu : U Class.bot = (Class.bot : Class ap) := by apply Class.ext; intro σ; rfl
  simp [transition, h, hd, hu]

theorem true_transition (v : Letter (Fin ap)) (s : Pair ap) (h : s.all = Class.top) :
    (transition v s).target.all = Class.top ∧ (transition v s).mark = true := by
  have hne : (Class.top : Class ap) ≠ Class.bot := by
    intro he; have hh := congrArg (fun x : Class ap => x (fun _ => false)) he
    exact Bool.noConfusion hh
  have hd : D v Class.top = (Class.top : Class ap) := by apply Class.ext; intro σ; rfl
  simp [transition, h, hd, U_top, hne]

theorem simple_bot_rejects (x : Class ap) (w : Word (Fin ap)) (h : Simple x)
    (hn : derivatives w 0 n x = Class.bot) : FinMarks (marks x w) := by
  refine ⟨n, fun k hk => ?_⟩
  apply (false_transition _ _ ?_).2
  rw [(simple_run x w h k).1]
  exact derivatives_bot_persists hn hk

theorem simple_top_accepts (x : Class ap) (w : Word (Fin ap)) (h : Simple x)
    (hn : derivatives w 0 n x = Class.top) : Inf (marks x w) := by
  intro N
  refine ⟨max N n, Nat.le_max_left _ _, ?_⟩
  apply (true_transition _ _ ?_).2
  rw [(simple_run x w h _).1]
  exact derivatives_top_persists hn (Nat.le_max_right _ _)

theorem holds_not_bot (h : Holds w j x) : x ≠ Class.bot := by
  intro he; rw [he] at h; exact Bool.noConfusion h

theorem safety_marks (v : Letter (Fin ap)) (s : Pair ap) (h : HasTag safety s.all)
    (hn : U (D v s.all) ≠ Class.bot) : (transition v s).mark = true := by
  have ht := U_safety (D_safety v h)
  by_cases he : U (D v s.all) = Class.top <;> simp_all [transition]

theorem initial_all (x : Class ap) : (initial x).all = U x := by
  unfold initial; split <;> rfl

theorem run_safety (x : Class ap) (w : Word (Fin ap)) (h : HasTag safety x) (n : Nat) :
    HasTag safety (run x w n).all := by
  induction n with
  | zero => rw [run, initial_all]; exact U_safety h
  | succ n ih =>
    change HasTag safety (transition (w n) (run x w n)).target.all
    rw [(simple_transition _ _ (Or.inl ih)).1]
    exact U_safety (D_safety _ ih)

/-- STAGE1 §4, safety, both directions. -/
theorem safety_language (x : Class ap) (hx : Positive x) (hsa : HasTag safety x)
    (w : Word (Fin ap)) : Inf (marks x w) ↔ Holds w 0 x := by
  constructor
  · intro hi
    apply Classical.byContradiction; intro hn
    obtain ⟨n, hc⟩ := class_safety_bad_prefix x hx hsa hn
    exact (complete_complement _).mp (simple_bot_rejects x w (Or.inl hsa) hc) hi
  · intro hw N
    refine ⟨N, Nat.le_refl _, ?_⟩
    apply safety_marks _ _ (run_safety x w hsa N)
    have he := (simple_transition (w N) (run x w N) (Or.inl (run_safety x w hsa N))).1
    rw [← he, show (transition (w N) (run x w N)).target.all = (run x w (N+1)).all from rfl,
      (simple_run x w (Or.inl hsa) (N+1)).1]
    exact holds_not_bot ((derivatives_holds w 0 (N+1) x).mpr hw)

theorem top_hasTag (tag : Formula (Fin ap) → Prop) : HasTag tag Class.top := by
  intro a ha; obtain ⟨σ, b, hb⟩ := ha
  exact False.elim (hb rfl)

theorem cosafety_mark_safety (v : Letter (Fin ap)) (s : Pair ap) (hc : HasTag cosafety s.all)
    (hm : (transition v s).mark = true) : HasTag safety (transition v s).target.all := by
  have ht := U_cosafety (D_cosafety v hc)
  by_cases hb : U (D v s.all) = Class.bot
  · simp [transition, hb] at hm
  · by_cases htop : U (D v s.all) = Class.top
    · have hne : (Class.top : Class ap) ≠ Class.bot := fun he => hb (htop.trans he)
      simpa only [transition, htop, hne, ↓reduceIte] using (top_hasTag safety (ap := ap))
    · by_cases hsa : HasTag safety (U (D v s.all))
      · simp only [transition, hb, htop, hsa, ↓reduceIte]
      · simp [transition, hb, htop, hsa, ht] at hm

theorem run_cosafety (x : Class ap) (w : Word (Fin ap)) (h : HasTag cosafety x) (n : Nat) :
    HasTag cosafety (run x w n).all := by
  induction n with
  | zero => rw [run, initial_all]; exact U_cosafety h
  | succ n ih =>
    change HasTag cosafety (transition (w n) (run x w n)).target.all
    rw [(simple_transition _ _ (Or.inr ih)).1]
    exact U_cosafety (D_cosafety _ ih)

/-- STAGE1 §4, co-safety, including the precedence of the safety row. -/
theorem cosafety_language (x : Class ap) (hx : NNFClass x) (hco : HasTag cosafety x)
    (w : Word (Fin ap)) : Inf (marks x w) ↔ Holds w 0 x := by
  constructor
  · intro hi
    apply Classical.byContradiction; intro hnot
    obtain ⟨n, _, hn⟩ := hi 0
    have hsafe : HasTag safety (run x w (n+1)).all :=
      cosafety_mark_safety (w n) (run x w n) (run_cosafety x w hco n) hn
    have hNNF : NNFClass (run x w (n+1)).all := by
      rw [(simple_run x w (Or.inr hco) (n+1)).1]
      exact derivatives_nnf w 0 (n+1) hx
    have hbad : ¬Holds w (n+1) (run x w (n+1)).all := by
      rw [(simple_run x w (Or.inr hco) (n+1)).1]
      have hd := derivatives_holds w 0 (n+1) x
      simp only [Nat.zero_add] at hd
      exact fun h => hnot (hd.mp h)
    obtain ⟨k, hk⟩ := class_safety_bad_prefix _ (nnfClass_positive hNNF) hsafe hbad
    have he : derivatives w 0 ((n+1)+k) x = Class.bot := by
      rw [derivatives_add]
      simpa only [Nat.zero_add, ← (simple_run x w (Or.inr hco) (n+1)).1] using hk
    exact (complete_complement _).mp (simple_bot_rejects x w (Or.inr hco) he) hi
  · intro hw
    obtain ⟨n, hn⟩ := class_cosafety_witness x (nnfClass_positive hx) hco hw
    exact simple_top_accepts x w (Or.inr hco) hn

theorem safety_complement (x : Class ap) (hx : Positive x) (hsa : HasTag safety x)
    (w : Word (Fin ap)) : FinMarks (marks x w) ↔ ¬Holds w 0 x := by
  rw [complete_complement, safety_language x hx hsa]

theorem cosafety_complement (x : Class ap) (hx : NNFClass x) (hco : HasTag cosafety x)
    (w : Word (Fin ap)) : FinMarks (marks x w) ↔ ¬Holds w 0 x := by
  rw [complete_complement, cosafety_language x hx hco]

/-- The least infinitely recurring priority, expressed with an eventual lower
bound. For bounded streams this is the usual min parity condition. -/
def MinEven (p : Nat → Nat) : Prop :=
  ∃ k, k % 2 = 0 ∧ (∀ N, ∃ n, N ≤ n ∧ p n = k) ∧ ∃ N, ∀ n, N ≤ n → k ≤ p n

/-- The greatest infinitely recurring priority, with an eventual upper bound. -/
def MaxOdd (p : Nat → Nat) : Prop :=
  ∃ k, k % 2 = 1 ∧ (∀ N, ∃ n, N ≤ n ∧ p n = k) ∧ ∃ N, ∀ n, N ≤ n → p n ≤ k

def oneSetMin (complement : Bool) (m : Nat → Bool) (n : Nat) : Nat :=
  if complement then (if m n then 1 else 2) else (if m n then 0 else 1)

def oneSetExport (complement : Bool) (m : Nat → Bool) (n : Nat) : Nat :=
  3 - oneSetMin complement m n

/-- STAGE1 §5: Inf(0), min-even orientation. -/
theorem oneSet_min_inf (m : Nat → Bool) : MinEven (oneSetMin false m) ↔ Inf m := by
  constructor
  · rintro ⟨k, hk, hi, _⟩ N
    have hk0 : k = 0 := by
      obtain ⟨n, _, he⟩ := hi 0
      cases hm : m n <;> simp [oneSetMin, hm] at he <;> omega
    obtain ⟨n, hn, he⟩ := hi N
    refine ⟨n, hn, ?_⟩
    cases hm : m n <;> simp_all [oneSetMin]
  · intro hi
    refine ⟨0, rfl, ?_, 0, fun _ _ => Nat.zero_le _⟩
    intro N; obtain ⟨n, hn, hm⟩ := hi N
    exact ⟨n, hn, by simp [oneSetMin, hm]⟩

/-- STAGE1 §5: Fin(0), min-even orientation. -/
theorem oneSet_min_fin (m : Nat → Bool) : MinEven (oneSetMin true m) ↔ FinMarks m := by
  constructor
  · rintro ⟨k, hk, hi, N, hN⟩
    have hk2 : k = 2 := by
      obtain ⟨n, _, he⟩ := hi 0
      cases hm : m n <;> simp [oneSetMin, hm] at he <;> omega
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn
    cases hm : m n <;> simp_all [oneSetMin]
  · rintro ⟨N, hN⟩
    refine ⟨2, rfl, ?_, N, ?_⟩
    · intro M
      exact ⟨max M N, Nat.le_max_left _ _, by simp [oneSetMin, hN _ (Nat.le_max_right _ _)]⟩
    · intro n hn; simp [oneSetMin, hN n hn]

/-- STAGE1 §5: Inf(0), max-odd export (marked 3, unmarked 2). -/
theorem oneSet_max_inf (m : Nat → Bool) : MaxOdd (oneSetExport false m) ↔ Inf m := by
  constructor
  · rintro ⟨k, hk, hi, _⟩ N
    have hk3 : k = 3 := by
      obtain ⟨n, _, he⟩ := hi 0
      cases hm : m n <;> simp [oneSetExport, oneSetMin, hm] at he <;> omega
    obtain ⟨n, hn, he⟩ := hi N
    refine ⟨n, hn, ?_⟩
    cases hm : m n <;> simp_all [oneSetExport, oneSetMin]
  · intro hi
    refine ⟨3, rfl, ?_, 0, ?_⟩
    · intro N; obtain ⟨n, hn, hm⟩ := hi N
      exact ⟨n, hn, by simp [oneSetExport, oneSetMin, hm]⟩
    · intro n _; cases hm : m n <;> simp [oneSetExport, oneSetMin, hm]

/-- STAGE1 §5: Fin(0), max-odd export (marked 2, unmarked 1). -/
theorem oneSet_max_fin (m : Nat → Bool) : MaxOdd (oneSetExport true m) ↔ FinMarks m := by
  constructor
  · rintro ⟨k, hk, hi, N, hN⟩
    have hk1 : k = 1 := by
      obtain ⟨n, _, he⟩ := hi 0
      cases hm : m n <;> simp [oneSetExport, oneSetMin, hm] at he <;> omega
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn
    cases hm : m n <;> simp_all [oneSetExport, oneSetMin]
  · rintro ⟨N, hN⟩
    refine ⟨1, rfl, ?_, N, ?_⟩
    · intro M
      exact ⟨max M N, Nat.le_max_left _ _, by simp [oneSetExport, oneSetMin, hN _ (Nat.le_max_right _ _)]⟩
    · intro n hn; simp [oneSetExport, oneSetMin, hN n hn]

end
end Tlsf.Dpa
