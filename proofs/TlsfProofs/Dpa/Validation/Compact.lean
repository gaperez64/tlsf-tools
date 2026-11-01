import TlsfProofs.Dpa.Validation.Equivalence

/-! Checked alphabet reduction before the language checker. Letters are merged
only when both complete tables have identical transitions and priorities at
every state. This removes unused AP valuations without a locality assumption. -/
namespace Tlsf.Dpa.Validation
variable {na nb alphabet : Nat}

def sameLetter (A : Parity (Fin alphabet) (Fin na))
    (B : Parity (Fin alphabet) (Fin nb)) (a b : Fin alphabet) : Bool :=
  (List.finRange na).all (fun s => decide (A.step s a = A.step s b)) &&
    (List.finRange nb).all (fun s => decide (B.step s a = B.step s b))

theorem sameLetter_exact (A : Parity (Fin alphabet) (Fin na))
    (B : Parity (Fin alphabet) (Fin nb)) (a b : Fin alphabet) :
    sameLetter A B a b = true ↔
      (∀ s, A.step s a = A.step s b) ∧ (∀ s, B.step s a = B.step s b) := by
  simp [sameLetter, List.all_eq_true]

def letterRepresentatives (A : Parity (Fin alphabet) (Fin na))
    (B : Parity (Fin alphabet) (Fin nb)) : Array (Fin alphabet) :=
  (List.finRange alphabet).foldl (fun reps a =>
    if reps.any (sameLetter A B a) then reps else reps.push a) #[]

def lettersCovered (A : Parity (Fin alphabet) (Fin na))
    (B : Parity (Fin alphabet) (Fin nb)) (reps : Array (Fin alphabet)) : Bool :=
  (List.finRange alphabet).all (fun a => reps.any (sameLetter A B a))

def Parity.reletter (A : Parity (Fin alphabet) (Fin na)) (reps : Array (Fin alphabet)) :
    Parity (Fin reps.size) (Fin na) := ⟨A.initial, fun s a => A.step s reps[a]⟩

private theorem reletter_language (A : Parity (Fin alphabet) (Fin na))
    (reps : Array (Fin alphabet)) (select : Fin alphabet → Fin reps.size)
    (hs : ∀ s a, A.step s a = A.step s reps[select a]) (w : Nat → Fin alphabet) :
    (A.reletter reps).Accepts (fun n => select (w n)) ↔ A.Accepts w := by
  have hr (n : Nat) : (A.reletter reps).run (fun n => select (w n)) n = A.run w n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (A.step ((A.reletter reps).run (fun n => select (w n)) n)
        reps[select (w n)]).1 = (A.step (A.run w n) (w n)).1
      rw [ih, ← hs]
  have hp : (A.reletter reps).priorities (fun n => select (w n)) = A.priorities w := by
    funext n
    change (A.step ((A.reletter reps).run (fun n => select (w n)) n)
      reps[select (w n)]).2 = (A.step (A.run w n) (w n)).2
    rw [hr, ← hs]
  change MaxOdd _ ↔ MaxOdd _
  rw [hp]

def checkCompact (A : Parity (Fin alphabet) (Fin na))
    (B : Parity (Fin alphabet) (Fin nb)) : Bool :=
  let reps := letterRepresentatives A B
  lettersCovered A B reps && check (A.reletter reps) (B.reletter reps)

theorem checkCompact_sound (A : Parity (Fin alphabet) (Fin na))
    (B : Parity (Fin alphabet) (Fin nb)) (h : checkCompact A B = true) :
    ∀ w, A.Accepts w ↔ B.Accepts w := by
  classical
  let reps := letterRepresentatives A B
  obtain ⟨hc, he⟩ := Bool.and_eq_true_iff.mp h
  have cover (a : Fin alphabet) : ∃ i : Fin reps.size, sameLetter A B a reps[i] = true := by
    obtain ⟨i, hi, he⟩ := Array.any_eq_true.mp ((List.all_eq_true.mp hc) a (by simp))
    exact ⟨⟨i, hi⟩, he⟩
  let select := fun a => Classical.choose (cover a)
  have hs (a : Fin alphabet) := (sameLetter_exact A B a reps[select a]).mp
    (Classical.choose_spec (cover a))
  intro w
  exact (reletter_language A reps select (fun s a => (hs a).1 s) w).symm.trans
    ((check_sound _ _ he (fun n => select (w n))).trans
      (reletter_language B reps select (fun s a => (hs a).2 s) w))

def Buchi.reletter (A : Buchi (Fin alphabet) (Fin na)) (reps : Array (Fin alphabet)) :
    Buchi (Fin reps.size) (Fin na) :=
  ⟨A.initial, fun s a => A.step s reps[a], A.accepting⟩

def checkBuchiCompact (A : Buchi (Fin alphabet) (Fin na))
    (B : Buchi (Fin alphabet) (Fin nb)) : Bool :=
  let reps := letterRepresentatives A.toParity B.toParity
  lettersCovered A.toParity B.toParity reps &&
    checkBuchi (A.reletter reps) (B.reletter reps)

theorem checkBuchiCompact_sound (A : Buchi (Fin alphabet) (Fin na))
    (B : Buchi (Fin alphabet) (Fin nb)) (h : checkBuchiCompact A B = true) :
    ∀ w, A.Accepts w ↔ B.Accepts w := by
  have he := checkCompact_sound A.toParity B.toParity h
  intro w
  exact (A.toParity_language w).symm.trans ((he w).trans (B.toParity_language w))

end Tlsf.Dpa.Validation
