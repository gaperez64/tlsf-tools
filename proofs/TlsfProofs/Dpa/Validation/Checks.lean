import TlsfProofs.Dpa.Validation.Equivalence

/-! Regressions where language equality needs more than a state bijection or
identical priorities. Checked by reduction in the kernel and by the executable. -/
namespace Tlsf.Dpa.Validation

def singleton (p : Nat) : Parity (Fin 2) (Fin 1) := ⟨0, fun _ _ => (0,p)⟩
def alternating (p q : Nat) : Parity (Fin 2) (Fin 2) :=
  ⟨0, fun s _ => if s = 0 then (1,p) else (0,q)⟩
def transient : Parity (Fin 2) (Fin 2) :=
  ⟨0, fun s _ => (1, if s = 0 then 7 else 2)⟩
def unreachable : Parity (Fin 2) (Fin 2) :=
  ⟨0, fun s _ => (s, if s = 0 then 3 else 0)⟩
def infLetters : Parity (Fin 2) (Fin 1) :=
  ⟨0, fun _ a => (0, if a = 0 then 1 else 0)⟩
def allBuchi : Buchi (Fin 2) (Fin 1) := ⟨0, fun _ _ => 0, fun _ => true⟩
def alternatingBuchi : Buchi (Fin 2) (Fin 2) :=
  ⟨0, fun s _ => if s = 0 then 1 else 0, fun s => decide (s = 0)⟩
def noneBuchi : Buchi (Fin 2) (Fin 1) := ⟨0, fun _ _ => 0, fun _ => false⟩

def equivalenceChecks : List (String × Bool) := [
  ("different-state-count-and-priorities", check (singleton 1) (alternating 3 0)),
  ("priority-renaming", check (singleton 3) (singleton 7)),
  ("opposite-parity-detected", !check (singleton 1) (singleton 0)),
  ("transient-priority-ignored", check transient (singleton 0)),
  ("unreachable-state-ignored", check (singleton 1) unreachable),
  ("letter-dependent-disagreement", !check (singleton 1) infLetters),
  ("same-letter-dependent-language", check infLetters infLetters),
  ("two-recurrent-priority-maxima", !check (alternating 3 2) (alternating 2 1)),
  ("buchi-different-state-count", checkBuchi allBuchi alternatingBuchi),
  ("buchi-rejecting-loop", !checkBuchi alternatingBuchi noneBuchi)]

theorem equivalence_checks : equivalenceChecks.all Prod.snd = true := by decide

end Tlsf.Dpa.Validation
