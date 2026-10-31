import TlsfProofs.Dpa.Validation.Construction
import TlsfProofs.Dpa.Validation.Checks

/-! Executable and kernel-checked reference-construction regressions. -/
open Tlsf Tlsf.Dpa Tlsf.Dpa.Impl

private def a : Formula (Fin 2) := .ap 0
private def b : Formula (Fin 2) := .ap 1
private def rank (_ : Formula (Fin 2)) : Nat := 0
private def gf : Formula (Fin 2) := .globally (.eventually a)
private def fg : Formula (Fin 2) := .eventually (.globally a)
private def absorbed : Formula (Fin 2) :=
  .globally (.disj (.eventually a) (.conj (.eventually a) (.eventually (.globally b))))
private def word (n : Nat) : Letter (Fin 2) := fun i => decide (i.val = n % 2)

private def probe (f : Formula (Fin 2)) : Bool :=
  match construct rank rank f with
  | none => false
  | some r =>
    let p := (List.range 6).map (r.parity.priorities word)
    !p.isEmpty

private def checks : List (String × Bool) := [
  ("absorption", equivalent (.disj a (.conj a b)) a),
  ("finite-transport", decide (transport rank (.next .tt) false 0 = some .tt)),
  ("GF-admission", transportedResearchCheck rank gf),
  ("FG-admission", transportedResearchCheck rank fg),
  ("frozen-review-research-decline", !transportedResearchCheck rank absorbed),
  ("GF-executable-parity", probe gf),
  ("FG-executable-parity", probe fg),
  ("top-absorption-executable-parity", probe (.disj gf (.conj gf fg))),
  ("positive-round-acceptance", positiveb (fun v : Fin 2 → Bool => v 0 && v 1)),
  ("negative-round-rejected", !positiveb (fun v : Fin 2 → Bool => !v 0))]

private def runtimeChecks : List (String × Bool) := [
  ("zero-colour-tree", decide ((buildTree (fun _ : Fin 0 → Bool => true)
    (fullColours 0)).advance [] Fin.elim0 = ([], 0)))]

theorem construction_checks : checks.all Prod.snd = true := by decide

def main : IO UInt32 := do
  let out ← IO.getStdout
  let mut failures := 0
  for (name, ok) in checks ++ runtimeChecks ++ Validation.equivalenceChecks do
    if !ok then
      failures := failures + 1
      out.putStrLn s!"FAIL {name}"
  out.putStrLn s!"{checks.length + runtimeChecks.length + Validation.equivalenceChecks.length} checks, {failures} failures"
  pure (if failures = 0 then 0 else 1)
