import TlsfProofs.Dpa.Impl.Admission
import TlsfProofs.Dpa.Impl.Buchi
import TlsfProofs.Dpa.Impl.Store
import TlsfProofs.Dpa.Impl.Assembly

/-! Executable diagnostics for the representation bridge. This is not yet an
automaton exporter; its scope is deliberately explicit in the executable name. -/
open Tlsf Tlsf.Dpa Tlsf.Dpa.Impl

private def a : Formula (Fin 2) := .ap 0
private def b : Formula (Fin 2) := .ap 1

private def checks : List (String × Bool × Bool) := [
  ("absorption", equivalent (.disj a (.conj a b)) a, true),
  ("tautology", equivalent (.disj a (.neg a)) .tt, true),
  ("contradiction", equivalent (.conj a (.neg a)) .ff, true),
  ("AP-negation", equivalent (.neg a) a, false),
  ("frozen-operands", equivalent (.eventually (.disj a (.conj a b))) (.eventually a), false),
  ("independent-duals", equivalent (.neg (.eventually a)) (.globally (.neg a)), false),
  ("absorbed-support", uses (.disj a (.conj a b)) b, false),
  ("essential-support", uses (.disj a (.conj a b)) a, true),
  ("absent-support", uses a (.eventually b), false),
  ("frozen-support", uses (.eventually (.next b)) (.next b), false),
  ("outer-support", uses (.eventually (.next b)) (.eventually (.next b)), true),
  ("constant-support", uses (.disj a (.neg a)) a, false)]

private def reviewBody (x : Formula (Fin 2)) : Formula (Fin 2) := .disj a (.conj a x)

private def reviewR (x : Formula (Fin 2)) : Formula (Fin 2) := .disj (.eventually (reviewBody x)) x

private def reviewK : Formula (Fin 2) := .globally (reviewR (.next (.eventually b)))

private def reviewL : Formula (Fin 2) := .globally (reviewR (.next (.next b)))

private def absorbedFrozen : Formula (Fin 2) :=
  .globally (.disj (.eventually a) (.conj (.eventually a) (.eventually (.globally b))))

private def componentChecks : List (String × Bool × Bool) := [
  ("GF-pi2", classTag .pi2 (.globally (.eventually a)), true),
  ("FG-sigma2", classTag .sigma2 (.eventually (.globally a)), true),
  ("review-k-accept", researchAdmitted reviewK, true),
  ("review-l-accept", researchAdmitted reviewL, true),
  ("frozen-absorption-decline", researchAdmitted absorbedFrozen, false),
  ("U-left-protection", protectedb (.until (.next a) b) (.next a), true),
  ("U-right-protection", protectedb (.until a (.next b)) (.next b), true),
  ("M-left-protection", protectedb (.strongRelease (.next a) b) (.next a), true),
  ("M-right-protection", protectedb (.strongRelease a (.next b)) (.next b), true),
  ("nested-X-protection", protectedb (.eventually (.next (.next a))) (.next a), true),
  ("absorbed-protector", protectedb (.disj a (.conj a (.eventually (.next b)))) (.next b), false),
  ("review-k-remainder", equivalent (Impl.initial reviewK).rejecting
    (.disj a (reviewR (.next (.eventually b)))), true),
  ("review-l-remainder", equivalent (Impl.initial reviewL).rejecting
    (.disj a (reviewR (.next (.next b)))), true),
  ("GF-retry", equivalent (Impl.initial (.globally (.eventually a))).rejecting
    (.disj a (.eventually a)), true),
  ("simultaneous-STEP", equivalent (stepSyntax (fun _ => true) (.next a)) a, true),
  ("finite-retention", equivalent
    (Impl.transition (fun _ => false) ⟨unfoldSyntax (.globally (.eventually a)), .next a⟩).target.rejecting a, true),
  ("finite-renewal-mark",
    (Impl.transition (fun _ => false) ⟨unfoldSyntax (.globally (.eventually a)), .next a⟩).mark, true)]

private def dualAndAdmissionChecks : List (String × Bool × Bool) := [
  ("sigma2-oriented-dual", classTag .pi2 (dual (.eventually (.globally a))), true),
  ("dual-language-is-not-Boolean-complement", equivalent (dual (.eventually a)) (.neg (.eventually a)), false),
  ("dual-class-congruence", equivalent
    (dual (.disj (.eventually a) (.conj (.eventually a) (.next b))))
    (dual (.eventually a)), true),
  ("absorbed-unsupported-sigma2", classTag .pi2 (dual
    (.disj (.eventually (.globally a)) (.conj (.eventually (.globally a)) (.globally (.eventually (.globally b)))))), true),
  ("mixed-whole-class", researchAdmitted (.conj (.globally (.eventually a)) (.eventually (.globally b))), false),
  ("mixed-canonical-admission", canonicalResearchCheck (.conj (.globally (.eventually a)) (.eventually (.globally b))), true),
  ("frozen-absorption-full-decline", canonicalResearchCheck absorbedFrozen, false),
  ("absorbed-unsupported-admission", canonicalResearchCheck (.disj a (.conj a absorbedFrozen)), true),
  ("review-i-identity-grouping", decide
    (Impl.compatibleGroups true [.globally b]
      [.disj (.eventually b) (.disj a (.neg a))] [a] [] =
      [booleanFold true [.globally b, a],
       booleanFold true [.disj (.eventually b) (.disj a (.neg a))]]), true),
  ("nonidentity-grouping", decide
    (Impl.compatibleGroups true [.globally b] [.eventually b] [a] [] =
      [booleanFold true [.globally b], booleanFold true [.eventually b, a]]), true)]

private def bothColours : ColourDag 2 :=
  (PositiveAcceptance.conj (.colour 0) (.colour 1)).compile

private def eitherColour : ColourDag 2 :=
  (PositiveAcceptance.disj (.colour 0) (.colour 1)).compile

private def alternating (n : Nat) (i : Fin 2) : Bool := decide (n % 2 = i.val)

private def firstMarks (β : ColourDag 2) (count : Nat) : List Bool :=
  (List.range count).map (completedRounds β alternating)

private def buchiChecks : List (String × Bool × Bool) := [
  ("Buchi-alternating-conjunction", decide (firstMarks bothColours 6 =
    [false, true, false, true, false, true]), true),
  ("Buchi-alternating-disjunction", decide (firstMarks eitherColour 4 =
    [true, true, true, true]), true),
  ("Buchi-missing-conjunct", decide ((List.range 4).map
    (completedRounds bothColours (fun _ i => decide (i.val = 0))) =
    [false, false, false, false]), true),
  ("Buchi-constant-true", decide (firstMarks (.leaf true) 3 = [true, true, true]), true),
  ("Buchi-constant-false", decide (firstMarks (.leaf false) 3 = [false, false, false]), true),
  ("Buchi-initial-true", (roundInitial (.leaf true : ColourDag 0)).incoming, true),
  ("Buchi-initial-false", (roundInitial (.leaf false : ColourDag 0)).incoming, false),
  ("Buchi-incoming-delay", decide ((List.range 6).map (incomingMarks bothColours alternating) =
    [true, false, true, false, true, false]), true),
  ("Buchi-source-priority", decide ((List.range 6).map (buchiPriority bothColours alternating) =
    [1, 0, 1, 0, 1, 0]), true),
  ("Buchi-state-split", decide
    ((roundTransition eitherColour ⟨eitherColour, true⟩ (alternating 0)).target =
       (roundTransition eitherColour ⟨eitherColour, false⟩ (alternating 0)).target ∧
     (roundTransition eitherColour ⟨eitherColour, true⟩ (alternating 0)).priority ≠
       (roundTransition eitherColour ⟨eitherColour, false⟩ (alternating 0)).priority), true)]

private def storedGF : ComponentStore 2 :=
  (internComponent false [] (.globally (.eventually a))).1

private def storedAP : ComponentStore 2 := (internComponent false [] a).1

private def storeChecks : List (String × Bool × Bool) := [
  ("store-fresh-pi2", decide ((internComponent false [] (.globally (.eventually a))).2 =
    ⟨0, false⟩), true),
  ("store-fresh-sigma2", decide ((internComponent false [] (.eventually (.globally a))).2 =
    ⟨0, true⟩), true),
  ("store-sigma2-oriented-run", decide
    ((freshComponent (.eventually (.globally a))).formula = dual (.eventually (.globally a))), true),
  ("store-equal-class-hit", decide
    ((internComponent false storedGF (.disj (.globally (.eventually a))
      (.conj (.globally (.eventually a)) (.next b)))).1.length = 1), true),
  ("store-cached-dual-hit", decide
    ((internComponent false storedGF (dual (.globally (.eventually a)))).2 = ⟨0, true⟩), true),
  ("store-repeat-sigma2", decide
    ((internComponent false (internComponent false [] (.eventually (.globally a))).1
      (.eventually (.globally a))).2 = ⟨0, true⟩), true),
  ("store-append-index", decide ((internComponent false storedAP b).2 = ⟨1, false⟩), true),
  ("store-preserve-existing-entry", decide ((internComponent false storedAP b).1[0]? = storedAP[0]?), true),
  ("store-parity-shares-weak-dual", decide
    ((internComponent false storedAP (.neg a)).2 = ⟨0, true⟩), true),
  ("store-Buchi-separates-weak-dual", decide
    ((internComponent true storedAP (.neg a)).2 = ⟨1, false⟩), true),
  ("store-ordered-lookup", decide
    ((internComponent false (internComponent true storedAP (.neg a)).1 (.neg a)).2 =
      ⟨0, true⟩), true)]

private def mixedPlan : AcceptancePlan 2 :=
  .binary true (.whole (.globally (.eventually a))) (.whole (.eventually (.globally b)))

private def sharedPlan : AcceptancePlan 2 := .binary true (.whole a) (.whole a)

private def shannonPlan : AcceptancePlan 2 := .shannon a (.whole b) (.whole (.neg b))

private def assemblyChecks : List (String × Bool × Bool) := [
  ("assembly-constant", decide ((assemble false (.constant true : AcceptancePlan 2) []).store = []), true),
  ("assembly-folded-tautology", decide
    ((assemble false (.whole (.disj a (.neg a))) []).acceptance = .constant true), true),
  ("assembly-mixed-orientations", decide
    ((assemble false mixedPlan []).acceptance =
      .binary true (.literal ⟨0, false⟩) (.literal ⟨1, true⟩)), true),
  ("assembly-shared-literal", decide
    ((assemble false sharedPlan []).store.length = 1 ∧
     (assemble false sharedPlan []).acceptance =
       .binary true (.literal ⟨0, false⟩) (.literal ⟨0, false⟩)), true),
  ("assembly-Shannon-cached-dual", decide
    ((assemble false shannonPlan []).store.length = 2 ∧
     (assemble false shannonPlan []).acceptance =
       .ite ⟨0, false⟩ (.literal ⟨1, false⟩) (.literal ⟨1, true⟩)), true),
  ("assembly-Shannon-old-index", decide
    ((assemble false shannonPlan storedAP).store[0]? = storedAP[0]?), true),
  ("assembly-group-identity", decide
    ((assemble false (groupedPlan true [.globally b]
      [.disj (.eventually b) (.disj a (.neg a))] [a] []) []).store.length = 1), true),
  ("assembly-group-nonidentity", decide
    ((assemble false (groupedPlan true [.globally b] [.eventually b] [a] []) []).store.length = 2), true)]

/-- Kernel reduction and the executable run check the same definitions. -/
theorem class_checks : checks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide

theorem component_checks : componentChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide

theorem dual_admission_checks : dualAndAdmissionChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide

theorem buchi_checks : buchiChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide

theorem store_checks : storeChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide

theorem assembly_checks : assemblyChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide

def main : IO UInt32 := do
  let out ← IO.getStdout
  let mut failures := 0
  for (name, actual, expected) in checks ++ componentChecks ++ dualAndAdmissionChecks ++ buchiChecks ++ storeChecks ++ assemblyChecks do
    out.putStrLn s!"{name}\t{actual}"
    if actual != expected then failures := failures + 1
  out.putStrLn s!"{checks.length + componentChecks.length + dualAndAdmissionChecks.length + buchiChecks.length + storeChecks.length + assemblyChecks.length} checks, {failures} failures"
  return if failures == 0 then 0 else 1
