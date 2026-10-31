import TlsfProofs.Dpa.Impl.Admission
import TlsfProofs.Dpa.Impl.Buchi
import TlsfProofs.Dpa.Impl.Store
import TlsfProofs.Dpa.Impl.Assembly
import TlsfProofs.Dpa.Impl.Transport
import TlsfProofs.Dpa.Impl.Selection
import TlsfProofs.Dpa.Impl.Cache
import TlsfProofs.Dpa.Impl.Grouping
import TlsfProofs.Dpa.Impl.Factoring
import TlsfProofs.Dpa.Impl.DefaultTags
import TlsfProofs.Dpa.Impl.Terminal

/-! Executable diagnostics for the representation bridge. This is not yet an
automaton exporter; its scope is deliberately explicit in the executable name. -/
open Tlsf Tlsf.Dpa Tlsf.Dpa.Impl

private def a : Formula (Fin 2) := .ap 0
private def b : Formula (Fin 2) := .ap 1

private def transportRank : Formula (Fin 2) → Nat
  | .ff => 0 | .tt => 1 | .ap a => a.val + 2 | .neg _ => 4 | _ => 5

private def transportChecks : List (String × Bool × Bool) := [
  ("term-sort-by-ID", decide (termBoolean transportRank true b a = .conj a b), true),
  ("term-duplicate", decide (termBoolean transportRank false a a = a), true),
  ("term-and-false", decide (termBoolean transportRank true a .ff = .ff), true),
  ("term-and-true", decide (termBoolean transportRank true a .tt = a), true),
  ("term-or-false", decide (termBoolean transportRank false a .ff = a), true),
  ("term-or-true", decide (termBoolean transportRank false a .tt = .tt), true),
  ("transport-X-constant", decide (transport transportRank (.next .tt) false 0 = some .tt), true),
  ("transport-F-constant", decide (transport transportRank (.eventually .ff) false 3 = some .ff), true),
  ("transport-G-constant", decide (transport transportRank (.globally .tt) true 2 = some .ff), true),
  ("transport-X-through-and", decide
    (transport transportRank (.next (.conj a b)) false 0 = some (.conj (.next a) (.next b))), true),
  ("transport-pending-X", decide
    (transport transportRank (.next (.disj a b)) false 2 =
      some (.disj (.next (.next (.next a))) (.next (.next (.next b))))), true),
  ("transport-DeMorgan-X", decide
    (transport transportRank (.next (.neg (.conj a b))) false 0 =
      some (.disj (.next (.neg a)) (.next (.neg b)))), true),
  ("transport-modal-reset", decide
    (transport transportRank (.next (.eventually (.conj (.next a) b))) false 0 =
      some (.next (.eventually (.conj b (.next a))))), true),
  ("transport-frozen-absorption", decide
    (transport transportRank (.eventually (.disj a (.conj a b))) false 0 =
      some (.eventually (.disj a (.conj a b)))), true),
  ("transport-U-reset", decide
    (transport transportRank (.next (.until a (.next b))) false 0 =
      some (.next (.until a (.next b)))), true),
  ("transport-U-dual", decide
    (transport transportRank (.until a b) true 0 = some (.release (.neg a) (.neg b))), true),
  ("transport-R-dual", decide
    (transport transportRank (.release a b) true 0 = some (.until (.neg a) (.neg b))), true),
  ("transport-W-dual", decide
    (transport transportRank (.weakUntil a b) true 0 = some (.strongRelease (.neg a) (.neg b))), true),
  ("transport-M-dual", decide
    (transport transportRank (.strongRelease a b) true 0 = some (.weakUntil (.neg a) (.neg b))), true),
  ("transport-F-dual", decide
    (transport transportRank (.eventually a) true 1 = some (.next (.globally (.neg a)))), true),
  ("transport-G-dual", decide
    (transport transportRank (.globally a) true 1 = some (.next (.eventually (.neg a)))), true),
  ("transport-implication", decide
    (transport transportRank (.impl a b) false 0 = some (.disj b (.neg a))), true),
  ("transport-negated-implication", decide
    (transport transportRank (.impl a b) true 0 = some (.conj a (.neg b))), true),
  ("transport-equivalence", decide
    (transport transportRank (.equiv a b) false 0 =
      some (.conj (.disj b (.neg a)) (.disj a (.neg b)))), true),
  ("transport-negated-equivalence", decide
    (transport transportRank (.equiv a b) true 0 =
      some (.disj (.conj a (.neg b)) (.conj b (.neg a)))), true),
  ("transport-reject-strong-next", decide
    (transport transportRank (.strongNext a) false 0 = none), true),
  ("transport-reject-absorbed-strong-next", decide
    (transport transportRank (.conj .ff (.strongNext a)) false 0 = none), true),
  ("X-distribution-changes-frozen-class", equivalent
    (.next (.conj a b)) (.conj (.next a) (.next b)), false)]

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

private def gf : Formula (Fin 2) := .globally (.eventually a)
private def fg : Formula (Fin 2) := .eventually (.globally b)
private def gfFirst (f : Formula (Fin 2)) : Nat := if f = gf then 0 else 1
private def fgFirst (f : Formula (Fin 2)) : Nat := if f = fg then 0 else 1

private def selectionChecks : List (String × Bool × Bool) := [
  ("selection-tautology", decide
    (canonicalPlan gfFirst (.disj a (.neg a)) = some (.constant true)), true),
  ("selection-contradiction", decide
    (canonicalPlan gfFirst (.conj a (.neg a)) = some (.constant false)), true),
  ("selection-whole-GF", decide (canonicalPlan gfFirst gf = some (.whole gf)), true),
  ("selection-mixed-GF-first", decide
    (canonicalPlan gfFirst (.conj gf fg) =
      some (.shannon gf (.whole (.conj .tt fg)) (.constant false))), true),
  ("selection-mixed-FG-first", decide
    (canonicalPlan fgFirst (.conj gf fg) =
      some (.shannon fg (.whole (.conj gf .tt)) (.constant false))), true),
  ("selection-skip-absorbed-variable", decide
    (selectCanonicalPlan [absorbedFrozen, gf, fg] (.conj gf fg) =
      selectCanonicalPlan [gf, fg] (.conj gf fg)), true),
  ("selection-absorbed-unsupported-whole", decide
    (canonicalPlan gfFirst (.disj a (.conj a absorbedFrozen)) =
      some (.whole (.disj a (.conj a absorbedFrozen)))), true),
  ("selection-unsupported-decline", decide (canonicalPlan gfFirst absorbedFrozen = none), true),
  ("cofactor-modal-frozen", decide (cofactor a false (.eventually a) = .eventually a), true),
  ("cofactor-supported-modal", decide (cofactor gf false (.conj gf fg) = .conj .ff fg), true)]

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

private def cacheRank (f : Formula (Fin 2)) : Nat :=
  if f = a then 0 else if f = b then 1 else if f = gf then 2 else 3

private def cacheChoice : Formula (Fin 2) := .disj (.conj a gf) (.conj (.neg a) fg)
private def cacheDag : Formula (Fin 2) := .conj (.disj a b) (.conj gf fg)
private def emptyAcceptance : AcceptanceState 2 := ⟨[], []⟩

private def cachedRun (highFirst : Bool) (f : Formula (Fin 2)) : Option (CachedAssembly 2) :=
  runCanonical (fun _ => highFirst) false
    (orderAtoms cacheRank (modalAtoms f).eraseDups) f emptyAcceptance

private def callIds (r : Option (CachedAssembly 2)) : List Nat :=
  ((r.map CachedAssembly.calls).getD []).map fun f =>
    if equivalent f a then 0 else if equivalent f b then 1
    else if equivalent f gf then 2 else if equivalent f fg then 3 else 4

private def cacheChecks : List (String × Bool × Bool) := [
  ("cache-high-first-success", (cachedRun true cacheChoice).isSome, true),
  ("cache-low-first-success", (cachedRun false cacheChoice).isSome, true),
  ("cache-high-first-call-order", decide (callIds (cachedRun true cacheChoice) = [0, 2, 3]), true),
  ("cache-low-first-call-order", decide (callIds (cachedRun false cacheChoice) = [0, 3, 2]), true),
  ("cache-colour-order-differs", decide
    ((cachedRun true cacheChoice).map (fun r => r.state.store) ≠
     (cachedRun false cacheChoice).map (fun r => r.state.store)), true),
  ("cache-DAG-high-first", decide (callIds (cachedRun true cacheDag) = [0, 2, 3, 1]), true),
  ("cache-DAG-low-first", decide (callIds (cachedRun false cacheDag) = [0, 1, 2, 3]), true),
  ("cache-canonical-key-skips-whole-subtree", decide
    ((cachedRun true cacheDag).bind (fun r =>
      runCanonical (fun _ => false) false [] (.conj .tt cacheDag) r.state) =
     (cachedRun true cacheDag).map (fun r => { r with calls := [] })), true),
  ("cache-old-entry-after-growth", decide
    (((cachedRun true cacheDag).bind (fun r => runCanonical (fun _ => false) false [] (.conj gf fg) r.state)
      |>.map CachedAssembly.calls) = some []), true),
  ("cache-constant-before-entry", decide
    ((runCanonical (fun _ => true) false [] (.disj a (.neg a))
      ⟨[], [⟨.tt, .constant false⟩]⟩ |>.map CachedAssembly.acceptance) = some (.constant true)), true)]

private def groupFormula : Formula (Fin 2) :=
  .conj (.globally b) (.conj (.eventually b) (.conj a (.conj gf fg)))

private def groupIdentity : Formula (Fin 2) :=
  .conj (.globally b)
    (.conj (.disj (.eventually b) (.disj a (.neg a))) (.conj a (.conj gf fg)))

private def groupedRun (safetyFirst : Bool) (f : Formula (Fin 2)) : Option (CachedAssembly 2) :=
  runFactored cacheRank (fun _ => true) (fun _ => safetyFirst) false f f emptyAcceptance

private def groupCallIds (r : Option (CachedAssembly 2)) : List Nat :=
  ((r.map CachedAssembly.calls).getD []).map fun f =>
    if equivalent f gf then 0 else if equivalent f fg then 1
    else if equivalent f (.globally b) then 2
    else if equivalent f (.conj (.eventually b) a) then 3
    else if equivalent f (.conj (.globally b) a) then 4 else 5

private def groupingChecks : List (String × Bool × Bool) := [
  ("grouping-structural-partition", decide
    (let p := partitionSyntax [a, .globally b, .eventually b, gf, fg]
     p.S = [.globally b] ∧ p.C = [.eventually b] ∧ p.B = [a] ∧ p.T = [gf, fg]), true),
  ("grouping-selected-plan-success", (selectSyntaxPlan (fun _ => true)
    (syntaxSize groupFormula + 1) groupFormula).isSome, true),
  ("grouping-run-success", (groupedRun true groupFormula).isSome, true),
  ("grouping-rest-before-safety-cosafety", decide
    (groupCallIds (groupedRun true groupFormula) = [0, 1, 2, 3]), true),
  ("grouping-rest-before-cosafety-safety", decide
    (groupCallIds (groupedRun false groupFormula) = [0, 1, 3, 2]), true),
  ("grouping-review-i-identity", decide
    (groupCallIds (groupedRun true groupIdentity) = [0, 1, 4]), true),
  ("grouping-review-i-either-order", decide
    (groupCallIds (groupedRun false groupIdentity) = [0, 1, 4]), true),
  ("grouping-disjunction", (groupedRun false
    (.disj (.globally b) (.disj (.eventually b) (.disj a (.disj gf fg))))).isSome, true),
  ("grouping-constant-fast-path", decide
    ((groupedRun true (.conj .ff groupFormula)).map CachedAssembly.calls = some []), true),
  ("grouping-research-original-fallback", decide
    ((groupedRun true (.disj a (.conj a absorbedFrozen))).map
      (fun r => r.state.store.length) = some 1), true),
  ("grouping-unsupported-decline", (groupedRun true absorbedFrozen).isSome, false)]

private def distributedG : Formula (Fin 2) :=
  .globally (.conj (.eventually a) (.eventually b))

private def factoredG : Formula (Fin 2) :=
  .conj (.globally (.eventually a)) (.globally (.eventually b))

private def distributedF : Formula (Fin 2) :=
  .eventually (.disj (.globally a) (.globally b))

private def factoredF : Formula (Fin 2) :=
  .disj (.eventually (.globally a)) (.eventually (.globally b))

private def factoringChecks : List (String × Bool × Bool) := [
  ("factor-safety-early-exit", decide
    (factorTerm transportRank 1 (.globally (.conj a b)) = some (.globally (.conj a b))), true),
  ("factor-cosafety-early-exit", decide
    (factorTerm transportRank 1 (.eventually (.disj a b)) = some (.eventually (.disj a b))), true),
  ("factor-G-distribution", decide (factor transportRank distributedG = some factoredG), true),
  ("factor-F-distribution", decide (factor transportRank distributedF = some factoredF), true),
  ("factor-newly-exposed-Boolean", decide
    (factor transportRank (.globally distributedG) = some
      (.conj (.globally (.globally (.eventually a)))
        (.globally (.globally (.eventually b))))), true),
  ("factor-X-rebuilds-without-distribution", decide
    (factor transportRank (.next distributedG) = some (.next factoredG)), true),
  ("factor-U-children", decide
    (factor transportRank (.until distributedG distributedF) = some (.until factoredG factoredF)), true),
  ("factor-R-children", decide
    (factor transportRank (.release distributedG distributedF) = some (.release factoredG factoredF)), true),
  ("factor-W-children", decide
    (factor transportRank (.weakUntil distributedG distributedF) = some (.weakUntil factoredG factoredF)), true),
  ("factor-M-children", decide
    (factor transportRank (.strongRelease distributedG distributedF) =
      some (.strongRelease factoredG factoredF)), true),
  ("factor-smart-constant", decide
    (factor transportRank (.globally (.conj (.eventually a) (.conj .ff gf))) = some .ff), true),
  ("factor-insufficient-fuel", (factorTerm transportRank 1 distributedG).isSome, false),
  ("factor-memo-hit", decide
    (factorCachedTerm transportRank 1 distributedG [(distributedG, factoredG)] =
      some (factoredG, [(distributedG, factoredG)])), true),
  ("factor-memo-frozen-syntax-key", decide
    (lookupFactored (.disj a (.conj a b)) [(a, a)] = none), true),
  ("factor-memo-miss", decide
    ((factorCached transportRank distributedG []).map Prod.fst = some factoredG), true),
  ("factor-cached-early-no-write", decide
    (factorCached transportRank (.globally (.conj a b)) [] =
      some (.globally (.conj a b), [])), true),
  ("factor-sibling-memo-reuse", decide
    ((factorCached transportRank (.until distributedG (.next distributedG)) []).map
      (fun (_, memo) => (memo.filter (fun e => e.1 == distributedG)).length) = some 1), true),
  ("factor-cached-zero-fuel", decide
    (factorCachedTerm transportRank 0 distributedG [(distributedG, factoredG)] = none), true),
  ("factor-cached-newly-exposed-Boolean", decide
    ((factorCached transportRank (.globally distributedG) []).map Prod.fst = some
      (.conj (.globally (.globally (.eventually a)))
        (.globally (.globally (.eventually b))))), true),
  ("factor-changes-frozen-class", equivalent distributedG factoredG, false),
  ("factor-original-admission-still-required", decide
    (runFactoring transportRank (fun _ => true) (fun _ => true) false
      absorbedFrozen emptyAcceptance = none), true),
  ("factor-transport-to-constructor", (runTransported transportRank (fun _ => true)
    (fun _ => true) false (.neg (.eventually
      (.disj (.neg (.eventually a)) (.neg (.eventually b))))) emptyAcceptance).isSome, true)]

private def absorbedOperand : Formula (Fin 2) := .disj a (.conj a (.globally b))
private def absorbedNext : Formula (Fin 2) := .next absorbedOperand
private def absorbedGlobal : Formula (Fin 2) :=
  .globally (.disj (.eventually a) (.conj (.eventually a) (.eventually (.globally b))))

private def defaultTagMask (started : Bool) (f : Formula (Fin 2)) : Option Nat :=
  (defaultTags transportRank (fun _ => false) 32 started f {}).map
    (fun r => fragmentMask r.1)

private def defaultTagChecks : List (String × Bool × Bool) := [
  ("default-tags-false", decide (defaultTagMask false .ff = some 31), true),
  ("default-tags-true", decide (defaultTagMask true .tt = some 31), true),
  ("default-tags-canonical-absorption", decide
    (defaultTagMask true absorbedOperand = some 31), true),
  ("default-tags-prestart-safety-exit", decide
    (defaultTagMask false absorbedNext = some 26), true),
  ("default-tags-started-refines-X", decide
    (defaultTagMask true absorbedNext = some 31), true),
  ("default-tags-recursive-G-absorption", decide
    (defaultTagMask false absorbedGlobal = some 8), true),
  ("default-tags-frozen-structural-differs", decide (tagMask absorbedGlobal = 0), true),
  ("default-tags-prestart-keeps-exact-false", decide
    ((defaultTags transportRank (fun _ => false) 32 false (.globally a) {}).map
      (fun r => r.2.atoms.length) = some 0), true),
  ("default-tags-started-writes-exact", decide
    ((defaultTags transportRank (fun _ => false) 32 true (.globally a) {}).map
      (fun r => r.2.atoms.length) = some 1), true),
  ("default-tags-phase-change-keeps-class-hit", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 false absorbedNext {}
         let (bits, s) ← defaultTags transportRank (fun _ => false) 32 true absorbedNext s
         pure (fragmentMask bits, s.atoms.length)) = some (26, 0)), true),
  ("default-tags-syntax-atom-cache-reuse", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 true absorbedNext {}
         let (bits, s) ← defaultTags transportRank (fun _ => false) 32 true
           (.conj absorbedNext b) s
         pure (fragmentMask bits, s.atoms.length)) = some (31, 1)), true),
  ("default-tags-equivalent-class-hit", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 false absorbedNext {}
         let (bits, s) ← defaultTags transportRank (fun _ => false) 32 true
           (.conj .tt absorbedNext) s
         pure (fragmentMask bits, s.atoms.length)) = some (26, 0)), true),
  ("default-tags-low-first", decide
    (defaultTagMask false (.conj (.globally a) (.eventually b)) = some 24), true),
  ("default-tags-high-first", decide
    ((defaultTags transportRank (fun _ => true) 32 false
      (.conj (.globally a) (.eventually b)) {}).map (fun r => fragmentMask r.1) = some 24), true),
  ("default-tags-cofactor-cache-writes", decide
    ((defaultTags transportRank (fun _ => false) 32 false
      (.conj (.globally a) (.eventually b)) {}).map (fun r => r.2.classes.length) = some 2), true),
  ("default-tags-refined-U", decide
    (defaultTagMask true (.until absorbedOperand b) = some 28), true),
  ("default-tags-refined-M", decide
    (defaultTagMask true (.strongRelease absorbedOperand b) = some 28), true),
  ("default-tags-refined-R", decide
    (defaultTagMask true (.release absorbedOperand b) = some 26), true),
  ("default-tags-refined-W", decide
    (defaultTagMask true (.weakUntil absorbedOperand b) = some 26), true),
  ("default-tags-zero-fuel", (defaultTags transportRank (fun _ => false) 0 true a {}).isNone, true),
  ("default-bounds-structural-low", decide
    (fragmentMask (freshTagBounds {} absorbedNext).low = 26), true),
  ("default-bounds-X-upper", decide
    (fragmentMask (freshTagBounds {} absorbedNext).high = 31), true),
  ("default-bounds-F-upper", decide
    (fragmentMask (freshTagBounds {} (.eventually a)).high = 28), true),
  ("default-bounds-G-upper", decide
    (fragmentMask (freshTagBounds {} (.globally a)).high = 26), true),
  ("default-bounds-refined-low", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 true absorbedNext {}
         pure (fragmentMask (freshTagBounds s absorbedNext).low)) = some 31), true),
  ("default-bounds-cached-before-refinement", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 true absorbedNext {}
         let old := (cachedTagBounds {} absorbedNext []).2
         pure (fragmentMask (cachedTagBounds s absorbedNext old).1.low)) = some 26), true)]

private def terminalAnd : ColourDag 2 := .node 0 (.leaf false)
  (.node 1 (.leaf false) (.leaf true))
private def terminalOr : ColourDag 2 := .node 0
  (.node 1 (.leaf false) (.leaf true)) (.leaf true)
private def terminalNeg : ColourDag 2 := .node 0 (.leaf true) (.leaf false)
private def unknownTerminals : Fin 2 → Option Bool := fun _ => none
private def firstTerminal (b : Bool) : Fin 2 → Option Bool :=
  fun i => if i == 0 then some b else none
private def terminalTest (known : Fin 2 → Option Bool) (f : ColourDag 2) : Option Bool :=
  (terminalShortcut (fun _ => false) 1 known f []).1
private def terminalShared : ColourDag 2 :=
  .node 0 (.node 1 (.leaf false) (.leaf true)) (.node 1 (.leaf false) (.leaf true))

private def terminalChecks : List (String × Bool × Bool) := [
  ("terminal-constant-false", decide
    (terminalTest unknownTerminals (.leaf false) = some false), true),
  ("terminal-constant-true", decide
    (terminalTest unknownTerminals (.leaf true) = some true), true),
  ("terminal-unknown-keeps-symbolic", decide
    (terminalTest unknownTerminals terminalAnd = none), true),
  ("terminal-and-shortcut-false", decide
    (terminalTest (firstTerminal false) terminalAnd = some false), true),
  ("terminal-or-shortcut-true", decide
    (terminalTest (firstTerminal true) terminalOr = some true), true),
  ("terminal-partial-true-is-insufficient", decide
    (terminalTest (firstTerminal true) terminalAnd = none), true),
  ("terminal-all-true", decide
    (terminalTest (fun _ => some true) terminalAnd = some true), true),
  ("terminal-complement-false-target", decide
    (terminalTest (firstTerminal false) terminalNeg = some true), true),
  ("terminal-complement-true-target", decide
    (terminalTest (firstTerminal true) terminalNeg = some false), true),
  ("terminal-pair-rejecting-does-not-decide", decide
    (terminalValue (⟨.globally a, .ff⟩ : State 2) = none), true),
  ("terminal-pair-all-true", decide
    (terminalValue (⟨.tt, .globally a⟩ : State 2) = some true), true),
  ("terminal-pair-all-false", decide
    (terminalValue (⟨.ff, .tt⟩ : State 2) = some false), true),
  ("terminal-canonical-all-true", decide
    (terminalValue (⟨.disj a (.neg a), .ff⟩ : State 2) = some true), true),
  ("terminal-unavailable-target", decide
    (partialTerminalValues (fun _ : Fin 2 => (none : Option (State 2))) 0 = none), true),
  ("terminal-low-first-shared-cache", decide
    ((terminalCondition (fun _ => false) 1 unknownTerminals terminalShared []).2.length = 2), true),
  ("terminal-high-first-shared-cache", decide
    ((terminalCondition (fun _ => true) 1 unknownTerminals terminalShared []).2.length = 2), true),
  ("terminal-epoch-hit-keeps-cache", decide
    (let r := terminalCondition (fun _ => false) 1 (firstTerminal false) terminalAnd []
     (terminalCondition (fun _ => true) 1 (firstTerminal false) terminalAnd r.2).2.length =
       r.2.length), true),
  ("terminal-stale-epoch-ignored", decide
    ((terminalShortcut (fun _ => false) 1 (firstTerminal false) terminalAnd
      [⟨0, terminalAnd, .leaf true⟩]).1 = some false), true),
  ("terminal-equivalent-key-hit", decide
    ((terminalCondition (fun _ => false) 1 unknownTerminals terminalShared
      [⟨1, .node 1 (.leaf false) (.leaf true), .node 1 (.leaf false) (.leaf true)⟩]).2.length = 1), true),
  ("terminal-constant-before-memo", decide
    ((terminalCondition (fun _ => false) 1 unknownTerminals (.leaf false)
      [⟨1, .leaf false, .leaf true⟩]).1 = .leaf false), true),
  ("terminal-empty-colour-true", decide
    ((terminalShortcut (fun _ => false) 1 (fun _ : Fin 0 => none) (.leaf true) []).1 = some true), true),
  ("terminal-true-reserved-priority", decide (terminalPriority 2 true = 5), true),
  ("terminal-false-reserved-priority", decide (terminalPriority 2 false = 4), true),
  ("terminal-ordinary-step", decide
    (shortcutStep 2 (fun (s : Nat) (_ : Unit) => (s+1, 7)) (fun _ _ => none) ()
      (.active 0) = (.active 1, 7)), true),
  ("terminal-enter-reserved-false", decide
    (shortcutStep 2 (fun (s : Nat) (_ : Unit) => (s+1, 7)) (fun _ _ => some false) ()
      (.active 0) = (.absorbing false, 4)), true),
  ("terminal-reserved-loop", decide
    (shortcutStep 2 (fun (s : Nat) (_ : Unit) => (s+1, 7)) (fun _ _ => some true) ()
      (.absorbing false) = (.absorbing false, 4)), true),
  ("terminal-delayed-shortcut-priorities", decide
    ([0, 1, 2, 3, 4].map (shortcutPriorities 2
      (fun (s : Nat) (_ : Unit) => (s+1, 7))
      (fun s _ => if s == 2 then some true else none) 0 (fun _ => ())) = [7, 7, 5, 5, 5]), true),
  ("terminal-Buchi-shortcut-disabled", decide
    ((productTerminalShortcut true (fun _ => false) 1 unknownTerminals (.leaf true) []).1 = none), true),
  ("terminal-parity-shortcut-enabled", decide
    ((productTerminalShortcut false (fun _ => false) 1 unknownTerminals (.leaf true) []).1 = some true), true),
  ("terminal-delayed-sink-state", decide
    (shortcutRun 2 (fun (s : Nat) (_ : Unit) => (s+1, 7))
      (fun s _ => if s == 2 then some true else none) 0 (fun _ => ()) 4 = .absorbing true), true)]

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

theorem transport_checks : transportChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide

theorem selection_checks : selectionChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem cache_checks : cacheChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem grouping_checks : groupingChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem factoring_checks : factoringChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem default_tag_checks : defaultTagChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem terminal_checks : terminalChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

def main : IO UInt32 := do
  let out ← IO.getStdout
  let mut failures := 0
  for (name, actual, expected) in checks ++ componentChecks ++ dualAndAdmissionChecks ++ buchiChecks ++ storeChecks ++ assemblyChecks ++ transportChecks ++ selectionChecks ++ cacheChecks ++ groupingChecks ++ factoringChecks ++ defaultTagChecks ++ terminalChecks do
    out.putStrLn s!"{name}\t{actual}"
    if actual != expected then failures := failures + 1
  out.putStrLn s!"{checks.length + componentChecks.length + dualAndAdmissionChecks.length + buchiChecks.length + storeChecks.length + assemblyChecks.length + transportChecks.length + selectionChecks.length + cacheChecks.length + groupingChecks.length + factoringChecks.length + defaultTagChecks.length + terminalChecks.length} checks, {failures} failures"
  return if failures == 0 then 0 else 1
