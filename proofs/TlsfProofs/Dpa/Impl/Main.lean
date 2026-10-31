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
import TlsfProofs.Dpa.Impl.RefinedComponent
import TlsfProofs.Dpa.Impl.TagTrace
import TlsfProofs.Dpa.Impl.RefinedAcceptance
import TlsfProofs.Dpa.Impl.RefinedConverse
import TlsfProofs.Dpa.Impl.SupportedTrace
import TlsfProofs.Dpa.Impl.QuickTrace
import TlsfProofs.Dpa.Impl.RemainderTrace
import TlsfProofs.Dpa.Impl.ComponentTrace
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
  ("default-tags-phase-change-clears-class-hit", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 false absorbedNext {}
         let (bits, s) ← startDefaultTags transportRank (fun _ => false) 32 absorbedNext s
         pure (fragmentMask bits, s.atoms.length)) = some (31, 1)), true),
  ("default-tags-start-retains-exact-atoms", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 false absorbedGlobal {}
         pure (s.start.atoms.length, s.start.classes.length)) = some (1, 0)), true),
  ("default-tags-syntax-atom-cache-reuse", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 true absorbedNext {}
         let (bits, s) ← defaultTags transportRank (fun _ => false) 32 true
           (.conj absorbedNext b) s
         pure (fragmentMask bits, s.atoms.length)) = some (31, 1)), true),
  ("default-tags-equivalent-class-hit", decide
    ((do let (_, s) ← defaultTags transportRank (fun _ => false) 32 true absorbedNext {}
         let (bits, s) ← defaultTags transportRank (fun _ => false) 32 true
           (.conj .tt absorbedNext) s
         pure (fragmentMask bits, s.atoms.length)) = some (31, 1)), true),
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

/-- Diagnostics read fresh default tag computations for each query. This
is a sound interface instance, not a model of C's shared cache trace. -/
private def diagnosticTags (f : Formula (Fin 2)) : FragmentBits :=
  match defaultTags transportRank (fun _ => false) 64 true f {} with
  | none => classBits f
  | some (bits, _) => bits

private theorem diagnosticTags_sound : TagClassifier.Sound diagnosticTags := by
  intro f t ht
  cases he : defaultTags transportRank (fun _ => false) 64 true f {} with
  | none =>
    simp only [diagnosticTags, he] at ht
    exact refined_structural_lower f t ht
  | some r =>
    rcases r with ⟨bits, s⟩
    simp only [diagnosticTags, he] at ht
    exact (defaultTags_sound transportRank (fun _ => false) 64 true f {} bits s
      TagCache.empty_valid he).2.2 t ht

private def refinedProtector : Formula (Fin 2) := .eventually absorbedNext

private def queryTrace (f : Formula (Fin 2)) : TagProgram 2 Unit := .query f (fun _ => .done ())

private def repeatTrace : TagProgram 2 (Nat × Nat × Nat) :=
  .query absorbedNext (fun first =>
    .query (.conj absorbedNext b) (fun middle =>
      .query (.conj .tt absorbedNext) (fun last =>
        .done (fragmentMask first, fragmentMask middle, fragmentMask last))))

private def sharedTrace (highFirst : Bool) : Option ((Nat × Nat × Nat) × TagCache 2) :=
  repeatTrace.exec (defaultTags transportRank (fun _ => highFirst) 32 true) {}

private def phasedTrace (n : Nat) : Option (TagCache 2) :=
  defaultTrace transportRank (fun _ => false) 32 (queryTrace absorbedNext)
    (fun k => queryTrace (if k == 0 then absorbedNext else .conj absorbedNext b)) {} n

private def traceChecks : List (String × Bool × Bool) := [
  ("trace-repeat-and-equivalent-key", decide
    ((sharedTrace false).map Prod.fst = some (31, 31, 31)), true),
  ("trace-high-first", decide
    ((sharedTrace true).map Prod.fst = some (31, 31, 31)), true),
  ("trace-frozen-cache-shared", decide
    ((sharedTrace false).map (fun r => r.2.atoms.length) = some 1), true),
  ("trace-final-classifier-replays", decide
    ((sharedTrace false).map (fun r => repeatTrace.eval (cacheClassifier r.2)) = some (31, 31, 31)), true),
  ("trace-startup-clears-weak-class", decide
    ((phasedTrace 0).map (fun s => fragmentMask (cacheClassifier s absorbedNext)) = some 31), true),
  ("trace-later-query-retains-answer", decide
    ((phasedTrace 1).map (fun s => fragmentMask (cacheClassifier s absorbedNext)) = some 31), true),
  ("trace-later-cache-hit-no-growth", decide
    ((do let s ← phasedTrace 1; let t ← phasedTrace 2
         pure (s.atoms.length == t.atoms.length && s.classes.length == t.classes.length)) = some true), true),
  ("trace-untouched-structural-fallback", decide
    (fragmentMask (cacheClassifier ({} : TagCache 2) absorbedNext) = 26), true),
  ("trace-constant-before-arbitrary-cell", decide
    (fragmentMask (cacheClassifier {classes := [(.tt, fun _ => false)] : TagCache 2} .tt) = 31), true),
  ("trace-query-failure-is-explicit", (repeatTrace.exec
    (defaultTags transportRank (fun _ => false) 0 true) {}).isSome, false)]

/-- A universal language witness uses the persistent trace, not the fresh
diagnostic classifier. Its soundness premise is discharged by the interpreter. -/
theorem shared_trace_language_witness (w : Word (Fin 2)) (n : Nat) :
    Sat none w (runTagged
      (defaultTraceClassifier transportRank (fun _ => false) 32 (queryTrace absorbedNext)
        (fun _ => queryTrace (.conj absorbedNext b)) {}) absorbedNext w n).all n ↔
      Sat none w absorbedNext 0 :=
  defaultTrace_all_language _ _ _ _ _ _ TagCache.empty_valid
    (by simp [absorbedNext, absorbedOperand, NNF, a, b]) w n

/-- Accepting-language equality for a nonstructural finite input, driven by
the persistent shared trace. The finite certificate is kernel computed. -/
theorem shared_trace_acceptance_witness (w : Word (Fin 2)) :
    Inf (marksTagged
      (defaultTraceClassifier transportRank (fun _ => false) 32 (queryTrace absorbedNext)
        (fun _ => queryTrace (.conj absorbedNext b)) {}) absorbedNext w) ↔
      Sat none w absorbedNext 0 := by
  apply defaultTrace_finite_language _ _ _ _ _ _ TagCache.empty_valid
    (by simp [absorbedNext, absorbedOperand, NNF, a, b])
  exact diagnosticTags_sound absorbedNext .finite (by decide +kernel)

theorem shared_trace_pi2_language_witness (w : Word (Fin 2)) :
    Inf (marksTagged
      (defaultTraceClassifier transportRank (fun _ => false) 32 (queryTrace absorbedNext)
        (fun _ => queryTrace (.conj absorbedNext b)) {}) gf w) ↔ Sat none w gf 0 :=
  defaultTrace_pi2_language _ _ _ _ _ _ TagCache.empty_valid
    (by simp [gf, NNF, a]) (by decide +kernel) w

theorem shared_trace_false_seeds_witness (w : Word (Fin 2))
    (hf : ¬Sat none w gf 0)
    (hnever : ∀ n, Class.ofFormula (runTagged
      (defaultTraceClassifier transportRank (fun _ => false) 32 (queryTrace absorbedNext)
        (fun _ => queryTrace (.conj absorbedNext b)) {}) gf w n).all ≠ Class.bot) :
    ∃ N, ∀ n, N ≤ n → ¬Sat none w
      (rhoTagged
        (defaultTraceClassifier transportRank (fun _ => false) 32 (queryTrace absorbedNext)
          (fun _ => queryTrace (.conj absorbedNext b)) {} n)
        (rawTagged
          (defaultTraceClassifier transportRank (fun _ => false) 32 (queryTrace absorbedNext)
            (fun _ => queryTrace (.conj absorbedNext b)) {}) gf w n)) n :=
  runTagged_eventually_false_seeds _
    (fun n => (defaultTraceClassifier_spec _ _ _ _ _ _ TagCache.empty_valid n).1)
    (fun n => (defaultTraceClassifier_spec _ _ _ _ _ _ TagCache.empty_valid n).2)
    (by simp [gf, NNF, a]) (by decide +kernel) w hf hnever

private def supportedF : Formula (Fin 2) := .eventually a
private def supportedG : Formula (Fin 2) := .globally b
private def supportedOrder : Formula (Fin 2) :=
  .disj (.conj a supportedF) (.conj (.neg a) supportedG)
private def supportedShared : Formula (Fin 2) :=
  .disj (.conj a supportedF) (.conj b supportedF)
private def supportedAbsorbed : Formula (Fin 2) := .disj a (.conj a gf)
private def supportedRun (f : Formula (Fin 2)) :
    Option (Option (Formula (Fin 2)) × TagCache 2) :=
  (rhoSupported transportRank f).exec (defaultTags transportRank (fun _ => false) 32 true) {}

private def supportedChecks : List (String × Bool × Bool) := [
  ("supported-absorbed-atom-not-queried", decide
    ((reduceSupported [gf, a] supportedAbsorbed).reads classBits = []), true),
  ("supported-AP-succeeds-with-zero-tag-fuel", decide
    (((reduceSupported [gf, a] supportedAbsorbed).exec
      (defaultTags transportRank (fun _ => false) 0 true) {}).map
        (fun r => r.1.isSome) = some true), true),
  ("supported-low-before-high", decide
    ((reduceSupported [a, supportedF, supportedG] supportedOrder).reads classBits =
      [supportedG, supportedF]), true),
  ("supported-shared-subgraph-queries-once", decide
    ((reduceSupported [a, b, supportedF] supportedShared).reads classBits = [supportedF]), true),
  ("supported-equivalent-mapped-hit-skips-query", decide
    ((mapSupported reduceAtomProgram [] supportedF [(.conj .tt supportedF, supportedF)]).reads
      classBits = []), true),
  ("supported-incomplete-alphabet-fails", decide
    ((reduceSupported [] supportedF).eval classBits = none), true),
  ("supported-constant-precedes-invalid-memo", decide
    ((mapSupported reduceAtomProgram [] (.tt : Formula (Fin 2)) [(.tt, .ff)]).eval classBits =
      some (.tt, [(.tt, .ff)])), true),
  ("supported-empty-tag-fuel-fails-on-modal-query", decide
    (((reduceSupported [supportedF] supportedF).exec
      (defaultTags transportRank (fun _ => false) 0 true) {}).isSome = false), true),
  ("supported-GF-retry-five-exact-calls", decide
    (((rhoSupported transportRank gf).reads classBits).length = 5), true),
  ("supported-GF-retry-preserves-eventuality", decide
    (((rhoSupported transportRank gf).eval classBits).map
      (fun r => equivalent r (unfoldSyntax supportedF)) = some true), true),
  ("supported-shared-default-execution-succeeds", (supportedRun gf).isSome, true),
  ("supported-default-result-matches-final-classifier", decide
    ((supportedRun gf).map (fun result => result.1.any (fun r =>
      equivalent r (rhoTagged (cacheClassifier result.2) gf))) = some true), true)]

private def quickTest (f : Formula (Fin 2)) (mask : List FragmentTag) :=
  hasTags transportRank (fun _ => false) 32 true f mask ({} : QuickCache 2)

private def quickRho (f : Formula (Fin 2)) :=
  (rhoSupported transportRank f).execQuick transportRank (fun _ => false) 32 true {}

private def quickRepeat : TagProgram 2 (Bool × Bool × Bool) :=
  .test absorbedNext [.cosafety] fun first =>
    .test (.conj .tt absorbedNext) [.finite] fun second =>
      .test absorbedNext [.safety, .cosafety] fun third => .done (first, second, third)

private def quickChecks : List (String × Bool × Bool) := [
  ("quick-lower-hit-skips-exact", decide
    ((quickTest supportedF [.cosafety]).map (fun r =>
      (r.1, r.2.tags.atoms.length, r.2.tags.classes.length)) = some (true, 0, 0)), true),
  ("quick-upper-miss-skips-exact", decide
    ((quickTest supportedF [.safety]).map (fun r =>
      (r.1, r.2.tags.atoms.length, r.2.tags.classes.length)) = some (false, 0, 0)), true),
  ("quick-undecided-refines-frozen-operand", decide
    ((quickTest absorbedNext [.cosafety]).map (fun r => (r.1, r.2.tags.atoms.length)) =
      some (true, 1)), true),
  ("quick-bounds-snapshot-stays-stale", decide
    ((quickTest absorbedNext [.finite]).map (fun r =>
      ((lookupTagBounds absorbedNext r.2.bounds).map (fun b => fragmentMask b.low),
       fragmentMask (freshTagBounds r.2.tags absorbedNext).low)) = some (some 26, 31)), true),
  ("quick-recursive-low-high-cells", decide
    ((quickTest (.conj a supportedF) [.cosafety]).map (fun r => r.2.bounds.length) = some 4), true),
  ("quick-empty-mask-skips-exact", decide
    ((quickTest absorbedNext []).map (fun r => (r.1, r.2.tags.classes.length)) = some (false, 0)), true),
  ("quick-mixed-mask-lower-wins", decide
    ((quickTest supportedF [.safety, .cosafety]).map (fun r =>
      (r.1, r.2.tags.classes.length)) = some (true, 0)), true),
  ("quick-equivalent-key-repeat", decide
    ((quickRepeat.execQuick transportRank (fun _ => false) 32 true {}).map Prod.fst =
      some (true, true, true)), true),
  ("quick-final-classifier-replays-predicates", decide
    ((quickRepeat.execQuick transportRank (fun _ => false) 32 true {}).map (fun r =>
      quickRepeat.eval (quickClassifier r.2)) = some (true, true, true)), true),
  ("quick-constant-true-empty-tag-cache", decide
    ((quickTest .tt [.finite]).map (fun r => (r.1, r.2.tags.classes.length)) = some (true, 0)), true),
  ("quick-constant-false-all-tags", decide
    ((quickTest .ff [.cosafety]).map Prod.fst = some true), true),
  ("quick-bounds-fuel-failure-explicit", decide
    ((hasTags transportRank (fun _ => false) 0 true a [.finite] {}).isSome = false), true),
  ("quick-startup-retains-bounds", decide
    ((quickTest absorbedNext [.finite]).map (fun r =>
      (r.2.start.tags.classes.length, r.2.start.tags.atoms.length, r.2.start.bounds.length)) =
      some (0, 1, 3)), true),
  ("quick-GF-extraction-matches-realized-classifier", decide
    ((quickRho gf).map (fun r => r.1.any (fun f =>
      equivalent f (rhoTagged (quickClassifier r.2) gf))) = some true), true),
  ("quick-absorbed-next-extraction", decide
    ((quickRho absorbedNext).map (fun r => r.1.any (fun f =>
      equivalent f (rhoTagged (quickClassifier r.2) absorbedNext))) = some true), true)]

private def memoRho (f : Formula (Fin 2)) (memo : RemainderCache 2 := [])
    (fuel : Nat := 32) (s : QuickCache 2 := {}) :=
  (rhoMemo transportRank f memo).execQuick transportRank (fun _ => false) fuel true s

private def memoRow (a r : Formula (Fin 2)) (memo : RemainderCache 2 := []) :=
  (rowMemo transportRank a r memo).execQuick transportRank (fun _ => false) 32 true {}

private def startupProtector : Formula (Fin 2) := .eventually (.disj a (.conj a absorbedNext))
private def startupFormula : Formula (Fin 2) := .conj absorbedNext startupProtector

/-- This follows both compiled initial calls, retaining the old remainder
memo while resetting class tags. It refutes unrestricted memo equality at
reset; it does not assert a language counterexample or constructor admission. -/
private def startupMemoProbe : Option (Bool × Bool × Nat) := do
  let (some (old, memo), s) ← (initialMemo transportRank startupFormula []).execQuick
    transportRank (fun _ => false) 32 false {} | none
  let (some (state, _), t) ← (initialMemo transportRank startupFormula memo).execQuick
    transportRank (fun _ => false) 32 true s.start | none
  pure (equivalent old.rejecting (rhoTagged (quickClassifier t) startupFormula),
    equivalent state.rejecting .ff, memo.length)

theorem startup_memo_mismatch : startupMemoProbe = some (false, true, 1) := by
  decide +kernel

private def memoChecks : List (String × Bool × Bool) := [
  ("memo-GF-first-miss-caches-retry-and-source", decide
    ((memoRho gf).map (fun r => r.1.map (fun (_, memo) => memo.length)) = some (some 2)), true),
  ("memo-GF-result-realized", decide
    ((memoRho gf).map (fun r => r.1.any (fun (f, _) =>
      equivalent f (rhoTagged (quickClassifier r.2) gf))) = some true), true),
  ("memo-equivalent-key-hit-needs-no-fuel", decide
    ((do let (some (f, memo), s) ← memoRho gf | none
         let (some (g, out), _) ← memoRho (.conj .tt gf) memo 0 s | none
         pure (equivalent f g, out.length)) = some (true, 2)), true),
  ("memo-hit-keeps-query-caches", decide
    ((do let (some (_, memo), s) ← memoRho gf | none
         let (_, t) ← memoRho gf memo 0 s
         pure (s.tags.classes.length == t.tags.classes.length &&
           s.tags.atoms.length == t.tags.atoms.length && s.bounds.length == t.bounds.length)) = some true), true),
  ("memo-hit-program-has-no-predicates", decide
    ((rhoMemo transportRank gf [(gf, supportedF)]).reads classBits = []), true),
  ("memo-unfolded-hit-has-no-finite-predicate", decide
    ((rhoUnfoldedMemo transportRank (unfoldSyntax gf)
      [(unfoldSyntax gf, unfoldSyntax supportedF)]).reads classBits = []), true),
  ("memo-retry-hit-skips-second-extraction", decide
    (((rhoMemo transportRank gf [(unfoldSyntax gf, unfoldSyntax supportedF)]).reads classBits).map
      (fun f => (equivalent f gf, equivalent f .tt)) = [(true, false), (false, true)]), true),
  ("memo-first-miss-has-five-predicates", decide
    (((rhoMemo transportRank gf []).reads classBits).length = 5), true),
  ("memo-failure-does-not-become-success", decide
    ((memoRho gf [] 0).isSome = false), true),
  ("memo-unfolded-no-second-retry", decide
    ((memoRho (unfoldSyntax gf)).map (fun r => r.1.map (fun (_, memo) => memo.length)) =
      some (some 1)), true),
  ("memo-startup-keeps-remainder-hit", decide
    ((do let (some (f, memo), s) ← memoRho gf | none
         let (some (g, out), _) ← memoRho gf memo 0 s.start | none
         pure (equivalent f g, out.length)) = some (true, 2)), true),
  ("memo-startup-equality-can-fail-while-component-suspends", decide
    (startupMemoProbe = some (false, true, 1)), true),
  ("component-program-false-sink-skips-queries", decide
    ((rowMemo transportRank (.ff : Formula (Fin 2)) supportedF []).reads classBits = []), true),
  ("component-program-true-sink-skips-queries", decide
    ((rowMemo transportRank (.tt : Formula (Fin 2)) supportedF []).reads classBits = []), true),
  ("component-program-safety-precedes-cosafety", decide
    ((rowMemo transportRank (.globally a) supportedF []).reads classBits =
      [unfoldSyntax (.globally a)]), true),
  ("component-program-cosafety-suspends", decide
    ((memoRow supportedF supportedG).map (fun r => r.1.any (fun (e, memo) =>
      !e.mark && equivalent e.target.rejecting .ff && decide (memo.length = 0))) = some true), true),
  ("component-program-continue-keeps-old-obligation", decide
    ((memoRow gf supportedF).map (fun r => r.1.any (fun (e, memo) =>
      !e.mark && equivalent e.target.rejecting supportedF && decide (memo.length = 0))) = some true), true),
  ("component-program-seed-hit-after-two-guards", decide
    ((rowMemo transportRank gf .ff [(gf, unfoldSyntax supportedF)]).reads classBits =
      [unfoldSyntax gf, unfoldSyntax gf]), true),
  ("component-program-retains-finite-remainder", decide
    ((memoRow gf a).map (fun r => r.1.any (fun (e, _) =>
      e.mark && equivalent e.target.rejecting (.conj a (unfoldSyntax supportedF)))) = some true), true),
  ("component-program-false-renewal-takes-sink", decide
    ((memoRow (.conj a gf) (.neg a)).map (fun r => r.1.any (fun (e, _) =>
      !e.mark && equivalent e.target.all .ff)) = some true), true),
  ("component-startup-single-combined-mask", decide
    ((initialMemo transportRank supportedF []).reads classBits = [unfoldSyntax supportedF]), true),
  ("component-startup-program-realized", decide
    (((initialMemo transportRank gf []).execQuick transportRank (fun _ => false) 32 true {}).map
      (fun r => r.1.any (fun (s, _) =>
        equivalent s.all (initialTagged (quickClassifier r.2) gf).all &&
        equivalent s.rejecting (initialTagged (quickClassifier r.2) gf).rejecting)) = some true), true)]

private def refinedProtected : Formula (Fin 2) := .conj absorbedNext refinedProtector

private def refinedChecks : List (String × Bool × Bool) := [
  ("refined-finite-structural-miss", classTag .finite absorbedNext, false),
  ("refined-finite-recursive-hit", diagnosticTags absorbedNext .finite, true),
  ("refined-co-structural-miss", classTag .cosafety refinedProtector, false),
  ("refined-co-recursive-hit", diagnosticTags refinedProtector .cosafety, true),
  ("refined-reduce-keeps-frozen-co", decide
    (reduceTagged diagnosticTags refinedProtector = refinedProtector), true),
  ("refined-research-reduce-elides-frozen", equivalent (reduce refinedProtector) .tt, true),
  ("refined-protection-keeps-X", protectedb
    (reduceTagged diagnosticTags refinedProtected) absorbedNext, true),
  ("refined-drop-X-keeps-protected", equivalent
    (dropX (reduceTagged diagnosticTags refinedProtected)) refinedProtected, true),
  ("refined-drop-X-elides-unprotected", equivalent
    (dropX (reduceTagged diagnosticTags absorbedNext)) .tt, true),
  ("refined-rho-keeps-co-obligation", equivalent
    (rhoTagged diagnosticTags refinedProtector) (unfoldSyntax refinedProtector), true),
  ("refined-retry-on-GF", equivalent
    (rhoTagged diagnosticTags (.globally (.eventually a))) (.disj a (.eventually a)), true),
  ("refined-initial-suspends", decide
    ((initialTagged diagnosticTags absorbedNext).rejecting = .ff), true),
  ("refined-after-X-accepting-letter", (transitionTagged diagnosticTags (fun _ => true)
    (runTagged (fun _ => diagnosticTags) absorbedNext (fun _ _ => true) 1)).mark, true),
  ("refined-after-X-rejecting-letter", (transitionTagged diagnosticTags (fun _ => false)
    (runTagged (fun _ => diagnosticTags) absorbedNext (fun _ _ => false) 1)).mark, false),
  ("refined-safety-row", (transitionTagged diagnosticTags (fun _ => true)
    (initialTagged diagnosticTags (.globally absorbedOperand))).mark, true),
  ("refined-cosafety-row", (transitionTagged diagnosticTags (fun _ => false)
    (initialTagged diagnosticTags (.eventually absorbedOperand))).mark, false),
  ("refined-finite-renewal-mark", (transitionTagged diagnosticTags (fun _ => false)
    ⟨unfoldSyntax (.globally (.eventually a)), absorbedNext⟩).mark, true),
  ("refined-finite-renewal-retains", equivalent
    (transitionTagged diagnosticTags (fun _ => false)
      ⟨unfoldSyntax (.globally (.eventually a)), absorbedNext⟩).target.rejecting a, true),
  ("refined-false-renewal-explicit-sink", decide
    ((rowTagged diagnosticTags (.conj a (.globally (.eventually b))) (.neg a)).target.all = .ff), true),
  ("refined-simultaneous-X-then-AP", equivalent
    (runTagged (fun _ => diagnosticTags) absorbedNext (fun _ _ => false) 2).all .ff, true)]

/-- A nonstructural finite-window witness exercises the language theorem,
not merely the executable classifier's returned mask. -/
theorem refined_window_witness (w v : Word (Fin 2)) (j : Nat)
    (hw : ∀ k, j ≤ k → k ≤ j+1 → w k = v k) :
    Sat none w absorbedNext j ↔ Sat none v absorbedNext j := by
  have hb : diagnosticTags absorbedNext .finite = true := by decide +kernel
  exact refined_finite_window (diagnosticTags_sound absorbedNext .finite hb) w v j hw

theorem refined_obligation_witness (w : Word (Fin 2)) (n : Nat) :
    TaggedInvariant (runTagged (fun _ => diagnosticTags) (.globally (.eventually a)) w n) :=
  (runTagged_spec (fun _ => diagnosticTags) (fun _ => diagnosticTags_sound) (by trivial) w n).1

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

theorem refined_checks : refinedChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem trace_checks : traceChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem supported_checks : supportedChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem quick_checks : quickChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem memo_checks : memoChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

theorem terminal_checks : terminalChecks.all (fun (_, actual, expected) => actual == expected) = true := by
  decide +kernel

def main : IO UInt32 := do
  let out ← IO.getStdout
  let mut failures := 0
  for (name, actual, expected) in checks ++ componentChecks ++ dualAndAdmissionChecks ++ buchiChecks ++ storeChecks ++ assemblyChecks ++ transportChecks ++ selectionChecks ++ cacheChecks ++ groupingChecks ++ factoringChecks ++ defaultTagChecks ++ refinedChecks ++ traceChecks ++ supportedChecks ++ quickChecks ++ memoChecks ++ terminalChecks do
    out.putStrLn s!"{name}\t{actual}"
    if actual != expected then failures := failures + 1
  out.putStrLn s!"{checks.length + componentChecks.length + dualAndAdmissionChecks.length + buchiChecks.length + storeChecks.length + assemblyChecks.length + transportChecks.length + selectionChecks.length + cacheChecks.length + groupingChecks.length + factoringChecks.length + defaultTagChecks.length + refinedChecks.length + traceChecks.length + supportedChecks.length + quickChecks.length + memoChecks.length + terminalChecks.length} checks, {failures} failures"
  return if failures == 0 then 0 else 1
