import TlsfProofs.Dpa.Impl.RemainderTrace

/-!
# Ordered component query programs

Startup is `src/lib/dpa_dela.c:327`; the row order is `:5`. The program
threads the persistent remainder memo explicitly and uses `execQuick` for
all predicates. Its same-phase refinement preserves the remainder-cache
realization invariant. Crossing C's startup reset remains separate.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

def initialMemo (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (memo : RemainderCache ap) : TagProgram ap (Option (State ap × RemainderCache ap)) :=
  let all := unfoldSyntax f
  .test all [.safety, .cosafety] fun suspend =>
    if suspend then .done (some (⟨all, .ff⟩, memo))
    else (rhoMemo rank f memo).bind fun result =>
      .done (result.map (fun (r, out) => (⟨all, r⟩, out)))

def rowMemo (rank : Formula (Fin ap) → Nat) (a r : Formula (Fin ap))
    (memo : RemainderCache ap) : TagProgram ap (Option (Edge ap × RemainderCache ap)) :=
  let next := unfoldSyntax a
  if equivalent next .ff then .done (some (⟨⟨.ff, .ff⟩, false⟩, memo))
  else if equivalent next .tt then .done (some (⟨⟨.tt, .ff⟩, true⟩, memo))
  else .test next [.safety] fun safe =>
    if safe then .done (some (⟨⟨next, .ff⟩, true⟩, memo))
    else .test next [.cosafety] fun co =>
      if co then .done (some (⟨⟨next, .ff⟩, false⟩, memo))
      else if equivalent r .ff then
        (rhoMemo rank a memo).bind fun result =>
          .done (result.map (fun (seed, out) => (⟨⟨next, seed⟩, false⟩, out)))
      else .test r [.finite] fun finite =>
        if finite then (rhoMemo rank a memo).bind fun result => match result with
          | none => .done none
          | some (seed, out) =>
            let q := Formula.conj r seed
            if equivalent q .ff then .done (some (⟨⟨.ff, .ff⟩, false⟩, out))
            else .done (some (⟨⟨next, q⟩, true⟩, out))
        else .done (some (⟨⟨next, r⟩, false⟩, memo))

def transitionMemo (rank : Formula (Fin ap) → Nat) (v : Letter (Fin ap))
    (s : State ap) (memo : RemainderCache ap) :=
  rowMemo rank (stepSyntax v s.all) (unfoldSyntax (stepSyntax v s.rejecting)) memo

theorem initialMemo_predicateOnly (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (memo : RemainderCache ap) : (initialMemo rank f memo).PredicateOnly := by
  intro suspend
  dsimp only
  split
  · trivial
  · apply TagProgram.PredicateOnly.bind _ (rhoMemo_predicateOnly rank f memo)
    intro _; trivial

theorem rowMemo_predicateOnly (rank : Formula (Fin ap) → Nat) (a r : Formula (Fin ap))
    (memo : RemainderCache ap) : (rowMemo rank a r memo).PredicateOnly := by
  simp only [rowMemo]
  split
  · trivial
  · split
    · trivial
    · intro safe
      dsimp only
      split
      · trivial
      · intro co
        dsimp only
        split
        · trivial
        · split
          · apply TagProgram.PredicateOnly.bind _ (rhoMemo_predicateOnly rank a memo)
            intro _; trivial
          · intro finite
            dsimp only
            split
            · apply TagProgram.PredicateOnly.bind _ (rhoMemo_predicateOnly rank a memo)
              intro result
              cases result with
              | none => trivial
              | some result =>
                rcases result with ⟨seed, out⟩
                dsimp only
                split <;> trivial
            · trivial

theorem initialMemo_spec (tags : TagClassifier ap) (hc : tags.Congruent)
    (rank : Formula (Fin ap) → Nat) (hm : memo.Realized tags)
    (he : (initialMemo rank f memo).eval tags = some (s, out)) :
    s.denote = (initialTagged tags f).denote ∧ out.Realized tags := by
  simp only [initialMemo, TagProgram.eval, List.any_cons, List.any_nil, Bool.or_false] at he
  simp only [initialTagged]
  split at he
  · rename_i h
    simp only [h, ↓reduceIte]
    cases Option.some.inj he
    exact ⟨rfl, hm⟩
  · rename_i h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    simp only [TagProgram.eval_bind, TagProgram.eval] at he
    cases hr : (rhoMemo rank f memo).eval tags with
    | none => simp [hr] at he
    | some result =>
      rcases result with ⟨seed, mout⟩
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hseed, hmout⟩ := rhoMemo_spec tags hc rank hm hr
      exact ⟨by simp only [State.denote, hseed], hmout⟩

theorem rowMemo_spec (tags : TagClassifier ap) (hc : tags.Congruent)
    (rank : Formula (Fin ap) → Nat) (hm : memo.Realized tags)
    (he : (rowMemo rank a r memo).eval tags = some (e, out)) :
    e.denote = (rowTagged tags a r).denote ∧ out.Realized tags := by
  simp only [rowMemo] at he
  simp only [rowTagged]
  split at he
  · rename_i h
    simp only [h, ↓reduceIte]
    cases Option.some.inj he
    exact ⟨rfl, hm⟩
  · rename_i hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    split at he
    · rename_i h
      simp only [h, ↓reduceIte]
      cases Option.some.inj he
      exact ⟨rfl, hm⟩
    · rename_i ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      simp only [TagProgram.eval, List.any_cons, List.any_nil, Bool.or_false] at he
      split at he
      · rename_i h
        simp only [h, ↓reduceIte]
        cases Option.some.inj he
        exact ⟨rfl, hm⟩
      · rename_i hs
        simp only [hs, Bool.false_eq_true, ↓reduceIte]
        simp only [TagProgram.eval, List.any_cons, List.any_nil, Bool.or_false] at he
        split at he
        · rename_i h
          simp only [h, ↓reduceIte]
          cases Option.some.inj he
          exact ⟨rfl, hm⟩
        · rename_i hco
          simp only [hco, Bool.false_eq_true, ↓reduceIte]
          split at he
          · rename_i h
            simp only [h, ↓reduceIte]
            simp only [TagProgram.eval_bind, TagProgram.eval] at he
            cases hr : (rhoMemo rank a memo).eval tags with
            | none => simp [hr] at he
            | some result =>
              rcases result with ⟨seed, mout⟩
              simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              obtain ⟨hseed, hmout⟩ := rhoMemo_spec tags hc rank hm hr
              exact ⟨by simp only [Edge.denote, State.denote, hseed], hmout⟩
          · rename_i hrbot
            simp only [hrbot, Bool.false_eq_true, ↓reduceIte]
            simp only [TagProgram.eval, List.any_cons, List.any_nil, Bool.or_false] at he
            split at he
            · rename_i hfinite
              simp only [hfinite, ↓reduceIte]
              simp only [TagProgram.eval_bind] at he
              cases hr : (rhoMemo rank a memo).eval tags with
              | none => simp [hr, TagProgram.eval] at he
              | some result =>
                rcases result with ⟨seed, mout⟩
                simp only [hr] at he
                obtain ⟨hseed, hmout⟩ := rhoMemo_spec tags hc rank hm hr
                have hconj : Class.ofFormula (.conj r seed) =
                    Class.ofFormula (.conj r (rhoTagged tags a)) := by
                  change meet (Class.ofFormula r) (Class.ofFormula seed) =
                    meet (Class.ofFormula r) (Class.ofFormula (rhoTagged tags a))
                  rw [hseed]
                have hq : equivalent (.conj r seed) .ff = equivalent (.conj r (rhoTagged tags a)) .ff := by
                  apply Bool.eq_iff_iff.mpr
                  simp only [equivalent_exact, hconj]
                split at he
                · rename_i hzero
                  rw [hq] at hzero
                  simp only [hzero, ↓reduceIte]
                  cases Option.some.inj he
                  exact ⟨rfl, hmout⟩
                · rename_i hzero
                  rw [hq] at hzero
                  simp only [hzero, Bool.false_eq_true, ↓reduceIte]
                  cases Option.some.inj he
                  exact ⟨by simp only [Edge.denote, State.denote, hconj], hmout⟩
            · rename_i hfinite
              simp only [hfinite, Bool.false_eq_true, ↓reduceIte]
              cases Option.some.inj he
              exact ⟨rfl, hm⟩

theorem initialMemo_quick (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (s : QuickCache ap) (hs : s.Valid) (memo : RemainderCache ap) (hm : memo.Realizes s)
    (he : (initialMemo rank f memo).execQuick rank highFirst fuel started s =
      some (some (state, out), last)) :
    state.denote = (initialTagged (quickClassifier last) f).denote ∧
      out.Realizes last ∧ last.Valid ∧ s.Extends last := by
  obtain ⟨hv, hx, hr⟩ := TagProgram.execQuick_spec rank highFirst fuel started _ s hs he
  have hresult (future : QuickCache ap) (hf : last.Extends future) (hvf : future.Valid) :
      state.denote = (initialTagged (quickClassifier future) f).denote ∧
        out.Realized (quickClassifier future) := by
    apply initialMemo_spec _ (fun _ _ h => quickClassifier_congr future h) rank
      (hm future (hx.trans hf) hvf)
    rw [← TagProgram.evalSeparate_predicateOnly _ (initialMemo_predicateOnly rank f memo)
      (cacheClassifier future.tags)]
    exact hr future hf hvf
  exact ⟨(hresult last (.refl _) hv).1, fun future hf hvf => (hresult future hf hvf).2, hv, hx⟩

theorem rowMemo_quick (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (s : QuickCache ap) (hs : s.Valid) (memo : RemainderCache ap) (hm : memo.Realizes s)
    (he : (rowMemo rank a r memo).execQuick rank highFirst fuel started s =
      some (some (edge, out), last)) :
    edge.denote = (rowTagged (quickClassifier last) a r).denote ∧
      out.Realizes last ∧ last.Valid ∧ s.Extends last := by
  obtain ⟨hv, hx, hr⟩ := TagProgram.execQuick_spec rank highFirst fuel started _ s hs he
  have hresult (future : QuickCache ap) (hf : last.Extends future) (hvf : future.Valid) :
      edge.denote = (rowTagged (quickClassifier future) a r).denote ∧
        out.Realized (quickClassifier future) := by
    apply rowMemo_spec _ (fun _ _ h => quickClassifier_congr future h) rank
      (hm future (hx.trans hf) hvf)
    rw [← TagProgram.evalSeparate_predicateOnly _ (rowMemo_predicateOnly rank a r memo)
      (cacheClassifier future.tags)]
    exact hr future hf hvf
  exact ⟨(hresult last (.refl _) hv).1, fun future hf hvf => (hresult future hf hvf).2, hv, hx⟩

theorem transitionMemo_quick (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (s : QuickCache ap) (hs : s.Valid) (memo : RemainderCache ap) (hm : memo.Realizes s)
    (v : Letter (Fin ap)) (state : State ap)
    (he : (transitionMemo rank v state memo).execQuick rank highFirst fuel started s =
      some (some (edge, out), last)) :
    edge.denote = (transitionTagged (quickClassifier last) v state).denote ∧
      out.Realizes last ∧ last.Valid ∧ s.Extends last :=
  rowMemo_quick rank highFirst fuel started s hs memo hm he

end Tlsf.Dpa.Impl
