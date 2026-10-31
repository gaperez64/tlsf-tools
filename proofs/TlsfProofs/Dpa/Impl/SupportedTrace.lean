import TlsfProofs.Dpa.Impl.RefinedConverse

/-!
# Supported Shannon traversal compiled to tag programs

The traversal order is `src/lib/dpa_formula.c:664`: constants, mapped-cache
hit, supported top variable, low child, high child, then cache the ITE.
The REDUCE atom program below uses predicate instructions. `exec` supplies
the exact-query reference path; `execQuick` in `QuickTrace.lean` supplies
C's cached predicates. Persistent remainder memoization is separate.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

def TagProgram.bind (p : TagProgram ap α) (k : α → TagProgram ap β) : TagProgram ap β :=
  match p with
  | .done a => k a
  | .query f cont => .query f (fun b => (cont b).bind k)
  | .test f mask cont => .test f mask (fun b => (cont b).bind k)

theorem TagProgram.eval_bind (tags : TagClassifier ap) (p : TagProgram ap α)
    (k : α → TagProgram ap β) : (p.bind k).eval tags = (k (p.eval tags)).eval tags := by
  induction p with
  | done _ => rfl
  | query f cont ih => exact ih (tags f)
  | test f mask cont ih => exact ih (mask.any (tags f))

abbrev MappedCache (ap : Nat) := List (Formula (Fin ap) × Formula (Fin ap))

def MappedCache.Valid (p : Formula (Fin ap) → Prop) (memo : MappedCache ap) : Prop :=
  ∀ e, e ∈ memo → Class.ofFormula e.2 = replaceTrue p (Class.ofFormula e.1)

def lookupMapped (f : Formula (Fin ap)) : MappedCache ap → Option (Formula (Fin ap))
  | [] => none
  | (g, r) :: rest => if equivalent g f then some r else lookupMapped f rest

theorem lookupMapped_spec (memo : MappedCache ap) (hm : MappedCache.Valid p memo)
    (he : lookupMapped f memo = some r) :
    Class.ofFormula r = replaceTrue p (Class.ofFormula f) := by
  induction memo with
  | nil => simp [lookupMapped] at he
  | cons e memo ih =>
    rcases e with ⟨g, s⟩
    simp only [lookupMapped] at he
    split at he
    · rename_i hg
      cases Option.some.inj he
      rw [hm (g, r) (by simp), (equivalent_exact _ _).mp hg]
    · exact ih (fun e hh => hm e (by simp [hh])) he

def mappedIte (v high low : Formula (Fin ap)) : Formula (Fin ap) :=
  .disj (.conj v high) (.conj (.neg v) low)

/-- A failed/incomplete alphabet remains explicit. Each successful branch
uses only essential variables; equivalent subgraphs reuse the mapped cache.
The atom program runs before the low child, and low before high, as in C. -/
def mapSupported (atomProgram : Formula (Fin ap) → TagProgram ap (Formula (Fin ap))) :
    List (Formula (Fin ap)) → Formula (Fin ap) → MappedCache ap →
      TagProgram ap (Option (Formula (Fin ap) × MappedCache ap))
  | atoms, f, memo =>
    if equivalent f .ff then .done (some (.ff, memo))
    else if equivalent f .tt then .done (some (.tt, memo))
    else match lookupMapped f memo with
    | some r => .done (some (r, memo))
    | none => match atoms with
      | [] => .done none
      | a :: atoms =>
        if uses f a then
          (atomProgram a).bind fun v =>
            (mapSupported atomProgram atoms (cofactor a false f) memo).bind fun low =>
              match low with
              | none => .done none
              | some (low, memo) =>
                (mapSupported atomProgram atoms (cofactor a true f) memo).bind fun high =>
                  match high with
                  | none => .done none
                  | some (high, memo) =>
                    let r := mappedIte v high low
                    .done (some (r, (f, r) :: memo))
        else mapSupported atomProgram atoms f memo

theorem mappedIte_substitution (p : Formula (Fin ap) → Prop)
    (hf : Uses (Class.ofFormula f) a)
    (hv : Class.ofFormula v = replaceTrue p (Class.ofFormula a))
    (hh : Class.ofFormula high = replaceTrue p (Class.ofFormula (cofactor a true f)))
    (hl : Class.ofFormula low = replaceTrue p (Class.ofFormula (cofactor a false f))) :
    Class.ofFormula (mappedIte v high low) = replaceTrue p (Class.ofFormula f) := by
  have hm := uses_in_bound (fun σ τ h => propEval_local f σ τ h) hf
  rw [← cofactor_shannon f a hm]
  apply Class.ext
  intro σ
  have hev := congrArg (fun x : Class ap => x σ) hv
  have heh := congrArg (fun x : Class ap => x σ) hh
  have hel := congrArg (fun x : Class ap => x σ) hl
  change propEval σ v = _ at hev
  change propEval σ high = _ at heh
  change propEval σ low = _ at hel
  change (propEval σ v && propEval σ high || !propEval σ v && propEval σ low) = _
  rw [hev, heh, hel]
  rfl

theorem mapSupported_spec (atomProgram : Formula (Fin ap) → TagProgram ap (Formula (Fin ap)))
    (tags : TagClassifier ap) (p : Formula (Fin ap) → Prop)
    (hv : ∀ f a, Uses (Class.ofFormula f) a →
      Class.ofFormula ((atomProgram a).eval tags) = replaceTrue p (Class.ofFormula a))
    (atoms : List (Formula (Fin ap))) (f : Formula (Fin ap)) (memo : MappedCache ap)
    (hm : MappedCache.Valid p memo)
    (he : (mapSupported atomProgram atoms f memo).eval tags = some (r, out)) :
    Class.ofFormula r = replaceTrue p (Class.ofFormula f) ∧ MappedCache.Valid p out := by
  induction atoms generalizing f memo r out with
  | nil =>
    simp only [mapSupported] at he
    split at he
    · rename_i hf
      cases Option.some.inj he
      rw [(equivalent_exact _ _).mp hf]
      exact ⟨rfl, hm⟩
    · split at he
      · rename_i hf
        cases Option.some.inj he
        rw [(equivalent_exact _ _).mp hf]
        exact ⟨rfl, hm⟩
      · cases hc : lookupMapped f memo with
        | none => simp [hc, TagProgram.eval] at he
        | some s =>
          simp only [hc, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨lookupMapped_spec memo hm hc, hm⟩
  | cons a atoms ih =>
    simp only [mapSupported] at he
    split at he
    · rename_i hf
      cases Option.some.inj he
      rw [(equivalent_exact _ _).mp hf]
      exact ⟨rfl, hm⟩
    · split at he
      · rename_i hf
        cases Option.some.inj he
        rw [(equivalent_exact _ _).mp hf]
        exact ⟨rfl, hm⟩
      · cases hc : lookupMapped f memo with
        | some s =>
          simp only [hc, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨lookupMapped_spec memo hm hc, hm⟩
        | none =>
          simp only [hc] at he
          split at he
          · rename_i hu
            simp only [TagProgram.eval_bind] at he
            cases hl : (mapSupported atomProgram atoms (cofactor a false f) memo).eval tags with
            | none => simp [hl, TagProgram.eval] at he
            | some lo =>
              rcases lo with ⟨low, ml⟩
              simp only [hl, TagProgram.eval_bind] at he
              obtain ⟨hlow, hml⟩ := ih _ _ hm hl
              cases hh : (mapSupported atomProgram atoms (cofactor a true f) ml).eval tags with
              | none => simp [hh, TagProgram.eval] at he
              | some hi =>
                rcases hi with ⟨high, mh⟩
                simp only [hh, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                obtain ⟨hhigh, hmh⟩ := ih _ _ hml hh
                have hr := mappedIte_substitution p ((uses_exact _ _).mp hu) (hv f a ((uses_exact _ _).mp hu)) hhigh hlow
                refine ⟨hr, ?_⟩
                intro e he
                rcases List.mem_cons.mp he with he | he
                · exact he ▸ hr
                · exact hmh e he
          · exact ih _ _ hm he

theorem mappedCofactor_dependsOn (a : Formula (Fin ap)) (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (value : Bool) (hd : (Class.ofFormula f).DependsOn (a :: atoms)) :
    (Class.ofFormula (cofactor a value f)).DependsOn atoms := by
  intro σ τ h
  change propEval σ (cofactor a value f) = propEval τ (cofactor a value f)
  rw [cofactor_eval, cofactor_eval]
  apply hd
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [setAtom]
  · by_cases he : b = a <;> simp [setAtom, he, h b hb]

theorem mappedSkip_dependsOn (a : Formula (Fin ap)) (atoms : List (Formula (Fin ap)))
    (f : Formula (Fin ap)) (hd : (Class.ofFormula f).DependsOn (a :: atoms))
    (hu : uses f a = false) : (Class.ofFormula f).DependsOn atoms := by
  intro σ τ h
  apply support_locality
  intro b hb
  rcases List.mem_cons.mp (uses_in_bound hd hb) with rfl | hm
  · have he := (uses_exact f b).mpr hb
    simp [hu] at he
  · exact h b hm

/-- A complete alphabet suffices, in any order and with arbitrary memo
contents. Incomplete alphabets cannot silently return an arbitrary map. -/
theorem mapSupported_success (atomProgram : Formula (Fin ap) → TagProgram ap (Formula (Fin ap)))
    (tags : TagClassifier ap) (atoms : List (Formula (Fin ap))) (f : Formula (Fin ap))
    (memo : MappedCache ap) (hd : (Class.ofFormula f).DependsOn atoms) :
    ∃ r out, (mapSupported atomProgram atoms f memo).eval tags = some (r, out) := by
  induction atoms generalizing f memo with
  | nil =>
    have he (σ : Assignment ap) : propEval σ f = propEval (fun _ => false) f :=
      hd σ (fun _ => false) (by simp)
    have hc : equivalent f .ff = true ∨ equivalent f .tt = true := by
      cases hv : propEval (fun _ => false) f
      · exact Or.inl ((equivalent_exact _ _).mpr (Class.ext (fun σ => (he σ).trans hv)))
      · exact Or.inr ((equivalent_exact _ _).mpr (Class.ext (fun σ => (he σ).trans hv)))
    rcases hc with hf | ht
    · exact ⟨.ff, memo, by simp [mapSupported, hf, TagProgram.eval]⟩
    · by_cases hf : equivalent f .ff = true
      · exact ⟨.ff, memo, by simp [mapSupported, hf, TagProgram.eval]⟩
      · exact ⟨.tt, memo, by simp [mapSupported, hf, ht, TagProgram.eval]⟩
  | cons a atoms ih =>
    by_cases hf : equivalent f .ff = true
    · exact ⟨.ff, memo, by simp [mapSupported, hf, TagProgram.eval]⟩
    by_cases ht : equivalent f .tt = true
    · exact ⟨.tt, memo, by simp [mapSupported, hf, ht, TagProgram.eval]⟩
    cases hm : lookupMapped f memo with
    | some r => exact ⟨r, memo, by simp [mapSupported, hf, ht, hm, TagProgram.eval]⟩
    | none =>
      cases hu : uses f a
      · obtain ⟨r, out, hr⟩ := ih f memo (mappedSkip_dependsOn a atoms f hd hu)
        exact ⟨r, out, by simp [mapSupported, hf, ht, hm, hu, hr]⟩
      · obtain ⟨low, ml, hl⟩ := ih (cofactor a false f) memo (mappedCofactor_dependsOn a atoms f false hd)
        obtain ⟨high, mh, hh⟩ := ih (cofactor a true f) ml (mappedCofactor_dependsOn a atoms f true hd)
        exact ⟨mappedIte ((atomProgram a).eval tags) high low,
          (f, mappedIte ((atomProgram a).eval tags) high low) :: mh,
          by simp [mapSupported, hf, ht, hm, hu, TagProgram.eval_bind, hl, hh, TagProgram.eval]⟩

def reduceAtomProgram (a : Formula (Fin ap)) : TagProgram ap (Formula (Fin ap)) :=
  if isAPb a then .done a
  else .test a [.cosafety] (fun yes => .done (if yes then a else .tt))

theorem reduceAtomProgram_eval (tags : TagClassifier ap) (f a : Formula (Fin ap))
    (hu : Uses (Class.ofFormula f) a) :
    Class.ofFormula ((reduceAtomProgram a).eval tags) =
      replaceTrue (fun b => (!isAPb b && !tags b .cosafety) = true) (Class.ofFormula a) := by
  apply Class.ext
  intro σ
  change propEval σ ((reduceAtomProgram a).eval tags) = propEval _ a
  rw [propEval_used_atom hu]
  by_cases ha : isAPb a = true
  · simp only [reduceAtomProgram, ha, ↓reduceIte, TagProgram.eval,
      Bool.not_true, Bool.false_and, Bool.false_eq_true]
    exact propEval_used_atom hu σ
  · simp only [reduceAtomProgram, ha, Bool.false_eq_true, ↓reduceIte, TagProgram.eval]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    cases tags a .cosafety <;> simp [propEval, propEval_used_atom hu]

def reduceSupported (atoms : List (Formula (Fin ap))) (f : Formula (Fin ap)) :=
  mapSupported reduceAtomProgram atoms f []

theorem reduceSupported_spec (tags : TagClassifier ap) (atoms : List (Formula (Fin ap)))
    (he : (reduceSupported atoms f).eval tags = some (r, out)) :
    Class.ofFormula r = Class.ofFormula (reduceTagged tags f) := by
  have hm : MappedCache.Valid (fun b => (!isAPb b && !tags b .cosafety) = true) ([] : MappedCache ap) := by
    intro e he; contradiction
  rw [reduceTagged, replace_exact]
  exact (mapSupported_spec reduceAtomProgram tags _ (reduceAtomProgram_eval tags) atoms f [] hm he).1

theorem reduceSupported_default (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (atoms : List (Formula (Fin ap))) (s : TagCache ap) (hs : s.Valid)
    (he : (reduceSupported atoms f).exec (defaultTags rank highFirst fuel started) s =
      some (some (r, out), last)) :
    (cacheClassifier last).Sound ∧ (cacheClassifier last).Lower ∧
      Class.ofFormula r = Class.ofFormula (reduceTagged (cacheClassifier last) f) := by
  obtain ⟨hsound, hlower, hr⟩ := TagProgram.default_realizes rank highFirst fuel started
    (reduceSupported atoms f) s hs he
  exact ⟨hsound, hlower, reduceSupported_spec _ atoms hr⟩

/-- Each new substitution epoch has a fresh mapped cache. The shared tag
cache is threaded by `TagProgram.exec`, independently of this cache. -/
def extractSupported (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    TagProgram ap (Option (Formula (Fin ap))) :=
  (reduceSupported (orderAtoms rank (modalAtoms f).eraseDups) f).bind fun result =>
    .done (result.map (fun (r, _) => unfoldSyntax (elide r)))

theorem extractSupported_spec (tags : TagClassifier ap) (rank : Formula (Fin ap) → Nat)
    (he : (extractSupported rank f).eval tags = some r) :
    Class.ofFormula r = Class.ofFormula (extractPassTagged tags f) := by
  simp only [extractSupported, TagProgram.eval_bind, TagProgram.eval] at he
  cases hm : (reduceSupported (orderAtoms rank (modalAtoms f).eraseDups) f).eval tags with
  | none => simp [hm] at he
  | some result =>
    rcases result with ⟨s, out⟩
    simp only [hm, Option.map_some, Option.some.injEq] at he
    subst r
    rw [← U_ofFormula, elide_exact, reduceSupported_spec tags _ hm]
    rw [extractPassTagged, ← U_ofFormula, elide_exact]

theorem extractSupported_success (tags : TagClassifier ap) (rank : Formula (Fin ap) → Nat)
    (f : Formula (Fin ap)) : ∃ r, (extractSupported rank f).eval tags = some r := by
  have hd : (Class.ofFormula f).DependsOn (orderAtoms rank (modalAtoms f).eraseDups) := by
    intro σ τ h
    exact propEval_local f σ τ (fun a ha => h a ((orderAtoms_mem rank _ a).mpr (by simp [ha])))
  obtain ⟨r, out, hr⟩ := mapSupported_success reduceAtomProgram tags _ f [] hd
  exact ⟨unfoldSyntax (elide r), by simp only [extractSupported, reduceSupported,
    TagProgram.eval_bind, hr, Option.map_some, TagProgram.eval]⟩

def TagClassifier.Congruent (tags : TagClassifier ap) : Prop :=
  ∀ f g, Class.ofFormula f = Class.ofFormula g → tags f = tags g

/-- The retry path, including the finite query on the unfolded
retry whose result cannot cause another retry by unfolding idempotence. -/
def rhoSupported (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    TagProgram ap (Option (Formula (Fin ap))) :=
  (extractSupported rank f).bind fun first => match first with
    | none => .done none
    | some r => .test r [.finite] fun yes =>
      if yes && !equivalent f (unfoldSyntax f) then
        (extractSupported rank (unfoldSyntax f)).bind fun second => match second with
          | none => .done none
          | some s => .test s [.finite] (fun _ => .done (some s))
      else .done (some r)

theorem rhoSupported_spec (tags : TagClassifier ap) (hc : tags.Congruent)
    (rank : Formula (Fin ap) → Nat) (he : (rhoSupported rank f).eval tags = some r) :
    Class.ofFormula r = Class.ofFormula (rhoTagged tags f) := by
  simp only [rhoSupported, TagProgram.eval_bind] at he
  cases hf : (extractSupported rank f).eval tags with
  | none => simp [hf, TagProgram.eval] at he
  | some first =>
    simp only [hf, TagProgram.eval, List.any_cons, List.any_nil, Bool.or_false] at he
    have hfirst := extractSupported_spec tags rank hf
    rw [hc _ _ hfirst] at he
    simp only [rhoTagged]
    split at he
    · rename_i ht
      simp only [ht, ↓reduceIte]
      cases hs : (extractSupported rank (unfoldSyntax f)).eval tags with
      | none => simp [hs, TagProgram.eval_bind, TagProgram.eval] at he
      | some second =>
        simp only [TagProgram.eval_bind, hs, TagProgram.eval, Option.some.injEq] at he
        subst r
        exact extractSupported_spec tags rank hs
    · rename_i ht
      simp only [ht, TagProgram.eval, Option.some.injEq] at he ⊢
      subst r
      exact hfirst

theorem rhoSupported_success (tags : TagClassifier ap) (rank : Formula (Fin ap) → Nat)
    (f : Formula (Fin ap)) : ∃ r, (rhoSupported rank f).eval tags = some r := by
  obtain ⟨first, hf⟩ := extractSupported_success tags rank f
  by_cases ht : (tags first .finite && !(equivalent f (unfoldSyntax f))) = true
  · obtain ⟨second, hs⟩ := extractSupported_success tags rank (unfoldSyntax f)
    exact ⟨second, by simp only [rhoSupported, TagProgram.eval_bind, hf, TagProgram.eval,
      List.any_cons, List.any_nil, Bool.or_false,
      ht, ↓reduceIte, hs]⟩
  · exact ⟨first, by simp only [rhoSupported, TagProgram.eval_bind, hf, TagProgram.eval,
      List.any_cons, List.any_nil, Bool.or_false,
      ht, Bool.false_eq_true, ↓reduceIte]⟩

theorem rhoSupported_default (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (s : TagCache ap) (hs : s.Valid)
    (he : (rhoSupported rank f).exec (defaultTags rank highFirst fuel started) s =
      some (some r, last)) :
    (cacheClassifier last).Sound ∧ (cacheClassifier last).Lower ∧
      Class.ofFormula r = Class.ofFormula (rhoTagged (cacheClassifier last) f) := by
  obtain ⟨hsound, hlower, hr⟩ := TagProgram.default_realizes rank highFirst fuel started
    (rhoSupported rank f) s hs he
  exact ⟨hsound, hlower, rhoSupported_spec _ (fun _ _ h => cacheClassifier_congr last h) rank hr⟩

/-- Exact calls visible to the query interpreter, excluding internal operand
queries of `defaultTags`. Used by offline traversal diagnostics. -/
def TagProgram.reads (tags : TagClassifier ap) : TagProgram ap α → List (Formula (Fin ap))
  | .done _ => []
  | .query f cont => f :: (cont (tags f)).reads tags
  | .test f mask cont => f :: (cont (mask.any (tags f))).reads tags

end Tlsf.Dpa.Impl
