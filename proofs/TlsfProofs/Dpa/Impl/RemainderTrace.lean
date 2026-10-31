import TlsfProofs.Dpa.Impl.QuickTrace

/-!
# Persistent remainder programs

`rhoMemo` follows `src/lib/dpa_formula.c:938`, including the initial memo
lookup and the recursive lookup on the unfolded retry. No query executes on
a hit. The memo survives the startup reset of class tags.

The invariant below is independent of later classifier changes. It proves
an unfolded co-safety obligation implied by the source, including old memo
hits. It does not assert equality with a newly recomputed `rhoTagged`.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}

theorem extractPassTagged_congr (tags : TagClassifier ap)
    (he : Class.ofFormula f = Class.ofFormula g) :
    Class.ofFormula (extractPassTagged tags f) = Class.ofFormula (extractPassTagged tags g) := by
  simp only [extractPassTagged, ← U_ofFormula, elide_exact, reduceTagged, replace_exact, he]

theorem rhoTagged_congr (tags : TagClassifier ap) (hc : tags.Congruent)
    (he : Class.ofFormula f = Class.ofFormula g) :
    Class.ofFormula (rhoTagged tags f) = Class.ofFormula (rhoTagged tags g) := by
  have hpass := extractPassTagged_congr tags he
  have heq : equivalent f (unfoldSyntax f) = equivalent g (unfoldSyntax g) := by
    apply Bool.eq_iff_iff.mpr
    simp only [equivalent_exact, ← U_ofFormula, he]
  simp only [rhoTagged, hc _ _ hpass, heq]
  split
  · exact extractPassTagged_congr tags (by simp only [← U_ofFormula, he])
  · exact hpass

/-- A permanent semantic certificate, expressed on classes because a
Shannon/ITE representative need not itself have NNF syntax. -/
def RemainderCertificate (f r : Formula (Fin ap)) : Prop :=
  NNFClass (Class.ofFormula r) ∧ U (Class.ofFormula r) = Class.ofFormula r ∧
  RefinedClass .cosafety r ∧ (U (Class.ofFormula f) ⇒ₚ Class.ofFormula r)

theorem RemainderCertificate.congr
    (hf : Class.ofFormula f = Class.ofFormula g) (hr : Class.ofFormula r = Class.ofFormula s)
    (h : RemainderCertificate f r) : RemainderCertificate g s := by
  simpa only [RemainderCertificate, RefinedClass, hf, hr] using h

theorem extractSupported_certificate (tags : TagClassifier ap) (hs : tags.Sound)
    (rank : Formula (Fin ap) → Nat) (hn : NNFClass (Class.ofFormula f))
    (he : (extractSupported rank f).eval tags = some r) : RemainderCertificate f r := by
  obtain ⟨g, hgn, hge⟩ := hn
  have hclass := (extractSupported_spec tags rank he).trans (extractPassTagged_congr tags hge.symm)
  have hv : RemainderCertificate g (extractPassTagged tags g) :=
    ⟨⟨_, extractPassTagged_nnf tags hgn, rfl⟩, extractPassTagged_unfolded tags g,
      extractPassTagged_refined tags hs g, extractPassTagged_weakens tags hgn⟩
  exact hv.congr hge hclass.symm

abbrev RemainderCache (ap : Nat) := List (Formula (Fin ap) × Formula (Fin ap))

def RemainderCache.Valid (memo : RemainderCache ap) : Prop :=
  ∀ e, e ∈ memo → RemainderCertificate e.1 e.2

theorem RemainderCache.empty_valid : RemainderCache.Valid ([] : RemainderCache ap) :=
  fun _ h => by simp at h

theorem RemainderCache.remember_valid (memo : RemainderCache ap) (hm : memo.Valid)
    (hr : RemainderCertificate f r) : RemainderCache.Valid ((f, r) :: memo) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hr
  · exact hm e he

theorem lookupRemainder_certificate (memo : RemainderCache ap) (hm : memo.Valid)
    (he : lookupMapped f memo = some r) : RemainderCertificate f r := by
  induction memo with
  | nil => simp [lookupMapped] at he
  | cons e memo ih =>
    rcases e with ⟨g, s⟩
    simp only [lookupMapped] at he
    split at he
    · rename_i hg
      cases Option.some.inj he
      exact (hm (g, r) (by simp)).congr ((equivalent_exact _ _).mp hg) rfl
    · exact ih (fun e hh => hm e (by simp [hh])) he

/-- The recursive call's unfolded source cannot retry again. It must still
perform its finite predicate, unless its persistent memo lookup hits. -/
def rhoUnfoldedMemo (rank : Formula (Fin ap) → Nat) (g : Formula (Fin ap))
    (memo : RemainderCache ap) : TagProgram ap (Option (Formula (Fin ap) × RemainderCache ap)) :=
  match lookupMapped g memo with
  | some r => .done (some (r, memo))
  | none => (extractSupported rank g).bind fun result => match result with
    | none => .done none
    | some r => .test r [.finite] fun _ => .done (some (r, (g, r) :: memo))

def rhoMemo (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (memo : RemainderCache ap) : TagProgram ap (Option (Formula (Fin ap) × RemainderCache ap)) :=
  match lookupMapped f memo with
  | some r => .done (some (r, memo))
  | none => (extractSupported rank f).bind fun result => match result with
    | none => .done none
    | some r => .test r [.finite] fun yes =>
      if yes && !equivalent f (unfoldSyntax f) then
        (rhoUnfoldedMemo rank (unfoldSyntax f) memo).bind fun result =>
          .done (result.map (fun (s, out) => (s, (f, s) :: out)))
      else .done (some (r, (f, r) :: memo))

theorem rhoUnfoldedMemo_predicateOnly (rank : Formula (Fin ap) → Nat) (g : Formula (Fin ap))
    (memo : RemainderCache ap) : (rhoUnfoldedMemo rank g memo).PredicateOnly := by
  simp only [rhoUnfoldedMemo]
  split
  · trivial
  · apply TagProgram.PredicateOnly.bind _ (extractSupported_predicateOnly rank g)
    intro result
    cases result with
    | none => trivial
    | some r => exact fun _ => trivial

theorem rhoMemo_predicateOnly (rank : Formula (Fin ap) → Nat) (f : Formula (Fin ap))
    (memo : RemainderCache ap) : (rhoMemo rank f memo).PredicateOnly := by
  simp only [rhoMemo]
  split
  · trivial
  · apply TagProgram.PredicateOnly.bind _ (extractSupported_predicateOnly rank f)
    intro result
    cases result with
    | none => trivial
    | some r =>
      intro yes
      dsimp only
      split
      · apply TagProgram.PredicateOnly.bind _ (rhoUnfoldedMemo_predicateOnly rank _ memo)
        intro _; trivial
      · trivial

theorem rhoUnfoldedMemo_certificate (tags : TagClassifier ap) (hs : tags.Sound)
    (rank : Formula (Fin ap) → Nat) (hn : NNFClass (Class.ofFormula g))
    (hm : memo.Valid) (he : (rhoUnfoldedMemo rank g memo).eval tags = some (r, out)) :
    RemainderCertificate g r ∧ out.Valid := by
  simp only [rhoUnfoldedMemo] at he
  cases hc : lookupMapped g memo with
  | some s =>
    simp only [hc, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨lookupRemainder_certificate _ hm hc, hm⟩
  | none =>
    simp only [hc, TagProgram.eval_bind] at he
    cases hf : (extractSupported rank g).eval tags with
    | none => simp [hf, TagProgram.eval] at he
    | some s =>
      simp only [hf, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hv := extractSupported_certificate tags hs rank hn hf
      exact ⟨hv, RemainderCache.remember_valid _ hm hv⟩

theorem rhoMemo_certificate (tags : TagClassifier ap) (hs : tags.Sound)
    (rank : Formula (Fin ap) → Nat) (hn : NNFClass (Class.ofFormula f))
    (hm : memo.Valid) (he : (rhoMemo rank f memo).eval tags = some (r, out)) :
    RemainderCertificate f r ∧ out.Valid := by
  simp only [rhoMemo] at he
  cases hc : lookupMapped f memo with
  | some s =>
    simp only [hc, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨lookupRemainder_certificate _ hm hc, hm⟩
  | none =>
    simp only [hc, TagProgram.eval_bind] at he
    cases hf : (extractSupported rank f).eval tags with
    | none => simp [hf, TagProgram.eval] at he
    | some s =>
      simp only [hf, TagProgram.eval] at he
      split at he
      · simp only [TagProgram.eval_bind, TagProgram.eval] at he
        cases hr : (rhoUnfoldedMemo rank (unfoldSyntax f) memo).eval tags with
        | none => simp [hr] at he
        | some result =>
          rcases result with ⟨result, mout⟩
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hnu : NNFClass (Class.ofFormula (unfoldSyntax f)) := by
            rw [← U_ofFormula]
            exact U_nnfClass hn
          obtain ⟨hv, hmv⟩ := rhoUnfoldedMemo_certificate tags hs rank hnu hm hr
          have hv' : RemainderCertificate f result := by
            refine ⟨hv.1, hv.2.1, hv.2.2.1, ?_⟩
            simpa only [← U_ofFormula, U_idempotent] using hv.2.2.2
          exact ⟨hv', RemainderCache.remember_valid _ hmv hv'⟩
      · simp only [TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hv := extractSupported_certificate tags hs rank hn hf
        exact ⟨hv, RemainderCache.remember_valid _ hm hv⟩

/-- Each actual quick-cache execution preserves the permanent remainder
certificates, without assuming that old results equal a fresh extraction. -/
theorem rhoMemo_quick_certificate (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (s : QuickCache ap) (hs : s.Valid) (hn : NNFClass (Class.ofFormula f))
    (memo : RemainderCache ap) (hm : memo.Valid)
    (he : (rhoMemo rank f memo).execQuick rank highFirst fuel started s =
      some (some (r, out), last)) :
    RemainderCertificate f r ∧ out.Valid ∧ last.Valid ∧ s.Extends last := by
  obtain ⟨hv, hx, _⟩ := TagProgram.execQuick_spec rank highFirst fuel started _ s hs he
  obtain ⟨hsound, _, hr⟩ := TagProgram.quick_realizes rank highFirst fuel started
    _ (rhoMemo_predicateOnly rank f memo) s hs he
  obtain ⟨hcert, hmout⟩ := rhoMemo_certificate _ hsound rank hn hm hr
  exact ⟨hcert, hmout, hv, hx⟩

/-- Equality under a particular classifier is stronger than the permanent
certificate. It is used only where the trace invariant establishes it. -/
def RemainderCache.Realized (tags : TagClassifier ap) (memo : RemainderCache ap) : Prop :=
  ∀ e, e ∈ memo → Class.ofFormula e.2 = Class.ofFormula (rhoTagged tags e.1)

theorem lookupRemainder_realized (tags : TagClassifier ap) (hc : tags.Congruent)
    (memo : RemainderCache ap) (hm : memo.Realized tags)
    (he : lookupMapped f memo = some r) :
    Class.ofFormula r = Class.ofFormula (rhoTagged tags f) := by
  induction memo with
  | nil => simp [lookupMapped] at he
  | cons e memo ih =>
    rcases e with ⟨g, s⟩
    simp only [lookupMapped] at he
    split at he
    · rename_i hg
      cases Option.some.inj he
      exact (hm (g, r) (by simp)).trans (rhoTagged_congr tags hc ((equivalent_exact _ _).mp hg))
    · exact ih (fun e hh => hm e (by simp [hh])) he

theorem RemainderCache.Realized.remember (hm : RemainderCache.Realized tags memo)
    (hr : Class.ofFormula r = Class.ofFormula (rhoTagged tags f)) :
    RemainderCache.Realized tags ((f, r) :: memo) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hr
  · exact hm e he

theorem rhoTagged_of_unfolded (tags : TagClassifier ap)
    (hu : U (Class.ofFormula g) = Class.ofFormula g) : rhoTagged tags g = extractPassTagged tags g := by
  have he : equivalent g (unfoldSyntax g) = true := (equivalent_exact _ _).mpr (by
    rw [← U_ofFormula, hu])
  simp only [rhoTagged, he, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem rhoUnfoldedMemo_spec (tags : TagClassifier ap) (hc : tags.Congruent)
    (rank : Formula (Fin ap) → Nat) (hu : U (Class.ofFormula g) = Class.ofFormula g)
    (hm : memo.Realized tags) (he : (rhoUnfoldedMemo rank g memo).eval tags = some (r, out)) :
    Class.ofFormula r = Class.ofFormula (rhoTagged tags g) ∧ out.Realized tags := by
  simp only [rhoUnfoldedMemo] at he
  cases hlookup : lookupMapped g memo with
  | some s =>
    simp only [hlookup, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨lookupRemainder_realized tags hc _ hm hlookup, hm⟩
  | none =>
    simp only [hlookup, TagProgram.eval_bind] at he
    cases hf : (extractSupported rank g).eval tags with
    | none => simp [hf, TagProgram.eval] at he
    | some s =>
      simp only [hf, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hv : Class.ofFormula s = Class.ofFormula (rhoTagged tags g) := by
        rw [rhoTagged_of_unfolded tags hu]
        exact extractSupported_spec tags rank hf
      exact ⟨hv, hm.remember hv⟩

theorem rhoMemo_spec (tags : TagClassifier ap) (hc : tags.Congruent)
    (rank : Formula (Fin ap) → Nat) (hm : memo.Realized tags)
    (he : (rhoMemo rank f memo).eval tags = some (r, out)) :
    Class.ofFormula r = Class.ofFormula (rhoTagged tags f) ∧ out.Realized tags := by
  simp only [rhoMemo] at he
  cases hlookup : lookupMapped f memo with
  | some s =>
    simp only [hlookup, TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨lookupRemainder_realized tags hc _ hm hlookup, hm⟩
  | none =>
    simp only [hlookup, TagProgram.eval_bind] at he
    cases hf : (extractSupported rank f).eval tags with
    | none => simp [hf, TagProgram.eval] at he
    | some s =>
      simp only [hf, TagProgram.eval, List.any_cons, List.any_nil, Bool.or_false] at he
      have hpass := extractSupported_spec tags rank hf
      rw [hc _ _ hpass] at he
      split at he
      · rename_i hretry
        simp only [TagProgram.eval_bind, TagProgram.eval] at he
        cases hr : (rhoUnfoldedMemo rank (unfoldSyntax f) memo).eval tags with
        | none => simp [hr] at he
        | some result =>
          rcases result with ⟨result, mout⟩
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hv, hmv⟩ := rhoUnfoldedMemo_spec tags hc rank
            (by simp only [← U_ofFormula, U_idempotent]) hm hr
          have hv' : Class.ofFormula result = Class.ofFormula (rhoTagged tags f) := by
            simp only [rhoTagged, hretry, ↓reduceIte]
            rw [rhoTagged_of_unfolded tags (by simp only [← U_ofFormula, U_idempotent])] at hv
            exact hv
          exact ⟨hv', hmv.remember hv'⟩
      · rename_i hretry
        simp only [TagProgram.eval, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hv : Class.ofFormula s = Class.ofFormula (rhoTagged tags f) := by
          simpa only [rhoTagged, hretry, Bool.false_eq_true, ↓reduceIte] using hpass
        exact ⟨hv, hm.remember hv⟩

/-- A memo populated by earlier queries remains realized by every future
extension of both caches in the same phase. Startup is not an extension:
it clears exact class cells and needs a separate retention argument. -/
def RemainderCache.Realizes (s : QuickCache ap) (memo : RemainderCache ap) : Prop :=
  ∀ last, s.Extends last → last.Valid → memo.Realized (quickClassifier last)

theorem RemainderCache.empty_realizes (s : QuickCache ap) :
    RemainderCache.Realizes s ([] : RemainderCache ap) := fun _ _ _ _ h => by simp at h

theorem rhoMemo_quick (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (s : QuickCache ap) (hs : s.Valid) (memo : RemainderCache ap) (hm : memo.Realizes s)
    (he : (rhoMemo rank f memo).execQuick rank highFirst fuel started s =
      some (some (r, out), last)) :
    Class.ofFormula r = Class.ofFormula (rhoTagged (quickClassifier last) f) ∧
      out.Realizes last ∧ last.Valid ∧ s.Extends last := by
  obtain ⟨hv, hx, hr⟩ := TagProgram.execQuick_spec rank highFirst fuel started _ s hs he
  have hresult (future : QuickCache ap) (hfuture : last.Extends future) (hvfuture : future.Valid) :
      Class.ofFormula r = Class.ofFormula (rhoTagged (quickClassifier future) f) ∧
        out.Realized (quickClassifier future) := by
    apply rhoMemo_spec _ (fun _ _ h => quickClassifier_congr future h) rank
      (hm future (hx.trans hfuture) hvfuture)
    rw [← TagProgram.evalSeparate_predicateOnly _ (rhoMemo_predicateOnly rank f memo)
      (cacheClassifier future.tags)]
    exact hr future hfuture hvfuture
  exact ⟨(hresult last (.refl _) hv).1, fun future hf hvf => (hresult future hf hvf).2, hv, hx⟩

end Tlsf.Dpa.Impl
