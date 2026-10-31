import TlsfProofs.Dpa.Impl.RefinedComponent

/-!
# Shared default-tag query traces

The cache cells are those of `src/lib/dpa_formula.c:81`. A completed query
remains readable throughout a phase, even when later queries recursively
populate both caches. Startup (`src/lib/dpa.c:510`) starts a new phase.
The query-program interpreter below uses the actual `defaultTags` definition;
its realization theorem supplies one sound classifier for an entire trace.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

theorem lookupClassTags_congr (h : Class.ofFormula f = Class.ofFormula g)
    (es : FragmentCache ap) : lookupClassTags f es = lookupClassTags g es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he : equivalent e.1 f = equivalent e.1 g := by
      apply Bool.eq_iff_iff.mpr
      simp only [equivalent_exact, h]
    simp only [lookupClassTags, he, ih]

/-- Preservation of already computed cells, rather than just their soundness.
No consistency premise about absent cells or cache-entry uniqueness is used. -/
def TagCache.Extends (s t : TagCache ap) : Prop :=
  (∀ a b, lookupAtomTags a s.atoms = some b → lookupAtomTags a t.atoms = some b) ∧
  (∀ f b, lookupClassTags f s.classes = some b → lookupClassTags f t.classes = some b)

theorem TagCache.Extends.refl (s : TagCache ap) : s.Extends s :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem TagCache.Extends.trans {s t u : TagCache ap}
    (h : s.Extends t) (h' : t.Extends u) : s.Extends u :=
  ⟨fun a b hb => h'.1 a b (h.1 a b hb), fun f b hb => h'.2 f b (h.2 f b hb)⟩

theorem TagCache.Extends.rememberAtom {s t : TagCache ap} (h : s.Extends t)
    (ha : lookupAtomTags a s.atoms = none) : s.Extends (t.rememberAtom a b) := by
  refine ⟨?_, h.2⟩
  intro g bits hg
  have hne : a ≠ g := by intro he; subst g; rw [ha] at hg; contradiction
  simpa only [TagCache.rememberAtom, lookupAtomTags, hne, ↓reduceIte] using h.1 g bits hg

theorem TagCache.Extends.rememberClass {s t : TagCache ap} (h : s.Extends t)
    (hf : lookupClassTags f s.classes = none) : s.Extends (t.rememberClass f b) := by
  refine ⟨h.1, ?_⟩
  intro g bits hg
  have hne : equivalent f g = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    rw [lookupClassTags_congr ((equivalent_exact _ _).mp he), hg] at hf
    contradiction
  simpa only [TagCache.rememberClass, lookupClassTags, hne, Bool.false_eq_true, ↓reduceIte]
    using h.2 g bits hg

def TagComputation.Preserves (q : TagComputation ap) : Prop :=
  ∀ f s b s', q f s = some (b, s') → s.Extends s'

theorem defaultAtomTags_preserves (q : TagComputation ap) (hq : q.Preserves)
    (started : Bool) (a : Formula (Fin ap)) (s : TagCache ap)
    (he : defaultAtomTags q started a s = some (b, s')) : s.Extends s' := by
  unfold defaultAtomTags at he
  cases hc : lookupAtomTags a s.atoms with
  | some bits =>
    simp only [hc, pure] at he
    cases Option.some.inj he
    exact .refl _
  | none =>
    simp only [hc] at he
    split at he
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
      obtain ⟨⟨left, sl⟩, hl, ⟨right, sr⟩, hr, he⟩ := he
      have hsl := hq _ _ _ _ hl
      have hsr : sl.Extends sr := by
        unfold tagRight at hr
        split at hr
        · exact hq _ _ _ _ hr
        · cases Option.some.inj hr; exact .refl _
      cases he
      exact (hsl.trans hsr).rememberAtom hc
    · cases Option.some.inj he; exact .refl _

theorem tagChildren_preserves (q : TagComputation ap) (hq : q.Preserves)
    (highFirst : Bool) (a f : Formula (Fin ap)) (s : TagCache ap)
    (he : tagChildren q highFirst a f s = some (low, high, s')) : s.Extends s' := by
  unfold tagChildren at he
  split at he
  all_goals
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨⟨first, sf⟩, hf, ⟨second, ss⟩, hs, he⟩ := he
    cases he
    exact (hq _ _ _ _ hf).trans (hq _ _ _ _ hs)

theorem defaultTags_preserves (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool) :
    (defaultTags rank highFirst fuel started : TagComputation ap).Preserves := by
  induction fuel with
  | zero => intro f s b s' he; simp [defaultTags] at he
  | succ fuel ih =>
    intro f s b s' he
    simp only [defaultTags] at he
    split at he
    · cases Option.some.inj he; exact .refl _
    · cases hc : lookupClassTags f s.classes with
      | some bits =>
        simp only [hc, pure] at he
        cases Option.some.inj he; exact .refl _
      | none =>
        simp only [hc] at he
        cases ht : (orderAtoms rank (modalAtoms f).eraseDups).find? (uses f) with
        | none => simp [ht] at he
        | some a =>
          simp only [ht, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
          obtain ⟨⟨atom, sa⟩, ha, ⟨low, high, sc⟩, hh, he⟩ := he
          cases he
          exact ((defaultAtomTags_preserves _ ih started a s ha).trans
            (tagChildren_preserves _ ih (highFirst f) a f sa hh)).rememberClass hc

/-- Untouched cells use the structural lower bound. Constants precede cache
lookup, just as in C; arbitrary unreachable constant cache cells are harmless. -/
def cacheClassifier (s : TagCache ap) : TagClassifier ap := fun f =>
  if equivalent f .ff || equivalent f .tt then allFragmentBits
  else (lookupClassTags f s.classes).getD (classBits f)

theorem cacheClassifier_spec (s : TagCache ap) (hs : s.Valid) (f : Formula (Fin ap)) :
    ClassTagSpec f (cacheClassifier s f) := by
  unfold cacheClassifier
  split
  · rename_i hc
    rcases Bool.or_eq_true_iff.mp hc with hc | hc
    · exact (constantClass_spec false).congr ((equivalent_exact _ _).mp hc).symm
    · exact (constantClass_spec true).congr ((equivalent_exact _ _).mp hc).symm
  · cases hc : lookupClassTags f s.classes with
    | none => exact classBits_spec f
    | some b => exact lookupClassTags_spec hs hc

theorem cacheClassifier_sound (s : TagCache ap) (hs : s.Valid) :
    (cacheClassifier s).Sound := fun f => (cacheClassifier_spec s hs f).2

theorem cacheClassifier_lower (s : TagCache ap) (hs : s.Valid) (f : Formula (Fin ap)) :
    BitsBelow (classBits f) (cacheClassifier s f) := (cacheClassifier_spec s hs f).1

theorem cacheClassifier_congr (s : TagCache ap)
    (he : Class.ofFormula f = Class.ofFormula g) : cacheClassifier s f = cacheClassifier s g := by
  have hc (c : Formula (Fin ap)) : equivalent f c = equivalent g c := by
    apply Bool.eq_iff_iff.mpr
    simp only [equivalent_exact, he]
  have hb : classBits f = classBits g := by
    funext t
    apply Bool.eq_iff_iff.mpr
    simp only [classBits, classTag_exact, he]
  simp only [cacheClassifier, hc, lookupClassTags_congr he, hb]

/-- Successful queries, including a cache hit or a constant, are realized by
the cache classifier at return and in every subsequent extension. -/
theorem defaultTags_read (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (he : defaultTags rank highFirst fuel started f s = some (b, s'))
    (hx : s'.Extends t) : cacheClassifier t f = b := by
  cases fuel with
  | zero => simp [defaultTags] at he
  | succ fuel =>
    simp only [defaultTags] at he
    unfold cacheClassifier
    split at he
    · rename_i hc
      cases Option.some.inj he
      simp only [hc, ↓reduceIte]
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      cases hl : lookupClassTags f s.classes with
      | some bits =>
        simp only [hl, pure] at he
        cases Option.some.inj he
        simp only [hx.2 f b hl, Option.getD_some]
      | none =>
        simp only [hl] at he
        cases ht : (orderAtoms rank (modalAtoms f).eraseDups).find? (uses f) with
        | none => simp [ht] at he
        | some a =>
          simp only [ht, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
          obtain ⟨⟨atom, sa⟩, _, ⟨low, high, sc⟩, _, he⟩ := he
          cases he
          have hh : lookupClassTags f (sc.rememberClass f
              (bitsMeet atom (bitsMeet low high))).classes =
              some (bitsMeet atom (bitsMeet low high)) := by
            simp only [TagCache.rememberClass, lookupClassTags,
              (equivalent_exact f f).mpr rfl, ↓reduceIte]
          simp only [hx.2 _ _ hh, Option.getD_some]

/-- Finite dependent query programs. Continuations can choose later queries
from earlier answers, so this includes finite retry and ordered table guards. -/
inductive TagProgram (ap : Nat) (α : Type) where
  | done (value : α)
  | query (f : Formula (Fin ap)) (next : FragmentBits → TagProgram ap α)
  | test (f : Formula (Fin ap)) (mask : List FragmentTag) (next : Bool → TagProgram ap α)

def TagProgram.eval (tags : TagClassifier ap) : TagProgram ap α → α
  | .done a => a
  | .query f k => (k (tags f)).eval tags
  | .test f mask k => (k (mask.any (tags f))).eval tags

def TagProgram.exec (q : TagComputation ap) : TagProgram ap α → TagCache ap →
    Option (α × TagCache ap)
  | .done a, s => some (a, s)
  | .query f k, s => do
    let (b, s) ← q f s
    (k b).exec q s
  | .test f mask k, s => do
    let (b, s) ← q f s
    (k (mask.any b)).exec q s

/-- Every successful shared-cache trace has one classifier that realizes all
its reads, not just unrelated witnesses for individual positive answers. -/
theorem TagProgram.default_exec (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (p : TagProgram ap α) (s : TagCache ap) (hs : s.Valid)
    (he : p.exec (defaultTags rank highFirst fuel started) s = some (a, s')) :
    s'.Valid ∧ s.Extends s' ∧ ∀ t, s'.Extends t → p.eval (cacheClassifier t) = a := by
  induction p generalizing s with
  | done value =>
    cases Option.some.inj he
    exact ⟨hs, .refl _, fun _ _ => rfl⟩
  | query f k ih =>
    simp only [exec, bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨b, sb⟩, hb, he⟩ := he
    have hv := (defaultTags_sound rank highFirst fuel started f s b sb hs hb).1
    obtain ⟨hv', hx, hr⟩ := ih b sb hv he
    refine ⟨hv', (defaultTags_preserves rank highFirst fuel started f s b sb hb).trans hx, ?_⟩
    intro t ht
    simp only [eval, defaultTags_read rank highFirst fuel started hb (hx.trans ht)]
    exact hr t ht
  | test f mask k ih =>
    simp only [exec, bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨b, sb⟩, hb, he⟩ := he
    have hv := (defaultTags_sound rank highFirst fuel started f s b sb hs hb).1
    obtain ⟨hv', hx, hr⟩ := ih (mask.any b) sb hv he
    refine ⟨hv', (defaultTags_preserves rank highFirst fuel started f s b sb hb).trans hx, ?_⟩
    intro t ht
    simp only [eval, defaultTags_read rank highFirst fuel started hb (hx.trans ht)]
    exact hr t ht

theorem TagProgram.default_realizes (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (p : TagProgram ap α) (s : TagCache ap) (hs : s.Valid)
    (he : p.exec (defaultTags rank highFirst fuel started) s = some (a, s')) :
    (cacheClassifier s').Sound ∧
      (∀ f, BitsBelow (classBits f) (cacheClassifier s' f)) ∧
      p.eval (cacheClassifier s') = a := by
  obtain ⟨hv, _, hr⟩ := p.default_exec rank highFirst fuel started s hs he
  exact ⟨cacheClassifier_sound s' hv, cacheClassifier_lower s' hv, hr s' (.refl _)⟩

/-- A persistent sequence of post-start traces. The pre-start trace executes
once before the class reset; exact atom cells survive it. Failure remains
explicit and does not turn a failed query into a successful trace. -/
def defaultTrace (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) : Nat → Option (TagCache ap)
  | 0 => do
    let (_, pre) ← before.exec (defaultTags rank highFirst fuel false) s
    let (_, post) ← (programs 0).exec (defaultTags rank highFirst fuel true) pre.start
    pure post
  | n+1 => do
    let prev ← defaultTrace rank highFirst fuel before programs s n
    let (_, post) ← (programs (n+1)).exec (defaultTags rank highFirst fuel true) prev
    pure post

theorem defaultTrace_valid (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) (hs : s.Valid) (n : Nat)
    (he : defaultTrace rank highFirst fuel before programs s n = some t) : t.Valid := by
  induction n generalizing t with
  | zero =>
    simp only [defaultTrace, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨⟨_, pre⟩, hp, ⟨_, post⟩, ht, he⟩ := he
    subst t
    have hv := (before.default_exec rank highFirst fuel false s hs hp).1
    exact ((programs 0).default_exec rank highFirst fuel true pre.start
      (TagCache.start_valid hv) ht).1
  | succ n ih =>
    simp only [defaultTrace, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨prev, hp, ⟨_, post⟩, ht, he⟩ := he
    subst t
    exact ((programs (n+1)).default_exec rank highFirst fuel true prev (ih hp) ht).1

/-- Failure fallback is explicit here solely to give a total classifier
stream to `runTagged`; language claims about successful C executions must
additionally identify their programs and returned component states. -/
def defaultTraceClassifier (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) (n : Nat) : TagClassifier ap :=
  match defaultTrace rank highFirst fuel before programs s n with
  | none => classBits
  | some t => cacheClassifier t

theorem defaultTraceClassifier_spec (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) (hs : s.Valid) (n : Nat) :
    (defaultTraceClassifier rank highFirst fuel before programs s n).Sound ∧
      ∀ f, BitsBelow (classBits f)
        (defaultTraceClassifier rank highFirst fuel before programs s n f) := by
  unfold defaultTraceClassifier
  cases he : defaultTrace rank highFirst fuel before programs s n with
  | none => exact ⟨classBits_sound, fun _ _ h => h⟩
  | some t =>
    have hv := defaultTrace_valid rank highFirst fuel before programs s hs n he
    exact ⟨cacheClassifier_sound t hv, cacheClassifier_lower t hv⟩

/-- All-field language equality with the classifier hypotheses discharged
by the actual shared default-tag traces, including C's startup class reset.
This is not an accepting-run theorem or a compiler for C's query traversal. -/
theorem defaultTrace_all_language (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat)
    (before : TagProgram ap Unit) (programs : Nat → TagProgram ap Unit)
    (s : TagCache ap) (hs : s.Valid) (hn : NNF f) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (runTagged (defaultTraceClassifier rank highFirst fuel before programs s) f w n).all n ↔
      Sat none w f 0 :=
  runTagged_all_language _
    (fun k => (defaultTraceClassifier_spec rank highFirst fuel before programs s hs k).1) hn w n

end Tlsf.Dpa.Impl
