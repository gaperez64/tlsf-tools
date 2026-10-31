import TlsfProofs.Dpa.Impl.Selection

/-!
# Default recursive tags and their phase-independent cache invariant

The operand calls and transfers are `src/lib/dpa_formula.c:81`; materialization
is `:366`. Atom keys retain frozen syntax; class keys use Boolean equality.
An absent atom cell means its initial structural tags, with exact_tags false.
Class cache hits precede refinement, including after started changes. The
reference uses the supplied atom-ID order and Boolean cofactors in place of
the reduced BDD. Either evaluation order of the two C child calls is allowed.

`RefinedAtom` describes the actual frozen atom and its materialized operands.
It is deliberately distinct from structural `fragmentSyntax`. Proving that
the component/extractor language theorems support these recursive predicates
is a further obligation; no structural component theorem is invoked here.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

abbrev FragmentBits := TagBits FragmentTag

def allFragmentBits : FragmentBits := fun _ => true

def structuralBits (a : Formula (Fin ap)) : FragmentBits := fun t => syntaxTag t a

def classBits (f : Formula (Fin ap)) : FragmentBits := fun t => classTag t f

def tagLhs : Formula α → Formula α
  | .next f | .eventually f | .globally f | .until f _ | .release f _
  | .weakUntil f _ | .strongRelease f _ => f
  | _ => .tt

def tagRhs : Formula α → Formula α
  | .until _ g | .release _ g | .weakUntil _ g | .strongRelease _ g => g
  | _ => .tt

def tagBinary : Formula α → Bool
  | .until _ _ | .release _ _ | .weakUntil _ _ | .strongRelease _ _ => true
  | _ => false

def tagRefinable : Formula α → Bool
  | .next _ | .eventually _ | .globally _ | .until _ _ | .release _ _
  | .weakUntil _ _ | .strongRelease _ _ => true
  | _ => false

def eventualBits (b : FragmentBits) : FragmentBits
  | .cosafety | .pi2 => b .cosafety
  | .sigma2 => b .sigma2
  | _ => false

def globalBits (b : FragmentBits) : FragmentBits
  | .safety | .sigma2 => b .safety
  | .pi2 => b .pi2
  | _ => false

def transferBits (a : Formula α) (left right : FragmentBits) : FragmentBits :=
  match a with
  | .next _ => left
  | .eventually _ => eventualBits left
  | .globally _ => globalBits left
  | .until _ _ | .strongRelease _ _ => eventualBits (bitsMeet left right)
  | .release _ _ | .weakUntil _ _ => globalBits (bitsMeet left right)
  | _ => fun _ => false

theorem transferBits_mono (a : Formula α) (hl : BitsBelow l l')
    (hr : BitsBelow r r') : BitsBelow (transferBits a l r) (transferBits a l' r') := by
  intro t ht
  cases a <;> cases t <;>
    simp only [transferBits, eventualBits, globalBits, bitsMeet, Bool.and_eq_true] at ht ⊢
  all_goals first | contradiction | exact hl _ ht |
    exact ⟨hl _ ht.1, hr _ ht.2⟩

theorem transferBits_structural (a : Formula (Fin ap)) (ha : tagRefinable a = true) :
    transferBits a (structuralBits (tagLhs a)) (structuralBits (tagRhs a)) =
      structuralBits a := by
  funext t
  cases a <;> cases t <;>
    simp_all [tagRefinable, transferBits, structuralBits, syntaxTag, tagLhs,
      tagRhs, eventualBits, globalBits, bitsMeet, finiteb, safetyb, cosafetyb,
      pi2b, sigma2b]

/-- Recursive canonical justification on the frozen syntax, not a claim
that that syntax has a structural tag or equals a different frozen atom. -/
inductive RefinedAtom : FragmentTag → Formula (Fin ap) → Prop where
  | structural (h : fragmentSyntax t a) : RefinedAtom t a
  | materialized (left right : FragmentBits)
      (hl : ∀ u, left u = true → HasTag (RefinedAtom u) (Class.ofFormula (tagLhs a)))
      (hr : ∀ u, right u = true → HasTag (RefinedAtom u) (Class.ofFormula (tagRhs a)))
      (ht : transferBits a left right t = true) : RefinedAtom t a

def RefinedClass (t : FragmentTag) (f : Formula (Fin ap)) : Prop :=
  HasTag (RefinedAtom t) (Class.ofFormula f)

theorem refined_structural_lower (f : Formula (Fin ap)) (t : FragmentTag)
    (h : classTag t f = true) : RefinedClass t f := by
  intro a ha
  exact .structural ((classTag_exact t f).mp h a ha)

theorem RefinedAtom.operator_upper (h : RefinedAtom t a) : operatorTagUpper t a := by
  cases h with
  | structural h => exact syntax_operator_upper a t h
  | materialized l r _ _ ht =>
    cases a <;> cases t <;>
      simp_all [transferBits, eventualBits, globalBits, operatorTagUpper]

def AtomTagSpec (a : Formula (Fin ap)) (b : FragmentBits) : Prop :=
  BitsBelow (structuralBits a) b ∧ ∀ t, b t = true → RefinedAtom t a

def ClassTagSpec (f : Formula (Fin ap)) (b : FragmentBits) : Prop :=
  BitsBelow (classBits f) b ∧ ∀ t, b t = true → RefinedClass t f

theorem structuralBits_spec (a : Formula (Fin ap)) : AtomTagSpec a (structuralBits a) :=
  ⟨fun _ h => h, fun t h => .structural ((syntaxTag_exact t a).mp h)⟩

theorem classBits_spec (f : Formula (Fin ap)) : ClassTagSpec f (classBits f) :=
  ⟨fun _ h => h, refined_structural_lower f⟩

theorem ClassTagSpec.congr (he : Class.ofFormula f = Class.ofFormula g)
    (h : ClassTagSpec f b) : ClassTagSpec g b := by
  have hc (t : FragmentTag) : classTag t f = classTag t g := by
    apply Bool.eq_iff_iff.mpr
    simp only [classTag_exact, he]
  exact ⟨fun t ht => h.1 t (by simpa only [classBits, hc t] using ht), fun t ht => by
    simpa only [RefinedClass, he] using h.2 t ht⟩

abbrev FragmentCache (ap : Nat) := List (Formula (Fin ap) × FragmentBits)

structure TagCache (ap : Nat) where
  atoms : FragmentCache ap := []
  classes : FragmentCache ap := []

def TagCache.Valid (s : TagCache ap) : Prop :=
  (∀ e, e ∈ s.atoms → AtomTagSpec e.1 e.2) ∧
  (∀ e, e ∈ s.classes → ClassTagSpec e.1 e.2)

theorem TagCache.empty_valid : ({} : TagCache ap).Valid := by
  constructor <;> intro e he <;> simp at he

def lookupAtomTags (a : Formula (Fin ap)) : FragmentCache ap → Option FragmentBits
  | [] => none
  | (f, b) :: rest => if f = a then some b else lookupAtomTags a rest

def lookupClassTags (f : Formula (Fin ap)) : FragmentCache ap → Option FragmentBits
  | [] => none
  | (g, b) :: rest => if equivalent g f then some b else lookupClassTags f rest

theorem lookupAtomTags_spec {s : TagCache ap} (hs : s.Valid) (he : lookupAtomTags a s.atoms = some b) :
    AtomTagSpec a b := by
  have h := hs.1
  generalize s.atoms = es at h he
  induction es with
  | nil => simp [lookupAtomTags] at he
  | cons e es ih =>
    rcases e with ⟨f, bits⟩
    simp only [lookupAtomTags] at he
    split at he
    · rename_i hf
      cases Option.some.inj he
      subst f
      exact h (a, b) (by simp)
    · exact ih (fun e hm => h e (by simp [hm])) he

theorem lookupClassTags_spec {s : TagCache ap} (hs : s.Valid) (he : lookupClassTags f s.classes = some b) :
    ClassTagSpec f b := by
  have h := hs.2
  generalize s.classes = es at h he
  induction es with
  | nil => simp [lookupClassTags] at he
  | cons e es ih =>
    rcases e with ⟨g, bits⟩
    simp only [lookupClassTags] at he
    split at he
    · rename_i hf
      cases Option.some.inj he
      exact (h (g, b) (by simp)).congr ((equivalent_exact _ _).mp hf)
    · exact ih (fun e hm => h e (by simp [hm])) he

def TagCache.rememberAtom (s : TagCache ap) (a : Formula (Fin ap)) (b : FragmentBits) :
    TagCache ap := { s with atoms := (a, b) :: s.atoms }

def TagCache.rememberClass (s : TagCache ap) (f : Formula (Fin ap)) (b : FragmentBits) :
    TagCache ap := { s with classes := (f, b) :: s.classes }

theorem TagCache.rememberAtom_valid {s : TagCache ap} (hs : s.Valid) (hb : AtomTagSpec a b) :
    (s.rememberAtom a b).Valid := by
  refine ⟨?_, hs.2⟩
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hb
  · exact hs.1 e he

theorem TagCache.rememberClass_valid {s : TagCache ap} (hs : s.Valid) (hb : ClassTagSpec f b) :
    (s.rememberClass f b).Valid := by
  refine ⟨hs.1, ?_⟩
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hb
  · exact hs.2 e he

abbrev TagComputation (ap : Nat) :=
  Formula (Fin ap) → TagCache ap → Option (FragmentBits × TagCache ap)

def TagComputation.Sound (recurse : TagComputation ap) : Prop :=
  ∀ f s b s', s.Valid → recurse f s = some (b, s') → s'.Valid ∧ ClassTagSpec f b

def tagRight (recurse : TagComputation ap) (a : Formula (Fin ap)) (s : TagCache ap) :
    Option (FragmentBits × TagCache ap) :=
  if tagBinary a then recurse (tagRhs a) s else some (allFragmentBits, s)

def defaultAtomTags (recurse : TagComputation ap) (started : Bool)
    (a : Formula (Fin ap)) (s : TagCache ap) : Option (FragmentBits × TagCache ap) := do
  match lookupAtomTags a s.atoms with
  | some b => pure (b, s)
  | none =>
    let initial := structuralBits a
    if tagRefinable a && (started || !(initial .safety || initial .cosafety)) then
      let (left, s) ← recurse (tagLhs a) s
      let (right, s) ← tagRight recurse a s
      let b := transferBits a left right
      pure (b, s.rememberAtom a b)
    else pure (initial, s)

private theorem trueClass_spec : ClassTagSpec (.tt : Formula (Fin ap)) allFragmentBits := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro t _ a ha
  have h := uses_in_bound (fun σ τ hh => propEval_local (.tt : Formula (Fin ap)) σ τ hh) ha
  simp [modalAtoms] at h

theorem defaultAtomTags_sound (recurse : TagComputation ap) (hr : recurse.Sound)
    (started : Bool) (a : Formula (Fin ap)) (s : TagCache ap) (hs : s.Valid)
    (he : defaultAtomTags recurse started a s = some (b, s')) :
    s'.Valid ∧ AtomTagSpec a b := by
  unfold defaultAtomTags at he
  cases hc : lookupAtomTags a s.atoms with
  | some bits =>
    simp only [hc, pure] at he
    cases Option.some.inj he
    exact ⟨hs, lookupAtomTags_spec hs hc⟩
  | none =>
    simp only [hc] at he
    split at he
    · rename_i hguard
      have hcan := (Bool.and_eq_true_iff.mp hguard).1
      cases hl : recurse (tagLhs a) s with
      | none => simp [hl] at he
      | some l =>
        rcases l with ⟨left, sl⟩
        obtain ⟨hsl, hleft⟩ := hr _ _ _ _ hs hl
        have hright : ∀ right sr,
            tagRight recurse a sl = some (right, sr) →
            sr.Valid ∧ ClassTagSpec (tagRhs a) right := by
          intro right sr h
          unfold tagRight at h
          split at h
          · exact hr _ _ _ _ hsl h
          · rename_i hn
            cases Option.some.inj h
            have heq : tagRhs a = .tt := by
              cases a <;> simp_all [tagBinary, tagRhs]
            exact ⟨hsl, heq ▸ trueClass_spec⟩
        simp only [hl] at he
        change ((tagRight recurse a sl).bind (fun r =>
          some (transferBits a left r.1, r.2.rememberAtom a (transferBits a left r.1)))) =
          some (b, s') at he
        generalize tagRight recurse a sl = rr at he hright
        cases rr with
        | none => simp at he
        | some r =>
          rcases r with ⟨right, sr⟩
          obtain ⟨hsr, hright⟩ := hright _ _ rfl
          change some (transferBits a left right, sr.rememberAtom a
            (transferBits a left right)) = some (b, s') at he
          cases Option.some.inj he
          have hb : AtomTagSpec a (transferBits a left right) := by
            refine ⟨?_, fun t ht => .materialized left right hleft.2 hright.2 ht⟩
            have hlo : BitsBelow (structuralBits (tagLhs a)) left := fun t ht =>
              hleft.1 t ((classTag_exact t _).mpr
                (syntax_tag_lower _ t ((syntaxTag_exact t _).mp ht)))
            have hro : BitsBelow (structuralBits (tagRhs a)) right := fun t ht =>
              hright.1 t ((classTag_exact t _).mpr
                (syntax_tag_lower _ t ((syntaxTag_exact t _).mp ht)))
            rw [← transferBits_structural a hcan]
            exact transferBits_mono a hlo hro
          exact ⟨TagCache.rememberAtom_valid hsr hb, hb⟩
    · cases Option.some.inj he
      exact ⟨hs, structuralBits_spec a⟩

theorem constantClass_spec (value : Bool) :
    ClassTagSpec (if value then .tt else .ff : Formula (Fin ap)) allFragmentBits := by
  cases value
  · refine ⟨fun _ _ => rfl, ?_⟩
    intro t _ a ha
    have h := uses_in_bound (fun σ τ hh => propEval_local (.ff : Formula (Fin ap)) σ τ hh) ha
    simp [modalAtoms] at h
  · exact trueClass_spec

def tagChildren (recurse : TagComputation ap) (highFirst : Bool)
    (a f : Formula (Fin ap)) (s : TagCache ap) :
    Option (FragmentBits × FragmentBits × TagCache ap) :=
  if highFirst then do
    let (high, s) ← recurse (cofactor a true f) s
    let (low, s) ← recurse (cofactor a false f) s
    pure (low, high, s)
  else do
    let (low, s) ← recurse (cofactor a false f) s
    let (high, s) ← recurse (cofactor a true f) s
    pure (low, high, s)

theorem tagChildren_sound (recurse : TagComputation ap) (hr : recurse.Sound)
    (highFirst : Bool) (a f : Formula (Fin ap)) (s : TagCache ap) (hs : s.Valid)
    (he : tagChildren recurse highFirst a f s = some (low, high, s')) :
    s'.Valid ∧ ClassTagSpec (cofactor a false f) low ∧
      ClassTagSpec (cofactor a true f) high := by
  unfold tagChildren at he
  split at he
  all_goals
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨⟨first, sf⟩, hf, ⟨second, ss⟩, hs', he⟩ := he
    obtain ⟨hsf, hfirst⟩ := hr _ _ _ _ hs hf
    obtain ⟨hss, hsecond⟩ := hr _ _ _ _ hsf hs'
    cases he
  · exact ⟨hss, hsecond, hfirst⟩
  · exact ⟨hss, hfirst, hsecond⟩

theorem shannonTagSpec (a f : Formula (Fin ap)) (ha : Uses (Class.ofFormula f) a)
    (hatom : AtomTagSpec a atom) (hlow : ClassTagSpec (cofactor a false f) low)
    (hhigh : ClassTagSpec (cofactor a true f) high) :
    ClassTagSpec f (bitsMeet atom (bitsMeet low high)) := by
  have hsplit (tag : Formula (Fin ap) → Prop) :=
    tags_shannon_intersection (tag := tag) (low := Class.ofFormula (cofactor a false f))
      (high := Class.ofFormula (cofactor a true f)) ha
      (cofactor_eval a f false) (cofactor_eval a f true)
  constructor
  · intro t ht
    obtain ⟨hta, htl, hth⟩ := (hsplit (fragmentSyntax t)).mp ((classTag_exact t f).mp ht)
    exact Bool.and_eq_true_iff.mpr ⟨hatom.1 t ((syntaxTag_exact t a).mpr hta),
      Bool.and_eq_true_iff.mpr
        ⟨hlow.1 t ((classTag_exact t _).mpr htl), hhigh.1 t ((classTag_exact t _).mpr hth)⟩⟩
  · intro t ht
    obtain ⟨hta, hrest⟩ := Bool.and_eq_true_iff.mp ht
    obtain ⟨htl, hth⟩ := Bool.and_eq_true_iff.mp hrest
    exact (hsplit (RefinedAtom t)).mpr
      ⟨hatom.2 t hta, hlow.2 t htl, hhigh.2 t hth⟩

def defaultTags (rank : Formula (Fin ap) → Nat) (highFirst : Formula (Fin ap) → Bool) :
    Nat → Bool → TagComputation ap
  | 0, _, _, _ => none
  | fuel + 1, started, f, s => do
    if equivalent f .ff || equivalent f .tt then pure (allFragmentBits, s)
    else match lookupClassTags f s.classes with
    | some b => pure (b, s)
    | none =>
      match (orderAtoms rank (modalAtoms f).eraseDups).find? (uses f) with
      | none => none
      | some a => do
        let (atom, s) ← defaultAtomTags (defaultTags rank highFirst fuel started) started a s
        let (low, high, s) ← tagChildren (defaultTags rank highFirst fuel started)
          (highFirst f) a f s
        let b := bitsMeet atom (bitsMeet low high)
        pure (b, s.rememberClass f b)

theorem defaultTags_sound (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool) :
    (defaultTags rank highFirst fuel started : TagComputation ap).Sound := by
  induction fuel with
  | zero => intro f s b s' _ he; simp [defaultTags] at he
  | succ fuel ih =>
    intro f s b s' hs he
    simp only [defaultTags] at he
    split at he
    · rename_i hc
      cases Option.some.inj he
      refine ⟨hs, ?_⟩
      rcases Bool.or_eq_true_iff.mp hc with hc | hc
      · exact (constantClass_spec false).congr ((equivalent_exact _ _).mp hc).symm
      · exact (constantClass_spec true).congr ((equivalent_exact _ _).mp hc).symm
    · cases hc : lookupClassTags f s.classes with
      | some bits =>
        simp only [hc, pure] at he
        cases Option.some.inj he
        exact ⟨hs, lookupClassTags_spec hs hc⟩
      | none =>
        simp only [hc] at he
        cases ht : (orderAtoms rank (modalAtoms f).eraseDups).find? (uses f) with
        | none => simp [ht] at he
        | some a =>
          simp only [ht, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
          obtain ⟨⟨atom, sa⟩, ha, ⟨low, high, sc⟩, hh, he⟩ := he
          obtain ⟨hsa, hatom⟩ := defaultAtomTags_sound _ ih started a s hs ha
          obtain ⟨hsc, hlow, hhigh⟩ := tagChildren_sound _ ih (highFirst f) a f sa hsa hh
          cases he
          have hb := shannonTagSpec a f ((uses_exact f a).mp (List.find?_some ht))
            hatom hlow hhigh
          exact ⟨TagCache.rememberClass_valid hsc hb, hb⟩

/-- In particular, a cache produced before start is valid for a later call
after start; no invalidation or stronger post-start exactness is assumed. -/
theorem defaultTags_phase_change (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel fuel' : Nat) (f g : Formula (Fin ap))
    (s : TagCache ap) (hs : s.Valid)
    (hbefore : defaultTags rank highFirst fuel false f s = some (b, s'))
    (hafter : defaultTags rank highFirst fuel' true g s' = some (b', s'')) :
    s''.Valid ∧ ClassTagSpec f b ∧ ClassTagSpec g b' := by
  obtain ⟨hs', hf⟩ := defaultTags_sound rank highFirst fuel false f s b s' hs hbefore
  obtain ⟨hs'', hg⟩ := defaultTags_sound rank highFirst fuel' true g s' b' s'' hs' hafter
  exact ⟨hs'', hf, hg⟩

def operatorBits (a : Formula α) : FragmentBits :=
  match a with
  | .eventually _ | .until _ _ | .strongRelease _ _ => fun t =>
      match t with | .finite | .safety => false | _ => true
  | .globally _ | .release _ _ | .weakUntil _ _ => fun t =>
      match t with | .finite | .cosafety => false | _ => true
  | _ => allFragmentBits

theorem operatorBits_exact (a : Formula α) (t : FragmentTag) :
    operatorBits a t = true ↔ operatorTagUpper t a := by
  cases a <;> cases t <;> simp [operatorBits, operatorTagUpper, allFragmentBits]

structure TagBounds where
  low : FragmentBits
  high : FragmentBits

/-- Unlike exact cached results, bounds are one-sided. This invariant is
independent of the current atom-cache contents and of the started flag. -/
def TagBounds.Valid (f : Formula (Fin ap)) (b : TagBounds) : Prop :=
  (∀ t, b.low t = true → RefinedClass t f) ∧
  (∀ t, RefinedClass t f → b.high t = true)

def atomLower (s : TagCache ap) (a : Formula (Fin ap)) : FragmentBits :=
  (lookupAtomTags a s.atoms).getD (structuralBits a)

theorem atomLower_spec (s : TagCache ap) (hs : s.Valid) (a : Formula (Fin ap)) :
    AtomTagSpec a (atomLower s a) := by
  unfold atomLower
  cases he : lookupAtomTags a s.atoms with
  | none => exact structuralBits_spec a
  | some bits => exact lookupAtomTags_spec hs he

/-- The denotation of `tag_bounds`, `src/lib/dpa_formula.c:127`. Folding
support has the same three-way Shannon intersection, including constants. -/
def freshTagBounds (s : TagCache ap) (f : Formula (Fin ap)) : TagBounds :=
  ⟨fun t => hasTag (fun a => atomLower s a t) f,
    fun t => hasTag (fun a => operatorBits a t) f⟩

theorem freshTagBounds_valid (s : TagCache ap) (hs : s.Valid) (f : Formula (Fin ap)) :
    (freshTagBounds s f).Valid f := by
  constructor
  · intro t ht a ha
    exact (atomLower_spec s hs a).2 t ((hasTag_exact _ f).mp ht a ha)
  · intro t ht
    exact (hasTag_exact _ f).mpr (fun a ha =>
      (operatorBits_exact a t).mpr ((ht a ha).operator_upper))

theorem TagBounds.Valid.congr {b : TagBounds} (he : Class.ofFormula f = Class.ofFormula g)
    (hb : b.Valid f) : b.Valid g := by
  simpa only [TagBounds.Valid, RefinedClass, he] using hb

abbrev TagBoundsCache (ap : Nat) := List (Formula (Fin ap) × TagBounds)

def TagBoundsCache.Valid (cache : TagBoundsCache ap) : Prop :=
  ∀ e, e ∈ cache → e.2.Valid e.1

def lookupTagBounds (f : Formula (Fin ap)) : TagBoundsCache ap → Option TagBounds
  | [] => none
  | (g, b) :: rest => if equivalent g f then some b else lookupTagBounds f rest

theorem lookupTagBounds_valid (cache : TagBoundsCache ap) (hc : cache.Valid)
    (he : lookupTagBounds f cache = some b) : b.Valid f := by
  induction cache with
  | nil => simp [lookupTagBounds] at he
  | cons e cache ih =>
    rcases e with ⟨g, bits⟩
    simp only [lookupTagBounds] at he
    split at he
    · rename_i hf
      cases Option.some.inj he
      exact (hc (g, b) (by simp)).congr ((equivalent_exact _ _).mp hf)
    · exact ih (fun e hm => hc e (by simp [hm])) he

def cachedTagBounds (s : TagCache ap) (f : Formula (Fin ap)) (cache : TagBoundsCache ap) :
    TagBounds × TagBoundsCache ap :=
  match lookupTagBounds f cache with
  | some b => (b, cache)
  | none => let b := freshTagBounds s f; (b, (f, b) :: cache)

theorem cachedTagBounds_valid (s : TagCache ap) (hs : s.Valid) (f : Formula (Fin ap))
    (cache : TagBoundsCache ap) (hc : cache.Valid) :
    let r := cachedTagBounds s f cache
    r.1.Valid f ∧ r.2.Valid := by
  unfold cachedTagBounds
  cases he : lookupTagBounds f cache with
  | some bits => exact ⟨lookupTagBounds_valid cache hc he, hc⟩
  | none =>
    refine ⟨freshTagBounds_valid s hs f, ?_⟩
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact freshTagBounds_valid s hs f
    · exact hc e hm

/-- Any lower-bound hit is justified, and any upper-bound miss excludes
every refined tag in the requested mask. An undecided mask still requires
the exact recursive call, whose positive answers use defaultTags_sound. -/
theorem TagBounds.Valid.mask {b : TagBounds} (hb : b.Valid f) (mask : List FragmentTag) :
    (mask.any b.low = true → ∃ t, t ∈ mask ∧ RefinedClass t f) ∧
    (mask.any b.high = false → ∀ t, t ∈ mask → ¬RefinedClass t f) := by
  constructor
  · intro h
    obtain ⟨t, hm, ht⟩ := List.any_eq_true.mp h
    exact ⟨t, hm, hb.1 t ht⟩
  · intro h t hm ht
    have hh := List.any_eq_true.mpr ⟨t, hm, hb.2 t ht⟩
    simp [h] at hh

def fragmentMask (b : FragmentBits) : Nat :=
  (if b .finite then 1 else 0) + (if b .safety then 2 else 0) +
  (if b .cosafety then 4 else 0) + (if b .pi2 then 8 else 0) +
  (if b .sigma2 then 16 else 0)

end Tlsf.Dpa.Impl
