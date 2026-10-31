import TlsfProofs.Dpa.Impl.DefaultTags

/-!
# Language certificates for recursive canonical tags

These lemmas concern the actual frozen syntax justified by `RefinedAtom`.
Boolean absorption is used only at class support boundaries; temporal
operands are not replaced by a language-equivalent structural witness.
-/
namespace Tlsf.Dpa.Impl
open Formula Class
variable {ap : Nat}
noncomputable section
local instance refinedLanguageDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Backwards valuation substitution for an arbitrary finite derivative. -/
def derivativeAssignment (w : Word (Fin ap)) (j : Nat) : Nat → Assignment ap → Assignment ap
  | 0, σ => unfoldAtom σ
  | n+1, σ => unfoldAtom (stepAtom (w j)
      (unfoldAtom (derivativeAssignment w (j+1) n σ)))

theorem derivatives_eval (w : Word (Fin ap)) (j n : Nat) (x : Class ap)
    (σ : Assignment ap) :
    derivatives w j n x σ = x (derivativeAssignment w j n σ) := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih => rw [derivatives, ih]; rfl

/-- Derivatives of a Boolean class depend only on derivatives of its actual
support atoms, even when the supplied syntax contains absorbed modalities. -/
theorem derivatives_support_eq (w : Word (Fin ap)) (j n : Nat) (x : Class ap)
    (σ τ : Assignment ap)
    (h : ∀ a, Uses x a → derivatives w j n (Class.ofFormula a) σ =
      derivatives w j n (Class.ofFormula a) τ) :
    derivatives w j n x σ = derivatives w j n x τ := by
  rw [derivatives_eval, derivatives_eval]
  apply support_locality
  intro a ha
  have he := h a ha
  rw [derivatives_eval, derivatives_eval] at he
  change propEval _ a = propEval _ a at he
  simpa only [propEval_used_atom ha] using he

theorem derivatives_constant_of_support (w : Word (Fin ap)) (j n : Nat) (x : Class ap)
    (h : ∀ a, Uses x a → derivatives w j n (Class.ofFormula a) =
      if Sat none w a j then Class.top else Class.bot) :
    derivatives w j n x = if Holds w j x then Class.top else Class.bot := by
  apply Class.ext
  intro σ
  have he := derivatives_support_eq w j n x σ (truthAssignment w (j+n)) (by
    intro a ha; rw [h a ha]; split <;> rfl)
  rw [he]
  have ht := derivatives_holds w j n x
  by_cases hs : Holds w j x
  · rw [ite_eq_left hs]; exact ht.mpr hs
  · rw [ite_eq_right hs]; exact Bool.eq_false_iff.mpr (fun hh => hs (ht.mp hh))

theorem derivatives_constant_persists (w : Word (Fin ap)) (j n m : Nat) (x : Class ap)
    (hn : n ≤ m)
    (h : derivatives w j n x = if Holds w j x then Class.top else Class.bot) :
    derivatives w j m x = if Holds w j x then Class.top else Class.bot := by
  by_cases hs : Holds w j x <;> simp only [hs, ↓reduceIte] at h ⊢
  · exact derivatives_top_persists h hn
  · exact derivatives_bot_persists h hn

theorem modalAtom_horizon (f a : Formula (Fin ap)) (ha : a ∈ modalAtoms f) :
    horizon a ≤ horizon f := by
  induction f with
  | tt | ff => contradiction
  | neg f ih => exact ih ha
  | conj f g ihf ihg | disj f g ihf ihg | impl f g ihf ihg | equiv f g ihf ihg =>
    rcases List.mem_append.mp ha with ha | ha
    · exact Nat.le_trans (ihf ha) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihg ha) (Nat.le_max_right _ _)
  | _ => have he := List.mem_singleton.mp ha; subst a; exact Nat.le_refl _

theorem usedAtom_horizon (ha : Uses (Class.ofFormula f) a) : horizon a ≤ horizon f :=
  modalAtom_horizon f a (uses_in_bound (fun σ τ h => propEval_local f σ τ h) ha)

/-- A canonical finite bit decides after at most the frozen syntax's horizon
plus one letters. No positivity or NNF premise is needed for this bound. -/
theorem refined_finite_atom_constant (h : RefinedAtom t a) :
    t = .finite → ∀ (w : Word (Fin ap)) (j n : Nat), horizon a < n →
    derivatives w j n (Class.ofFormula a) =
      if Sat none w a j then Class.top else Class.bot := by
  induction h with
  | @structural t a ht =>
    intro he w j n hn
    subst t
    simpa only [ofFormula_holds] using
      derivatives_constant_persists w j (horizon a+1) n (Class.ofFormula a)
      (by omega) (by simpa only [ofFormula_holds] using finite_window_constant a ht w j)
  | @materialized a t left right hl hr ht ihl ihr =>
    intro he w j n hn
    subst t
    cases a <;> simp only [transferBits, eventualBits, globalBits, Bool.false_eq_true] at ht
    case next f =>
      cases n with
      | zero => omega
      | succ n =>
        have hc : derivatives w (j+1) n (Class.ofFormula f) =
            if Holds w (j+1) (Class.ofFormula f) then Class.top else Class.bot := by
          apply derivatives_constant_of_support
          intro b hb
          exact ihl .finite ht b hb rfl w (j+1) n
            (by have hh := usedAtom_horizon hb; simp only [horizon] at hn; omega)
        have hd : delta (w j) (Class.ofFormula (.next f)) = U (Class.ofFormula f) := by
          apply Class.ext; intro σ; rfl
        rw [derivatives, hd, derivatives_U, hc]
        simp only [ofFormula_holds, Sat, InRange, true_and, not_true_eq_false, false_or]

theorem refined_finite_class_constant (h : RefinedClass .finite f)
    (w : Word (Fin ap)) (j n : Nat) (hn : horizon f < n) :
    derivatives w j n (Class.ofFormula f) =
      if Sat none w f j then Class.top else Class.bot := by
  rw [← ofFormula_holds]
  apply derivatives_constant_of_support
  intro a ha
  exact refined_finite_atom_constant (h a ha) rfl w j n
    (Nat.lt_of_le_of_lt (usedAtom_horizon ha) hn)

/-- A derivative observes only the letters it consumes. -/
theorem derivatives_prefix (w v : Word (Fin ap)) (j n : Nat) (x : Class ap)
    (h : ∀ k, j ≤ k → k < j+n → w k = v k) :
    derivatives w j n x = derivatives v j n x := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih =>
    simp only [derivatives, h j (Nat.le_refl _) (by omega)]
    exact ih (j+1) _ (fun k hk hkn => h k (by omega) (by omega))

theorem refined_finite_window (h : RefinedClass .finite f)
    (w v : Word (Fin ap)) (j : Nat)
    (hw : ∀ k, j ≤ k → k ≤ j+horizon f → w k = v k) :
    Sat none w f j ↔ Sat none v f j := by
  have hd := derivatives_prefix w v j (horizon f+1) (Class.ofFormula f)
    (fun k hk hkn => hw k hk (by omega))
  rw [refined_finite_class_constant h w j _ (by omega),
    refined_finite_class_constant h v j _ (by omega)] at hd
  have hne : (Class.top : Class ap) ≠ Class.bot := by
    intro he
    have hh := congrArg (fun x : Class ap => x (fun _ => false)) he
    exact Bool.noConfusion hh
  by_cases hs : Sat none w f j <;> by_cases ht : Sat none v f j <;> simp_all

/-- Semantic certificates expose constants in the actual derivative run. -/
def GoodPrefix (f : Formula (Fin ap)) : Prop :=
  ∀ w j, Sat none w f j → EventuallyTop w j (Class.ofFormula f)

def BadPrefix (f : Formula (Fin ap)) : Prop :=
  ∀ w j, ¬Sat none w f j → EventuallyBot w j (Class.ofFormula f)

theorem goodPrefix_support (x : Class ap) (hx : Positive x)
    (h : ∀ a, Uses x a → GoodPrefix a) (hs : Holds w j x) : EventuallyTop w j x := by
  apply (allMeet_witness ((supportList x).map (goodFactor (truthAssignment w j))) ?_).mono
    (goodBranch_implies x hx _ hs)
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  have hu := (mem_supportList x a).mp ha
  unfold goodFactor
  split
  · rename_i hap
    cases a <;> simp only [isAP] at hap
    case ap p =>
      split
      · rename_i hs'
        apply h (.ap p) hu w j
        simpa only [truthAssignment, decide_eq_true_eq] using hs'
      · rename_i hs'
        have hn : ¬Sat none w (.ap p) j := by
          simpa only [truthAssignment, decide_eq_true_eq] using hs'
        exact cosafety_witness (.neg (.ap p)) (by trivial) w j ⟨trivial, hn⟩
  · split
    · rename_i hs'
      apply h a hu w j
      simpa only [truthAssignment, decide_eq_true_eq] using hs'
    · exact ⟨0, U_top⟩

theorem badPrefix_support (x : Class ap) (hx : Positive x)
    (h : ∀ a, Uses x a → BadPrefix a) (hs : ¬Holds w j x) : EventuallyBot w j x := by
  apply (allJoin_bad_prefix ((supportList x).map (badFactor (truthAssignment w j))) ?_).antimono
    (implies_badClause x hx _ (Bool.eq_false_iff.mpr hs))
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  have hu := (mem_supportList x a).mp ha
  unfold badFactor
  split
  · rename_i hap
    cases a <;> simp only [isAP] at hap
    case ap p =>
      split
      · rename_i hs'
        have hn : ¬Sat none w (.neg (.ap p)) j := by
          intro hneg
          apply hneg.2
          simpa only [truthAssignment, decide_eq_true_eq] using hs'
        exact safety_bad_prefix (.neg (.ap p)) (by trivial) w j hn
      · rename_i hs'
        apply h (.ap p) hu w j
        simpa only [truthAssignment, decide_eq_true_eq] using hs'
  · split
    · exact ⟨0, rfl⟩
    · rename_i hs'
      apply h a hu w j
      simpa only [truthAssignment, decide_eq_true_eq] using hs'

theorem nnf_modalAtom (hf : NNF f) (ha : a ∈ modalAtoms f) : NNF a := by
  induction f with
  | tt | ff => contradiction
  | neg f ih => cases f <;> simp_all [NNF, modalAtoms]
  | conj f g ihf ihg | disj f g ihf ihg =>
    rcases List.mem_append.mp ha with ha | ha
    · exact ihf hf.1 ha
    · exact ihg hf.2 ha
  | impl f g | equiv f g | strongNext f => contradiction
  | _ => have he := List.mem_singleton.mp ha; subst a; exact hf

theorem nnf_usedAtom (hf : NNF f) (ha : Uses (Class.ofFormula f) a) : NNF a :=
  nnf_modalAtom hf (uses_in_bound (fun σ τ h => propEval_local f σ τ h) ha)

theorem GoodPrefix.next (hf : GoodPrefix f) : GoodPrefix (.next f) := by
  intro w j hs
  apply EventuallyTop.step.mpr
  have he : delta (w j) (Class.ofFormula (.next f)) = U (Class.ofFormula f) := by
    apply Class.ext; intro σ; rfl
  rw [he]
  exact (hf w (j+1) (hs.2.resolve_left (fun h => h trivial))).to_U

theorem GoodPrefix.eventually (hf : GoodPrefix f) : GoodPrefix (.eventually f) := by
  intro w j hs
  obtain ⟨k, hjk, hrange, hk⟩ := hs.2
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
  have hk' : Sat none w f (j+d) := hd ▸ hk
  clear hs hjk hk hd hrange k
  induction d generalizing j with
  | zero =>
    apply EventuallyTop.of_U
    rw [U_eventually]
    exact (hf w j hk').to_U.join_left
  | succ d ih =>
    apply EventuallyTop.step.mpr
    rw [delta_eventually]
    exact (ih (j+1) (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hk')).to_U.join_right

theorem GoodPrefix.until (hf : GoodPrefix f) (hg : GoodPrefix g) : GoodPrefix (.until f g) := by
  intro w j hs
  obtain ⟨k, hjk, hrange, hsat, hall⟩ := hs.2
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
  have hg' : Sat none w g (j+d) := hd ▸ hsat
  have hall' : ∀ i, j ≤ i → i < j+d → Sat none w f i := by simpa only [← hd] using hall
  clear hs hjk hsat hall hd hrange k
  induction d generalizing j with
  | zero =>
    apply EventuallyTop.of_U
    rw [U_until]
    exact (hg w j hg').to_U.join_left
  | succ d ih =>
    apply EventuallyTop.step.mpr
    rw [delta_until]
    have ht := ih (j+1)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hg')
      (fun i hi hik => hall' i (by omega) (by omega))
    have hfirst := EventuallyTop.step.mp (hf w j (hall' j (Nat.le_refl _) (by omega)))
    exact (hfirst.meet ht.to_U).join_right

theorem GoodPrefix.strongRelease (hf : GoodPrefix f) (hg : GoodPrefix g) :
    GoodPrefix (.strongRelease f g) := by
  intro w j hs
  have he := (Tlsf.Rewrites.strongRelease_eq (len := none) (w := w) (a := f) (b := g) (j := j) trivial).mp hs
  obtain ⟨k, hjk, hrange, hfg, hall⟩ := he.2
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
  have hfg' : Sat none w f (j+d) ∧ Sat none w g (j+d) := hd ▸ hfg.2
  have hall' : ∀ i, j ≤ i → i < j+d → Sat none w g i := by simpa only [← hd] using hall
  clear hs he hjk hfg hall hd hrange k
  induction d generalizing j with
  | zero =>
    apply EventuallyTop.of_U
    rw [U_strongRelease]
    exact (hg w j hfg'.2).to_U.meet (hf w j hfg'.1).to_U.join_left
  | succ d ih =>
    apply EventuallyTop.step.mpr
    rw [delta_strongRelease]
    have ht := ih (j+1)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hfg')
      (fun i hi hik => hall' i (by omega) (by omega))
    have hfirst := EventuallyTop.step.mp (hg w j (hall' j (Nat.le_refl _) (by omega)))
    exact hfirst.meet ht.to_U.join_right

theorem BadPrefix.next (hf : BadPrefix f) : BadPrefix (.next f) := by
  intro w j hs
  apply EventuallyBot.step.mpr
  have he : delta (w j) (Class.ofFormula (.next f)) = U (Class.ofFormula f) := by
    apply Class.ext; intro σ; rfl
  rw [he]
  exact (hf w (j+1) (fun h => hs ⟨trivial, Or.inr h⟩)).to_U

theorem BadPrefix.globally (hf : BadPrefix f) : BadPrefix (.globally f) := by
  intro w j hs
  have hex : ∃ k, j ≤ k ∧ ¬Sat none w f k := by
    apply Classical.byContradiction; intro hn
    apply hs; refine ⟨trivial, ?_⟩
    intro k hk _
    exact Classical.byContradiction (fun h => hn ⟨k, hk, h⟩)
  obtain ⟨k, hjk, hk⟩ := hex
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
  have hk' : ¬Sat none w f (j+d) := hd ▸ hk
  clear hs hjk hk hd k
  induction d generalizing j with
  | zero =>
    apply EventuallyBot.of_U
    rw [U_globally]
    exact (hf w j hk').to_U.meet_left
  | succ d ihd =>
    apply EventuallyBot.step.mpr
    rw [delta_globally]
    have ht := ihd (j+1) (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hk')
    exact ht.to_U.meet_right

theorem BadPrefix.release (hleft : BadPrefix f) (hright : BadPrefix g) : BadPrefix (.release f g) := by
  intro w j hs
  have hu : UntilAt none j (fun k => ¬Sat none w f k) (fun k => ¬Sat none w g k) :=
    Classical.byContradiction (fun hn => hs ⟨trivial, hn⟩)
  obtain ⟨k, hjk, hrange, hg, hall⟩ := hu
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
  have hg' : ¬Sat none w g (j+d) := hd ▸ hg
  have hall' : ∀ i, j ≤ i → i < j+d → ¬Sat none w f i := by simpa only [← hd] using hall
  clear hs hjk hg hall hd hrange k
  induction d generalizing j with
  | zero =>
    apply EventuallyBot.of_U
    rw [U_release]
    exact (hright w j hg').to_U.meet_left
  | succ d ihd =>
    apply EventuallyBot.step.mpr
    rw [delta_release]
    have ht := ihd (j+1)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hg')
      (fun i hi hik => hall' i (by omega) (by omega))
    have hfirst := EventuallyBot.step.mp (hleft w j (hall' j (Nat.le_refl _) (by omega)))
    exact (hfirst.join ht.to_U).meet_right

theorem BadPrefix.weakUntil (hleft : BadPrefix f) (hright : BadPrefix g) : BadPrefix (.weakUntil f g) := by
  intro w j hs
  have hn : ¬(UntilAt none j (Sat none w f) (Sat none w g) ∨ AllFuture none j (Sat none w f)) :=
    fun h => hs ⟨trivial, h⟩
  have hu := (Tlsf.Rewrites.not_weakUntil_dual (len := none) (j := j)
    (p := fun k => ¬Sat none w f k) (q := fun k => ¬Sat none w g k)).mp
    (by simpa only [Classical.not_not] using hn)
  obtain ⟨k, hjk, hrange, hfg, hall⟩ := hu
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjk
  have hfg' : ¬Sat none w f (j+d) ∧ ¬Sat none w g (j+d) := hd ▸ hfg
  have hall' : ∀ i, j ≤ i → i < j+d → ¬Sat none w g i := by simpa only [← hd] using hall
  clear hs hn hjk hfg hall hd hrange k
  induction d generalizing j with
  | zero =>
    apply EventuallyBot.of_U
    rw [U_weakUntil]
    exact (hright w j hfg'.2).to_U.join (hleft w j hfg'.1).to_U.meet_left
  | succ d ihd =>
    apply EventuallyBot.step.mpr
    rw [delta_weakUntil]
    have ht := ihd (j+1)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 d] using hfg')
      (fun i hi hik => hall' i (by omega) (by omega))
    have hg := EventuallyBot.step.mp (hright w j (hall' j (Nat.le_refl _) (by omega)))
    exact hg.join ht.to_U.meet_right

/-- Only safety/co-safety bits are used by these two certificates. -/
def PrefixCertificate (t : FragmentTag) (f : Formula (Fin ap)) : Prop :=
  (t = .safety → BadPrefix f) ∧ (t = .cosafety → GoodPrefix f)

/-- Recursive canonical operands justify bad/good prefixes of the frozen
atom itself. Positivity is obtained from NNF at each materialized boundary. -/
theorem refined_prefix_atom (h : RefinedAtom t a) : NNF a → PrefixCertificate t a := by
  induction h with
  | @structural t a ht =>
    intro _
    constructor
    · intro he; subst t; exact safety_bad_prefix a ht
    · intro he; subst t; exact cosafety_witness a ht
  | @materialized a t left right hl hr ht ihl ihr =>
    have hleft (u : FragmentTag) (hu : left u = true) (hn : NNF (tagLhs a)) :
        PrefixCertificate u (tagLhs a) := by
      constructor
      · intro he w j hs
        apply badPrefix_support _ (nnf_positive _ hn) _ ((not_congr (ofFormula_holds _)).mpr hs)
        intro b hb
        exact (ihl u hu b hb (nnf_usedAtom hn hb)).1 he
      · intro he w j hs
        apply goodPrefix_support _ (nnf_positive _ hn) _ ((ofFormula_holds _).mpr hs)
        intro b hb
        exact (ihl u hu b hb (nnf_usedAtom hn hb)).2 he
    have hright (u : FragmentTag) (hu : right u = true) (hn : NNF (tagRhs a)) :
        PrefixCertificate u (tagRhs a) := by
      constructor
      · intro he w j hs
        apply badPrefix_support _ (nnf_positive _ hn) _ ((not_congr (ofFormula_holds _)).mpr hs)
        intro b hb
        exact (ihr u hu b hb (nnf_usedAtom hn hb)).1 he
      · intro he w j hs
        apply goodPrefix_support _ (nnf_positive _ hn) _ ((ofFormula_holds _).mpr hs)
        intro b hb
        exact (ihr u hu b hb (nnf_usedAtom hn hb)).2 he
    intro hn
    constructor
    · intro he
      subst t
      cases a <;> simp only [transferBits, eventualBits, globalBits, bitsMeet,
        Bool.and_eq_true, Bool.false_eq_true] at ht
      case next f => exact ((hleft .safety ht hn).1 rfl).next
      case globally f => exact ((hleft .safety ht hn).1 rfl).globally
      case release f g =>
        exact ((hleft .safety ht.1 hn.1).1 rfl).release ((hright .safety ht.2 hn.2).1 rfl)
      case weakUntil f g =>
        exact ((hleft .safety ht.1 hn.1).1 rfl).weakUntil ((hright .safety ht.2 hn.2).1 rfl)
    · intro he
      subst t
      cases a <;> simp only [transferBits, eventualBits, globalBits, bitsMeet,
        Bool.and_eq_true, Bool.false_eq_true] at ht
      case next f => exact ((hleft .cosafety ht hn).2 rfl).next
      case eventually f => exact ((hleft .cosafety ht hn).2 rfl).eventually
      case «until» f g =>
        exact ((hleft .cosafety ht.1 hn.1).2 rfl).until ((hright .cosafety ht.2 hn.2).2 rfl)
      case strongRelease f g =>
        exact ((hleft .cosafety ht.1 hn.1).2 rfl).strongRelease ((hright .cosafety ht.2 hn.2).2 rfl)

theorem refined_safety_bad_prefix (hn : NNF f) (h : RefinedClass .safety f)
    (w : Word (Fin ap)) (j : Nat) (hs : ¬Sat none w f j) :
    EventuallyBot w j (Class.ofFormula f) := by
  apply badPrefix_support _ (nnf_positive _ hn) _ ((not_congr (ofFormula_holds _)).mpr hs)
  intro a ha
  exact (refined_prefix_atom (h a ha) (nnf_usedAtom hn ha)).1 rfl

theorem refined_cosafety_witness (hn : NNF f) (h : RefinedClass .cosafety f)
    (w : Word (Fin ap)) (j : Nat) (hs : Sat none w f j) :
    EventuallyTop w j (Class.ofFormula f) := by
  apply goodPrefix_support _ (nnf_positive _ hn) _ ((ofFormula_holds _).mpr hs)
  intro a ha
  exact (refined_prefix_atom (h a ha) (nnf_usedAtom hn ha)).2 rfl

/-- A refined atom justifies every support atom of its own class. The
structural constructor can also contain Boolean syntax; materialized
constructors are frozen modalities. -/
theorem RefinedAtom.class_tag (h : RefinedAtom t a) :
    HasTag (RefinedAtom t) (Class.ofFormula a) := by
  cases h with
  | structural hs =>
    intro b hb
    exact .structural (syntax_tag_lower a t hs b hb)
  | materialized left right hl hr ht =>
    intro b hb
    have hm := uses_in_bound (fun σ τ hh => propEval_local _ σ τ hh) hb
    cases a <;> simp only [transferBits, Bool.false_eq_true] at ht
    all_goals
      have he := List.mem_singleton.mp hm
      subst b
      exact .materialized left right hl hr ht

def LocalFragment (t : FragmentTag) : Prop := t = .finite ∨ t = .safety ∨ t = .cosafety

theorem tag_U_of_atoms {x : Class ap} (h : ∀ a, Uses x a → HasTag tag (U (Class.ofFormula a))) :
    HasTag tag (U x) := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := U_uses hb
  exact h a ha b (by simpa only [U_ofFormula] using hab)

theorem tag_D_of_atoms {x : Class ap} (v : Letter (Fin ap))
    (h : ∀ a, Uses x a → HasTag tag (D v (Class.ofFormula a))) : HasTag tag (D v x) := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := D_uses v hb
  exact h a ha b (by simpa only [D_ofFormula] using hab)

theorem refined_U_atom (h : RefinedAtom t a) :
    LocalFragment t → HasTag (RefinedAtom t) (U (Class.ofFormula a)) := by
  induction h with
  | @structural t a hs =>
    intro ht b hb
    apply RefinedAtom.structural
    rcases ht with rfl | rfl | rfl
    · have hf := formula_finite_tag a hs
      rw [finite_U_fixed hf] at hb
      exact hf b hb
    · exact U_safety (formula_safety_tag a hs) b hb
    · exact U_cosafety (formula_cosafety_tag a hs) b hb
  | @materialized a t left right hl hr ht ihl ihr =>
    have hself := (RefinedAtom.materialized left right hl hr ht).class_tag
    have hleft (u : FragmentTag) (hu : left u = true) (hlocal : LocalFragment u) :
        HasTag (RefinedAtom u) (U (Class.ofFormula (tagLhs a))) :=
      tag_U_of_atoms (fun b hb => ihl u hu b hb hlocal)
    have hright (u : FragmentTag) (hu : right u = true) (hlocal : LocalFragment u) :
        HasTag (RefinedAtom u) (U (Class.ofFormula (tagRhs a))) :=
      tag_U_of_atoms (fun b hb => ihr u hu b hb hlocal)
    intro hlocal
    rcases hlocal with rfl | rfl | rfl
    · cases a <;> simp only [transferBits, eventualBits, globalBits, Bool.false_eq_true] at ht
      case next f => exact hself
    · cases a <;> simp only [transferBits, eventualBits, globalBits, bitsMeet,
        Bool.and_eq_true, Bool.false_eq_true] at ht
      case next f => exact hself
      case globally f =>
        rw [U_globally]
        exact meet_tag (hleft .safety ht (by simp [LocalFragment])) hself
      case release f g =>
        rw [U_release]
        exact meet_tag (hright .safety ht.2 (by simp [LocalFragment]))
          (join_tag (hleft .safety ht.1 (by simp [LocalFragment])) hself)
      case weakUntil f g =>
        rw [U_weakUntil]
        exact join_tag (hright .safety ht.2 (by simp [LocalFragment]))
          (meet_tag (hleft .safety ht.1 (by simp [LocalFragment])) hself)
    · cases a <;> simp only [transferBits, eventualBits, globalBits, bitsMeet,
        Bool.and_eq_true, Bool.false_eq_true] at ht
      case next f => exact hself
      case eventually f =>
        rw [U_eventually]
        exact join_tag (hleft .cosafety ht (by simp [LocalFragment])) hself
      case «until» f g =>
        rw [U_until]
        exact join_tag (hright .cosafety ht.2 (by simp [LocalFragment]))
          (meet_tag (hleft .cosafety ht.1 (by simp [LocalFragment])) hself)
      case strongRelease f g =>
        rw [U_strongRelease]
        exact meet_tag (hright .cosafety ht.2 (by simp [LocalFragment]))
          (join_tag (hleft .cosafety ht.1 (by simp [LocalFragment])) hself)

theorem refined_U {x : Class ap} (ht : LocalFragment t) (h : HasTag (RefinedAtom t) x) :
    HasTag (RefinedAtom t) (U x) :=
  tag_U_of_atoms (fun a ha => refined_U_atom (h a ha) ht)

theorem refined_D_atom (ht : LocalFragment t) (h : RefinedAtom t a)
    (v : Letter (Fin ap)) : HasTag (RefinedAtom t) (D v (Class.ofFormula a)) := by
  cases h with
  | structural hs =>
    intro b hb
    apply RefinedAtom.structural
    rcases ht with rfl | rfl | rfl
    · exact D_finite v (formula_finite_tag a hs) b hb
    · exact D_safety v (formula_safety_tag a hs) b hb
    · exact D_cosafety v (formula_cosafety_tag a hs) b hb
  | materialized left right hl hr hbit =>
    have hself := (RefinedAtom.materialized left right hl hr hbit).class_tag
    cases a <;> simp only [transferBits, Bool.false_eq_true] at hbit
    case next f => exact hl t hbit
    all_goals exact hself

theorem refined_D {x : Class ap} (ht : LocalFragment t) (v : Letter (Fin ap)) (h : HasTag (RefinedAtom t) x) :
    HasTag (RefinedAtom t) (D v x) :=
  tag_D_of_atoms v (fun a ha => refined_D_atom ht (h a ha) v)

theorem refined_finite_U_fixed {x : Class ap} (h : HasTag (RefinedAtom .finite) x) : U x = x := by
  apply Class.ext
  intro σ
  change x (unfoldAtom σ) = x σ
  apply support_locality
  intro a ha
  have ht := h a ha
  have he : U (Class.ofFormula a) = Class.ofFormula a := by
    cases ht with
    | structural hs => exact finite_U_fixed (formula_finite_tag a hs)
    | materialized l r hl hr hb =>
      cases a <;> simp only [transferBits, eventualBits, globalBits, Bool.false_eq_true] at hb
      rfl
  have heval := congrArg (fun c : Class ap => c σ) he
  change propEval (unfoldAtom σ) a = propEval σ a at heval
  simpa only [propEval_used_atom ha] using heval

/-- Direct consumers of the bits returned by the executable classifier. -/
theorem defaultTags_language_certificates (rank : Formula (Fin ap) → Nat)
    (highFirst : Formula (Fin ap) → Bool) (fuel : Nat) (started : Bool)
    (hn : NNF f) (hs : s.Valid)
    (he : defaultTags rank highFirst fuel started f s = some (b, s')) :
    (b .finite = true → ∀ w j n, horizon f < n →
      derivatives w j n (Class.ofFormula f) =
        if Sat none w f j then Class.top else Class.bot) ∧
    (b .safety = true → BadPrefix f) ∧ (b .cosafety = true → GoodPrefix f) := by
  have hb := (defaultTags_sound rank highFirst fuel started f s b s' hs he).2.2
  exact ⟨fun hf => refined_finite_class_constant (hb .finite hf),
    fun hf => refined_safety_bad_prefix hn (hb .safety hf),
    fun hf => refined_cosafety_witness hn (hb .cosafety hf)⟩

end
end Tlsf.Dpa.Impl
