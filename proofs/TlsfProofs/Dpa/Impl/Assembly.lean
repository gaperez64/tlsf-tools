import TlsfProofs.Dpa.Impl.Store
import TlsfProofs.Dpa.Impl.Admission

/-!
# Shared-store Boolean and Shannon assembly

Successful construction steps of `src/lib/dpa_dela.c:117` and
`src/lib/dpa_formula.c:583` are represented by an explicit acceptance plan:
constants, admitted whole classes, Boolean grouping, and Shannon branching.
Compilation executes the store lookup/update, threads the resulting stores,
and constructs indexed acceptance, rather than asking for an existential
product presentation. Every intermediate acceptance has an index bound, so
later insertions preserve its entire meaning.

This module proves assembly of a valid plan. Selecting the exact plan from
C's materialized classes, grouping, memoized DAG and argument evaluation
order remains separate; in particular, this is not the complete C grouped
constructor or its transport/default-tag refinement. The reference compiles
the high child before the low child, with soundness independent of the
original store's contents or existing sharing.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

inductive ColourAcceptance where
  | constant : Bool → ColourAcceptance
  | literal : ColourLiteral → ColourAcceptance
  | binary : Bool → ColourAcceptance → ColourAcceptance → ColourAcceptance
  | ite : ColourLiteral → ColourAcceptance → ColourAcceptance → ColourAcceptance
  deriving DecidableEq, Repr

def ColourAcceptance.eval : ColourAcceptance → (Nat → Bool) → Bool
  | .constant b, _ => b
  | .literal l, v => l.eval v
  | .binary op f g, v => if op then f.eval v && g.eval v else f.eval v || g.eval v
  | .ite l high low, v => if l.eval v then high.eval v else low.eval v

def ColourAcceptance.Bounded : ColourAcceptance → Nat → Prop
  | .constant _, _ => True
  | .literal l, n => l.index < n
  | .binary _ f g, n => f.Bounded n ∧ g.Bounded n
  | .ite l high low, n => l.index < n ∧ high.Bounded n ∧ low.Bounded n

theorem ColourAcceptance.Bounded.mono (e : ColourAcceptance) {n k : Nat}
    (h : e.Bounded n) (hn : n ≤ k) : e.Bounded k := by
  induction e with
  | constant _ => trivial
  | literal _ => exact Nat.lt_of_lt_of_le h hn
  | binary _ _ _ ih ih' => exact ⟨ih h.1, ih' h.2⟩
  | ite _ _ _ ih ih' => exact ⟨Nat.lt_of_lt_of_le h.1 hn, ih h.2.1, ih' h.2.2⟩

theorem ColourAcceptance.eval_extends (e : ColourAcceptance) {s t : ComponentStore ap}
    (h : StoreExtends s t) (hb : e.Bounded s.length) (w : Word (Fin ap)) :
    e.eval (storeTruth t w) = e.eval (storeTruth s w) := by
  induction e with
  | constant _ => rfl
  | literal l => exact h.literal w l hb
  | binary op f g ih ih' => simp only [eval, ih hb.1, ih' hb.2]
  | ite l high low ih ih' => simp only [eval, h.literal w l hb.1, ih hb.2.1, ih' hb.2.2]

inductive AcceptancePlan (ap : Nat) where
  | constant : Bool → AcceptancePlan ap
  | whole : Formula (Fin ap) → AcceptancePlan ap
  | binary : Bool → AcceptancePlan ap → AcceptancePlan ap → AcceptancePlan ap
  | shannon : Formula (Fin ap) → AcceptancePlan ap → AcceptancePlan ap → AcceptancePlan ap

def AcceptancePlan.source : AcceptancePlan ap → Formula (Fin ap)
  | .constant b => if b then .tt else .ff
  | .whole f => f
  | .binary op f g => if op then .conj f.source g.source else .disj f.source g.source
  | .shannon a high low => .disj (.conj a high.source) (.conj (.neg a) low.source)

def AcceptancePlan.Valid : AcceptancePlan ap → Prop
  | .constant _ => True
  | .whole f => NNF f ∧ researchAdmitted f = true
  | .binary _ f g => f.Valid ∧ g.Valid
  | .shannon a high low =>
    (NNF a ∧ researchAdmitted a = true) ∧ high.Valid ∧ low.Valid

structure Assembly (ap : Nat) where
  store : ComponentStore ap
  acceptance : ColourAcceptance

def assemble (buchi : Bool) : AcceptancePlan ap → ComponentStore ap → Assembly ap
  | .constant b, s => ⟨s, .constant b⟩
  | .whole f, s =>
    if equivalent f .ff then ⟨s, .constant false⟩
    else if equivalent f .tt then ⟨s, .constant true⟩
    else
      let r := internComponent buchi s f
      ⟨r.1, .literal r.2⟩
  | .binary op f g, s =>
    let left := assemble buchi f s
    let right := assemble buchi g left.store
    ⟨right.store, .binary op left.acceptance right.acceptance⟩
  | .shannon a high low, s =>
    let test := internComponent buchi s a
    let h := assemble buchi high test.1
    let l := assemble buchi low h.store
    ⟨l.store, .ite test.2 h.acceptance l.acceptance⟩

/-- The recursive invariant needed to preserve shared literals through both
branches. It applies to every valid existing store, not just the empty one. -/
theorem assemble_spec (buchi : Bool) (p : AcceptancePlan ap) (hp : p.Valid)
    (s : ComponentStore ap) (hs : StoreValid s) :
    let r := assemble buchi p s
    StoreExtends s r.store ∧ StoreValid r.store ∧ r.acceptance.Bounded r.store.length ∧
      ∀ w, r.acceptance.eval (storeTruth r.store w) = true ↔ Sat none w p.source 0 := by
  induction p generalizing s with
  | constant b =>
    refine ⟨StoreExtends.refl s, hs, trivial, ?_⟩
    intro w; cases b <;> simp [assemble, ColourAcceptance.eval, AcceptancePlan.source, Sat, InRange]
  | whole f =>
    simp only [assemble]
    split
    · rename_i hf
      refine ⟨StoreExtends.refl s, hs, trivial, ?_⟩
      intro w
      simpa [ColourAcceptance.eval, AcceptancePlan.source, Sat] using
        (class_language ((equivalent_exact f .ff).mp hf) w 0).symm
    · split
      · rename_i hf
        refine ⟨StoreExtends.refl s, hs, trivial, ?_⟩
        intro w
        simpa [ColourAcceptance.eval, AcceptancePlan.source, Sat, InRange] using
          (class_language ((equivalent_exact f .tt).mp hf) w 0).symm
      · exact ⟨internComponent_prefix buchi s f,
          internComponent_valid buchi s hs f hp.1 hp.2,
          internComponent_bound buchi s f,
          internComponent_language buchi s hs f hp.1 hp.2⟩
  | binary op f g ihf ihg =>
    obtain ⟨ef, vf, bf, lf⟩ := ihf hp.1 s hs
    obtain ⟨eg, vg, bg, lg⟩ := ihg hp.2 (assemble buchi f s).store vf
    refine ⟨ef.trans eg, vg, ⟨bf.mono _ eg.length_le, bg⟩, ?_⟩
    intro w
    have he := (assemble buchi f s).acceptance.eval_extends eg bf w
    dsimp only [assemble, ColourAcceptance.eval]
    rw [he]
    cases op <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
        lf w, lg w, AcceptancePlan.source, Sat, InRange, true_and]
  | shannon a high low ihh ihl =>
    have et : StoreExtends s (internComponent buchi s a).1 := internComponent_prefix buchi s a
    have vt := internComponent_valid buchi s hs a hp.1.1 hp.1.2
    have bt := internComponent_bound buchi s a
    have lt := internComponent_language buchi s hs a hp.1.1 hp.1.2
    obtain ⟨eh, vh, bh, lh⟩ := ihh hp.2.1 (internComponent buchi s a).1 vt
    obtain ⟨el, vl, bl, ll⟩ := ihl hp.2.2
      (assemble buchi high (internComponent buchi s a).1).store vh
    refine ⟨et.trans (eh.trans el), vl,
      ⟨Nat.lt_of_lt_of_le bt (eh.trans el).length_le, bh.mono _ el.length_le, bl⟩, ?_⟩
    intro w
    have heTest := (eh.trans el).literal w (internComponent buchi s a).2 bt
    have heHigh := (assemble buchi high (internComponent buchi s a).1).acceptance.eval_extends el bh w
    dsimp only [assemble, ColourAcceptance.eval]
    rw [heTest, heHigh]
    cases hc : (internComponent buchi s a).2.eval
      (storeTruth (internComponent buchi s a).1 w) with
    | false =>
      have ha : ¬Sat none w a 0 := by
        intro ha
        have hh := (lt w).mpr ha
        rw [hc] at hh
        contradiction
      simp only [Bool.false_eq_true, ↓reduceIte, ll w, AcceptancePlan.source,
        Sat, InRange, true_and, ha, false_and, false_or, not_false_eq_true]
    | true =>
      have ha := (lt w).mp hc
      simp only [↓reduceIte, lh w, AcceptancePlan.source, Sat, InRange,
        true_and, ha, not_true_eq_false, false_and, or_false]

/-- Extend a finite valuation by false outside the store. Bounds ensure those
outside values cannot influence the compiled acceptance. -/
def finiteValuation (n : Nat) (v : Fin n → Bool) (i : Nat) : Bool :=
  if h : i < n then v ⟨i, h⟩ else false

def Assembly.skeleton (r : Assembly ap) : Skeleton r.store.length :=
  fun v => r.acceptance.eval (finiteValuation r.store.length v)

theorem ColourAcceptance.eval_local (e : ColourAcceptance) (hb : e.Bounded n)
    (v u : Nat → Bool) (he : ∀ i, i < n → v i = u i) : e.eval v = e.eval u := by
  induction e with
  | constant _ => rfl
  | literal l => simp only [eval, ColourLiteral.eval, he l.index hb]
  | binary _ _ _ ih ih' => simp only [eval, ih hb.1, ih' hb.2]
  | ite l _ _ ih ih' =>
    simp only [eval, ColourLiteral.eval, he l.index hb.1, ih hb.2.1, ih' hb.2.2]
    rfl

/-- The same executable assembly supplies the actual finite product
presentation; no new components are chosen by this theorem. -/
theorem assemble_presentation (buchi : Bool) (p : AcceptancePlan ap) (hp : p.Valid)
    (s : ComponentStore ap) (hs : StoreValid s) :
    let r := assemble buchi p s
    ProductPresentation p.source (storeClasses r.store) r.skeleton := by
  obtain ⟨_, hv, hb, hl⟩ := assemble_spec buchi p hp s hs
  constructor
  · intro i w
    have he := List.getElem?_eq_getElem i.isLt
    have hc := storeColour_language (assemble buchi p s).store hv i.val _ he w
    simpa only [storeClasses, marks_exact, storeColours, he] using
      hc.trans (ofFormula_holds _).symm
  · intro w
    have he := (assemble buchi p s).acceptance.eval_local hb
      (finiteValuation _ (componentTruth (storeClasses (assemble buchi p s).store) w))
      (storeTruth (assemble buchi p s).store w) (by
        intro i hi
        simp only [finiteValuation, hi, ↓reduceDIte]
        exact (storeTruth_componentTruth _ hv w ⟨i, hi⟩).symm)
    unfold Assembly.skeleton
    rw [he]
    exact hl w

/-- A canonical cofactor or grouped/factored-language theorem may identify
the source represented by the selected successful construction plan. -/
theorem assemble_presentation_of_language (buchi : Bool) (p : AcceptancePlan ap) (hp : p.Valid)
    (s : ComponentStore ap) (hs : StoreValid s) (f : Formula (Fin ap))
    (hf : ∀ w, Sat none w p.source 0 ↔ Sat none w f 0) :
    let r := assemble buchi p s
    ProductPresentation f (storeClasses r.store) r.skeleton := by
  obtain ⟨hc, hl⟩ := assemble_presentation buchi p hp s hs
  exact ⟨hc, fun w => (hl w).trans (hf w)⟩

/-- A Shannon cofactor decomposition supplies the source class; compilation
supplies and preserves the actual colour numbers of both branches. -/
theorem assemble_shannon_presentation (buchi : Bool) (s : ComponentStore ap) (hs : StoreValid s)
    (a f : Formula (Fin ap)) (ha : NNF a ∧ researchAdmitted a = true)
    (high low : AcceptancePlan ap) (hh : high.Valid) (hl : low.Valid)
    (he : Class.ofFormula f = Class.ofFormula
      (.disj (.conj a high.source) (.conj (.neg a) low.source))) :
    let r := assemble buchi (.shannon a high low) s
    ProductPresentation f (storeClasses r.store) r.skeleton :=
  assemble_presentation_of_language buchi (.shannon a high low) ⟨ha, hh, hl⟩ s hs f
    (fun w => class_language he.symm w 0)

def foldPlans (op : Bool) : List (AcceptancePlan ap) → AcceptancePlan ap
  | [] => .constant op
  | p::ps => .binary op p (foldPlans op ps)

theorem foldPlans_source (op : Bool) (ps : List (AcceptancePlan ap)) :
    (foldPlans op ps).source = booleanFold op (ps.map AcceptancePlan.source) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases op <;> simp [foldPlans, AcceptancePlan.source, booleanFold, ih]

theorem foldPlans_valid (op : Bool) (ps : List (AcceptancePlan ap))
    (h : ∀ p, p ∈ ps → p.Valid) : (foldPlans op ps).Valid := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨h p (by simp), ih (fun q hq => h q (by simp [hq]))⟩

theorem safety_pi2b (f : Formula α) (h : safety f) : pi2b f = true := by
  induction f with
  | neg f _ => cases f <;> simp_all [safety, pi2b]
  | _ => simp_all [safety, pi2b]

theorem whole_safety_valid (f : Formula (Fin ap)) (h : safety f) :
    (AcceptancePlan.whole f).Valid := by
  refine ⟨safety_nnf h, ?_⟩
  simp only [researchAdmitted, Bool.or_eq_true]
  exact Or.inl ((classTag_exact .pi2 f).mpr
    (syntax_tag_lower f .pi2 ((pi2b_exact f).mp (safety_pi2b f h))))

theorem whole_cosafety_valid (f : Formula (Fin ap)) (h : cosafety f) :
    (AcceptancePlan.whole f).Valid := by
  refine ⟨cosafety_nnf h, ?_⟩
  simp only [researchAdmitted, Bool.or_eq_true]
  exact Or.inl ((classTag_exact .pi2 f).mpr (syntax_tag_lower f .pi2 (.base h)))

/-- Assemble the two canonical groups and recursive rest plans, using the
executable folded-class identity test already proved equal to C's guard. -/
def groupedPlan (op : Bool) (S C B : List (Formula (Fin ap)))
    (rest : List (AcceptancePlan ap)) : AcceptancePlan ap :=
  foldPlans op ((compatibleGroups op S C B []).map AcceptancePlan.whole ++ rest)

theorem groupedPlan_valid (op : Bool) (S C B : List (Formula (Fin ap)))
    (rest : List (AcceptancePlan ap))
    (hs : ∀ f, f ∈ S → safety f) (hc : ∀ f, f ∈ C → cosafety f)
    (hb : ∀ f, f ∈ B → finite f) (ht : ∀ p, p ∈ rest → p.Valid) :
    (groupedPlan op S C B rest).Valid := by
  apply foldPlans_valid
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    rw [compatibleGroups_exact] at hf
    unfold Dpa.compatibleGroups at hf
    split at hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · apply whole_safety_valid; apply booleanFold_safety
        intro g hg
        exact (List.mem_append.mp hg).elim (hs g) (fun h => finite_implies_safety g (hb g h))
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact whole_cosafety_valid _ (booleanFold_cosafety op hc)
        · contradiction
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact whole_safety_valid _ (booleanFold_safety op hs)
      · rcases List.mem_cons.mp hf with rfl | hf
        · apply whole_cosafety_valid; apply booleanFold_cosafety
          intro g hg
          exact (List.mem_append.mp hg).elim (hc g) (fun h => finite_implies_cosafety g (hb g h))
        · contradiction
  · exact ht p hp

theorem groupedPlan_source (op : Bool) (S C B : List (Formula (Fin ap)))
    (rest : List (AcceptancePlan ap)) :
    (groupedPlan op S C B rest).source =
      booleanFold op (compatibleGroups op S C B (rest.map AcceptancePlan.source)) := by
  simp only [groupedPlan, foldPlans_source, List.map_append, List.map_map]
  rw [compatibleGroups_exact, compatibleGroups_exact]
  unfold Dpa.compatibleGroups
  split <;> rfl

theorem groupedPlan_language (op : Bool) (S C B : List (Formula (Fin ap)))
    (rest : List (AcceptancePlan ap)) (w : Word (Fin ap)) (n : Nat) :
    Sat none w (groupedPlan op S C B rest).source n ↔
      Sat none w (booleanFold op (S++C++B++rest.map AcceptancePlan.source)) n := by
  rw [groupedPlan_source]
  exact compatibleGroups_language op S C B _ w n

/-- The grouped acceptance now has a concrete shared-store product
presentation, for both grouping branches and either Boolean operation. -/
theorem assemble_grouped_presentation (buchi : Bool) (s : ComponentStore ap) (hv : StoreValid s)
    (op : Bool) (S C B : List (Formula (Fin ap))) (rest : List (AcceptancePlan ap))
    (hs : ∀ f, f ∈ S → safety f) (hc : ∀ f, f ∈ C → cosafety f)
    (hb : ∀ f, f ∈ B → finite f) (ht : ∀ p, p ∈ rest → p.Valid) :
    let r := assemble buchi (groupedPlan op S C B rest) s
    ProductPresentation (booleanFold op (S++C++B++rest.map AcceptancePlan.source))
      (storeClasses r.store) r.skeleton :=
  assemble_presentation_of_language buchi _ (groupedPlan_valid op S C B rest hs hc hb ht) s hv _
    (fun w => groupedPlan_language op S C B rest w 0)

end Tlsf.Dpa.Impl
