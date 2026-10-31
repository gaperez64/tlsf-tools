import TlsfProofs.Dpa.Impl.Factoring
import TlsfProofs.Dpa.Impl.Buchi
import TlsfProofs.Dpa.Validation.Automaton

/-! The uncached executable construction. Correctness concerns the machines
returned here, independently of C's representation and optimizations. -/
namespace Tlsf.Dpa.Impl
variable {ap : Nat}

abbrev Configuration (r : Assembly ap) := Fin r.store.length → State ap

def Assembly.productInitial (r : Assembly ap) : Configuration r :=
  fun i => initial r.store[i.val].formula

def Assembly.productStep (r : Assembly ap) (s : Configuration r) (v : Letter (Fin ap)) :
    Configuration r × ColourSet r.store.length :=
  (fun i => (transition v (s i)).target, fun i => (transition v (s i)).mark)

def Assembly.productRun (r : Assembly ap) (w : Word (Fin ap)) : Nat → Configuration r
  | 0 => r.productInitial
  | n+1 => (r.productStep (r.productRun w n) (w n)).1

def Assembly.colours (r : Assembly ap) (w : Word (Fin ap)) (n : Nat) : ColourSet r.store.length :=
  (r.productStep (r.productRun w n) (w n)).2

theorem Assembly.productRun_projection (r : Assembly ap) (w : Word (Fin ap))
    (n : Nat) (i : Fin r.store.length) :
    r.productRun w n i = run r.store[i.val].formula w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Assembly.productRun, Assembly.productStep, run, ih]

theorem Assembly.colours_exact (r : Assembly ap) (w : Word (Fin ap)) :
    r.colours w = productColours (storeClasses r.store) w := by
  funext n i
  rw [store_productColours]
  simp only [Assembly.colours, Assembly.productStep, Assembly.productRun_projection,
    storeColours, List.getElem?_eq_getElem i.isLt, marks]

def Assembly.tree (r : Assembly ap) : ZTree r.skeleton (fullColours r.store.length) :=
  buildTree r.skeleton (fullColours r.store.length)

def Assembly.parity (r : Assembly ap) :
    Validation.Parity (Letter (Fin ap)) (Configuration r × List Nat) where
  initial := (r.productInitial, r.tree.leftmost)
  step s v :=
    let p := r.productStep s.1 v
    let t := r.tree.advance s.2 p.2
    ((p.1, t.1), exportBound r.store.length -
      (t.2 + if r.skeleton (fullColours r.store.length) then 0 else 1))

theorem Assembly.parity_run (r : Assembly ap) (w : Word (Fin ap)) (n : Nat) :
    r.parity.run w n = (r.productRun w n, treeRun r.tree (r.colours w) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Validation.Parity.run, ih]
    rfl

theorem Assembly.parity_language (r : Assembly ap) (f : Formula (Fin ap))
    (hp : ProductPresentation f (storeClasses r.store) r.skeleton) (w : Word (Fin ap)) :
    r.parity.Accepts w ↔ Sat none w f 0 := by
  have he : r.parity.priorities w =
      fun n => exportBound r.store.length - treePriority r.tree (r.colours w) n := by
    funext n
    unfold Validation.Parity.priorities
    rw [Assembly.parity_run]
    rfl
  rw [Validation.Parity.Accepts, he, tree_maxOdd, Assembly.colours_exact]
  exact (product_language _ _ w (fun i => hp.1 i w)).trans (hp.2 w)

def liftDag {n : Nat} : ColourDag n → ColourDag (n+1)
  | .leaf b => .leaf b
  | .node i l h => .node i.succ (liftDag l) (liftDag h)

/-- Tabulate a Boolean acceptance as a Shannon diagram, without any BDD library. -/
def truthDag : (n : Nat) → Skeleton n → ColourDag n
  | 0, β => .leaf (β Fin.elim0)
  | n+1, β =>
    .node 0 (liftDag (truthDag n (fun v => β (Fin.cases false v))))
      (liftDag (truthDag n (fun v => β (Fin.cases true v))))

theorem truthDag_lift (d : ColourDag n) (v : Fin (n+1) → Bool) :
    (liftDag d).eval v = d.eval (fun i => v i.succ) := by
  induction d with
  | leaf _ => rfl
  | node i l h il ih => simp only [liftDag, ColourDag.eval, il, ih]

theorem truthDag_eval (β : Skeleton n) (v : Fin n → Bool) : (truthDag n β).eval v = β v := by
  induction n with
  | zero => have hv : v = Fin.elim0 := funext (fun i => Fin.elim0 i); subst v; rfl
  | succ n ih =>
    simp only [truthDag, ColourDag.eval, truthDag_lift, ih]
    have hv : Fin.cases (v 0) (fun i => v i.succ) = v := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    cases h : v 0 <;> simpa only [h, Bool.false_eq_true, ↓reduceIte] using congrArg β hv

def positiveb (β : Skeleton m) : Bool :=
  (colourVectors m).all (fun a => (colourVectors m).all (fun b =>
    !(decide (Dpa.Subset a b) && β a) || β b))

theorem positiveb_exact (β : Skeleton m) : positiveb β = true ↔ PositiveColours β := by
  have imp (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
    cases a <;> cases b <;> decide
  simp only [positiveb, List.all_eq_true, imp, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h a b hab ha => h a (colourVectors_complete a) b (colourVectors_complete b) ⟨hab, ha⟩,
    fun h a _ b _ hab => h a b hab.1 hab.2⟩

def Assembly.buchi (r : Assembly ap) :
    Validation.Buchi (Letter (Fin ap)) (Configuration r × RoundState r.store.length) where
  initial := (r.productInitial, roundInitial (truthDag _ r.skeleton))
  step s v :=
    let p := r.productStep s.1 v
    (p.1, roundStep (truthDag _ r.skeleton) s.2 p.2)
  accepting s := s.2.incoming

theorem Assembly.buchi_run (r : Assembly ap) (w : Word (Fin ap)) (n : Nat) :
    r.buchi.run w n = (r.productRun w n, roundRun (truthDag _ r.skeleton) (r.colours w) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Validation.Buchi.run, ih]
    rfl

theorem Assembly.buchi_language (r : Assembly ap) (f : Formula (Fin ap))
    (hp : ProductPresentation f (storeClasses r.store) r.skeleton)
    (hb : positiveb r.skeleton = true) (w : Word (Fin ap)) :
    r.buchi.Accepts w ↔ Sat none w f 0 := by
  have hd : (truthDag _ r.skeleton).eval = r.skeleton := funext (truthDag_eval r.skeleton)
  have hpos : PositiveColours (truthDag _ r.skeleton).eval := by
    rw [hd]; exact (positiveb_exact _).mp hb
  change Inf (fun n => (r.buchi.run w n).2.incoming) ↔ _
  simp only [Assembly.buchi_run]
  change Inf (incomingMarks (truthDag _ r.skeleton) (r.colours w)) ↔ _
  rw [incomingMarks_language _ hpos, hd, Assembly.colours_exact]
  exact (product_language _ _ w (fun i => hp.1 i w)).trans (hp.2 w)

def construct (rank atomRank : Formula (Fin ap) → Nat) (f : Formula (Fin ap)) :
    Option (Assembly ap) := (referencePlan rank atomRank f).map (fun p => assemble false p [])

/-- The same executable construction supplies the parity language, and the
state-based round-monitor language whenever its acceptance is positive. -/
theorem uncached_construction_language (rank atomRank : Formula (Fin ap) → Nat)
    (f : Formula (Fin ap)) (ha : transportedResearchCheck rank f = true) :
    ∃ r, construct rank atomRank f = some r ∧
      (∀ w, r.parity.Accepts w ↔ Sat none w f 0) ∧
      (positiveb r.skeleton = true → ∀ w, r.buchi.Accepts w ↔ Sat none w f 0) := by
  obtain ⟨p, hp, hv, hl⟩ := referencePlan_success rank atomRank f ha
  have hs : StoreValid ([] : ComponentStore ap) := by intro e he; simp at he
  have hpres := assemble_presentation_of_language false p hv [] hs f (fun w => hl w 0)
  exact ⟨assemble false p [], by simp [construct, hp],
    fun w => Assembly.parity_language _ f hpres w,
    fun hb w => Assembly.buchi_language _ f hpres hb w⟩

end Tlsf.Dpa.Impl
