import TlsfProofs.Dpa.Zielonka

/-!
# Executable positive-Boolean Büchi rounds

`src/lib/dpa_dela.c:203` walks the acceptance BDD's Shannon children,
substituting true for every colour on the current edge. `:272` resets a true
residual and stores the completion bit in the target pair; `:278` exports the
source pair's incoming bit. `src/lib/dpa.c:300` initializes that bit to
acceptance != false.

`ColourDag` exposes the same Shannon recursion. C's interned canonical true
and false IDs are tested here by exhaustive finite truth tables. Sharing,
node order and reduction do not affect these tests or the recursion's
denotation; the BDD representation boundary remains explicit. Every monitor
definition below is executable, including the constant tests and initial bit.
-/
namespace Tlsf.Dpa.Impl
variable {m : Nat}

/-- Finite colour valuations, used only for executable canonical constant tests. -/
def colourVectors : (m : Nat) → List (Fin m → Bool)
  | 0 => [Fin.elim0]
  | m+1 => (colourVectors m).flatMap (fun v => [Fin.cases false v, Fin.cases true v])

theorem colourVectors_complete (v : Fin m → Bool) : v ∈ colourVectors m := by
  induction m with
  | zero =>
    have he : v = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [colourVectors, he]
  | succ m ih =>
    apply List.mem_flatMap.mpr
    refine ⟨fun i => v i.succ, ih _, ?_⟩
    have he : v = Fin.cases (v 0) (fun i => v i.succ) := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [he]
    cases v 0 <;> simp

inductive ColourDag (m : Nat) where
  | leaf : Bool → ColourDag m
  | node : Fin m → ColourDag m → ColourDag m → ColourDag m
  deriving DecidableEq, Repr

/-- Low child first, as in C's `DpaClass`. -/
def ColourDag.eval : ColourDag m → Skeleton m
  | .leaf b, _ => b
  | .node i low high, v => if v i then high.eval v else low.eval v

def ColourDag.constant (b : Bool) (f : ColourDag m) : Bool :=
  (colourVectors m).all (fun v => f.eval v == b)

theorem ColourDag.constant_exact (b : Bool) (f : ColourDag m) :
    f.constant b = true ↔ ∀ v, f.eval v = b := by
  simp only [ColourDag.constant, List.all_eq_true, beq_iff_eq]
  exact ⟨fun h v => h v (colourVectors_complete v), fun h v _ => h v⟩

/-- Boolean operations on Shannon diagrams. C uses canonical BDD operations;
these executable operations have exactly the same Boolean denotations. -/
def ColourDag.conj : ColourDag m → ColourDag m → ColourDag m
  | .leaf false, _ => .leaf false
  | .leaf true, g => g
  | .node i low high, g => .node i (low.conj g) (high.conj g)

def ColourDag.disj : ColourDag m → ColourDag m → ColourDag m
  | .leaf false, g => g
  | .leaf true, _ => .leaf true
  | .node i low high, g => .node i (low.disj g) (high.disj g)

theorem ColourDag.conj_eval (f g : ColourDag m) (v : Fin m → Bool) :
    (f.conj g).eval v = (f.eval v && g.eval v) := by
  induction f with
  | leaf b => cases b <;> rfl
  | node i low high il ih => cases h : v i <;> simp [conj, eval, h, il, ih]

theorem ColourDag.disj_eval (f g : ColourDag m) (v : Fin m → Bool) :
    (f.disj g).eval v = (f.eval v || g.eval v) := by
  induction f with
  | leaf b => cases b <;> rfl
  | node i low high il ih => cases h : v i <;> simp [disj, eval, h, il, ih]

/-- `seen_colours`: marked variables choose high; unmarked variables retain
both recursively mapped children. Canonical interning is represented by eval. -/
def seenColours : ColourDag m → (Fin m → Bool) → ColourDag m
  | .leaf b, _ => .leaf b
  | .node i low high, colours =>
    if colours i then seenColours high colours
    else .node i (seenColours low colours) (seenColours high colours)

def colourUnion (a b : Fin m → Bool) : Fin m → Bool := fun i => a i || b i

theorem seenColours_exact (f : ColourDag m) (colours v : Fin m → Bool) :
    (seenColours f colours).eval v = f.eval (colourUnion v colours) := by
  induction f with
  | leaf b => rfl
  | node i low high il ih =>
    cases hc : colours i <;> cases hv : v i <;>
      simp [seenColours, ColourDag.eval, colourUnion, hc, hv, il, ih]

/-- A positive Boolean acceptance is monotone in its Inf-colour arguments. -/
def PositiveColours (β : Skeleton m) : Prop :=
  ∀ a b, Subset a b → β a = true → β b = true

/-- The acceptance grammar in `src/lib/dpa_formula.c:622`: constants,
positive Π₂ component colours, and Boolean conjunction/disjunction. C disables
cached-dual sharing for this grammar (`src/lib/dpa_dela.c:99`). The component
store/constructor bridge is separate from this round-monitor theorem. -/
inductive PositiveAcceptance (m : Nat) where
  | constant : Bool → PositiveAcceptance m
  | colour : Fin m → PositiveAcceptance m
  | conj : PositiveAcceptance m → PositiveAcceptance m → PositiveAcceptance m
  | disj : PositiveAcceptance m → PositiveAcceptance m → PositiveAcceptance m
  deriving DecidableEq, Repr

def PositiveAcceptance.compile : PositiveAcceptance m → ColourDag m
  | .constant b => .leaf b
  | .colour i => .node i (.leaf false) (.leaf true)
  | .conj f g => f.compile.conj g.compile
  | .disj f g => f.compile.disj g.compile

theorem PositiveAcceptance.positive (f : PositiveAcceptance m) :
    PositiveColours f.compile.eval := by
  induction f with
  | constant c => intro _ _ _ ha; exact ha
  | colour i =>
    intro a b hab ha
    have hi : a i = true := by simpa [compile, ColourDag.eval] using ha
    simp [compile, ColourDag.eval, hab i hi]
  | conj f g ihf ihg =>
    intro a b hab ha
    simp only [compile, ColourDag.conj_eval, Bool.and_eq_true] at ha ⊢
    exact ⟨ihf a b hab ha.1, ihg a b hab ha.2⟩
  | disj f g ihf ihg =>
    intro a b hab ha
    simp only [compile, ColourDag.disj_eval, Bool.or_eq_true] at ha ⊢
    exact ha.elim (fun h => Or.inl (ihf a b hab h)) (fun h => Or.inr (ihg a b hab h))

/-- Remember the residual acceptance and the incoming completion bit, which
must be part of the state key even when two residuals agree. -/
structure RoundState (m : Nat) where
  residual : ColourDag m
  incoming : Bool
  deriving DecidableEq, Repr

def roundInitial (β : ColourDag m) : RoundState m := ⟨β, !β.constant false⟩

def roundStep (β : ColourDag m) (s : RoundState m) (colours : Fin m → Bool) :
    RoundState m :=
  let residual := seenColours s.residual colours
  let complete := residual.constant true
  ⟨if complete then β else residual, complete⟩

structure RoundEdge (m : Nat) where
  target : RoundState m
  priority : Nat
  deriving DecidableEq, Repr

/-- Joint's Büchi leaf branch: target stores the new mark; priority reads
the old mark. The two fields must not be conflated. -/
def roundTransition (β : ColourDag m) (s : RoundState m) (colours : Fin m → Bool) :
    RoundEdge m := ⟨roundStep β s colours, if s.incoming then 1 else 0⟩

theorem incoming_state_split (β r : ColourDag m) (colours : Fin m → Bool) :
    (roundTransition β ⟨r, true⟩ colours).target =
      (roundTransition β ⟨r, false⟩ colours).target ∧
    (roundTransition β ⟨r, true⟩ colours).priority = 1 ∧
    (roundTransition β ⟨r, false⟩ colours).priority = 0 := by
  exact ⟨rfl, rfl, rfl⟩

def roundRun (β : ColourDag m) (colours : Nat → Fin m → Bool) : Nat → RoundState m
  | 0 => roundInitial β
  | n+1 => roundStep β (roundRun β colours n) (colours n)

def completedRounds (β : ColourDag m) (colours : Nat → Fin m → Bool) (n : Nat) : Bool :=
  (roundStep β (roundRun β colours n) (colours n)).incoming

/-- C emits this source-state bit, rather than the just-computed completion. -/
def incomingMarks (β : ColourDag m) (colours : Nat → Fin m → Bool) (n : Nat) : Bool :=
  (roundRun β colours n).incoming

/-- Auxiliary union-of-seen-colours implementation, used to prove the
residual implementation above. It is not substituted for it in the executable. -/
def roundSeen (β : Skeleton m) (colours : Nat → Fin m → Bool) : Nat → (Fin m → Bool)
  | 0 => fun _ => false
  | n+1 =>
    let seen := colourUnion (roundSeen β colours n) (colours n)
    if β seen then fun _ => false else seen

def unionCompleted (β : Skeleton m) (colours : Nat → Fin m → Bool) (n : Nat) : Bool :=
  β (colourUnion (roundSeen β colours n) (colours n))

private theorem union_left (a b : Fin m → Bool) : Subset a (colourUnion a b) := by
  intro i hi; simp [colourUnion, hi]

private theorem union_right (a b : Fin m → Bool) : Subset b (colourUnion a b) := by
  intro i hi; simp [colourUnion, hi]

private theorem union_subset {a b c : Fin m → Bool} (ha : Subset a c) (hb : Subset b c) :
    Subset (colourUnion a b) c := by
  intro i hi
  simp only [colourUnion, Bool.or_eq_true] at hi
  exact hi.elim (ha i) (hb i)

@[simp] private theorem union_empty (a : Fin m → Bool) :
    colourUnion a (fun _ => false) = a := by
  funext i; simp [colourUnion]

@[simp] private theorem empty_union (a : Fin m → Bool) :
    colourUnion (fun _ => false) a = a := by
  funext i; simp [colourUnion]

private theorem union_assoc (a b c : Fin m → Bool) :
    colourUnion (colourUnion a b) c = colourUnion a (colourUnion b c) := by
  funext i; exact Bool.or_assoc _ _ _

private theorem union_comm (a b : Fin m → Bool) : colourUnion a b = colourUnion b a := by
  funext i; exact Bool.or_comm _ _

/-- Substitution of seen colours reaches canonical true exactly when the
positive acceptance holds on those colours (all unseen colours false). -/
theorem seen_complete (β : ColourDag m) (hp : PositiveColours β.eval)
    (seen colours : Fin m → Bool) (s : RoundState m)
    (hs : ∀ v, s.residual.eval v = β.eval (colourUnion v seen)) :
    (seenColours s.residual colours).constant true =
      β.eval (colourUnion seen colours) := by
  apply Bool.eq_iff_iff.mpr
  rw [ColourDag.constant_exact]
  constructor
  · intro h
    have h0 := h (fun _ => false)
    simpa only [seenColours_exact, hs, empty_union, union_comm colours seen] using h0
  · intro h v
    rw [seenColours_exact, hs]
    apply hp _ _ ?_ h
    intro i hi
    simp only [colourUnion, Bool.or_eq_true] at hi ⊢
    exact hi.elim (fun h => Or.inr h) (fun h => Or.inl (Or.inr h))

/-- The executable C-shaped residual run and the union run agree at every
step, including reset. This quantifies over arbitrary colour streams. -/
theorem roundRun_residual (β : ColourDag m) (hp : PositiveColours β.eval)
    (colours : Nat → Fin m → Bool) (n : Nat) (v : Fin m → Bool) :
    (roundRun β colours n).residual.eval v =
      β.eval (colourUnion v (roundSeen β.eval colours n)) := by
  induction n generalizing v with
  | zero => simp [roundRun, roundInitial, roundSeen]
  | succ n ih =>
    have hc := seen_complete β hp (roundSeen β.eval colours n) (colours n)
      (roundRun β colours n) ih
    simp only [roundRun, roundStep, hc, roundSeen]
    split
    · simp
    · rw [seenColours_exact, ih]
      congr 1
      rw [union_assoc, union_comm (colours n)]

theorem completedRounds_exact (β : ColourDag m) (hp : PositiveColours β.eval)
    (colours : Nat → Fin m → Bool) :
    completedRounds β colours = unionCompleted β.eval colours := by
  funext n
  exact seen_complete β hp _ _ _ (roundRun_residual β hp colours n)

private theorem roundSeen_subset (β : Skeleton m) (colours : Nat → Fin m → Bool)
    (R : Fin m → Bool) (N : Nat) (hN : Subset (roundSeen β colours N) R)
    (hc : ∀ n, N ≤ n → Subset (colours n) R) (k : Nat) :
    Subset (roundSeen β colours (N+k)) R := by
  induction k with
  | zero => simpa using hN
  | succ k ih =>
    rw [Nat.add_succ, roundSeen]
    split
    · intro i hi; contradiction
    · exact union_subset ih (hc _ (Nat.le_add_right N k))

private theorem roundSeen_persistent (β : Skeleton m) (colours : Nat → Fin m → Bool)
    (N : Nat) (hf : ∀ n, N ≤ n → unionCompleted β colours n = false)
    (n : Nat) (hn : N ≤ n) (i : Fin m) (hi : colours n i = true) (k : Nat) :
    roundSeen β colours (n+1+k) i = true := by
  induction k with
  | zero =>
    change (if unionCompleted β colours n then (fun _ => false)
      else colourUnion (roundSeen β colours n) (colours n)) i = true
    rw [hf n hn]
    exact union_right _ _ i hi
  | succ k ih =>
    rw [Nat.add_succ]
    change (if unionCompleted β colours (n+1+k) then (fun _ => false)
      else colourUnion (roundSeen β colours (n+1+k)) (colours (n+1+k))) i = true
    rw [hf _ (by omega)]
    exact union_left _ _ i ih

/-- The liveness argument uses finitely many colours, not a bound on the
time between their occurrences. Alternating colours can complete conjunctions. -/
theorem unionCompleted_language (β : Skeleton m) (hp : PositiveColours β)
    (colours : Nat → Fin m → Bool) :
    Inf (unionCompleted β colours) ↔ EmersonLei β colours := by
  classical
  constructor
  · intro hi
    apply Classical.byContradiction
    intro hb
    have hb' : β (recurrentColours colours) = false := Bool.eq_false_iff.mpr hb
    obtain ⟨N, hN⟩ := recurrent_eventually_subset colours (recurrentColours colours)
      (fun _ h => h)
    obtain ⟨n, hn, hc⟩ := hi N
    have hreset : roundSeen β colours (n+1) = fun _ => false := by
      change (if unionCompleted β colours n then (fun _ => false)
        else colourUnion (roundSeen β colours n) (colours n)) = _
      rw [hc]; rfl
    obtain ⟨k, hk, hcomplete⟩ := hi (n+1)
    have hs : Subset (roundSeen β colours k) (recurrentColours colours) := by
      have hh := roundSeen_subset β colours (recurrentColours colours) (n+1)
        (by rw [hreset]; intro i hi; contradiction)
        (fun j hj => hN j (by omega)) (k-(n+1))
      simpa [Nat.add_sub_cancel' hk] using hh
    have ht := hp _ _ (union_subset hs (hN k (by omega))) hcomplete
    rw [hb'] at ht
    contradiction
  · intro he
    apply Classical.byContradiction
    intro hi
    obtain ⟨N, hN⟩ := (not_inf_iff_fin _).mp hi
    obtain ⟨M, hM⟩ := finite_eventually (List.finRange m)
      (fun i k => recurrentColours colours i = true → roundSeen β colours k i = true) (by
        intro i _
        by_cases hr : recurrentColours colours i = true
        · have hrec : Inf (fun n => colours n i) := by
            simpa [recurrentColours] using hr
          obtain ⟨n, hn, hc⟩ := hrec N
          refine ⟨n+1, fun k hk _ => ?_⟩
          have hh := roundSeen_persistent β colours N hN n hn i hc (k-(n+1))
          simpa [Nat.add_sub_cancel' hk] using hh
        · exact ⟨0, fun _ _ hh => False.elim (hr hh)⟩)
    have hs : Subset (recurrentColours colours) (roundSeen β colours (max N M)) :=
      fun i hi => hM _ (Nat.le_max_right _ _) i (by simp) hi
    have ht := hp _ (colourUnion (roundSeen β colours (max N M)) (colours (max N M)))
      (fun i hi => union_left _ _ i (hs i hi)) he
    have hf := hN (max N M) (Nat.le_max_left _ _)
    rw [unionCompleted, ht] at hf
    contradiction

/-- Main monitor theorem, about the executable residual walk and reset. -/
theorem completedRounds_language (β : ColourDag m) (hp : PositiveColours β.eval)
    (colours : Nat → Fin m → Bool) :
    Inf (completedRounds β colours) ↔ EmersonLei β.eval colours := by
  rw [completedRounds_exact β hp]
  exact unionCompleted_language β.eval hp colours

theorem incomingMarks_succ (β : ColourDag m) (colours : Nat → Fin m → Bool) (n : Nat) :
    incomingMarks β colours (n+1) = completedRounds β colours n := rfl

/-- The arbitrary finite initial bit and the one-step shift cannot affect
Inf acceptance. Source-state acceptance therefore equals edge completion. -/
theorem incomingMarks_inf (β : ColourDag m) (colours : Nat → Fin m → Bool) :
    Inf (incomingMarks β colours) ↔ Inf (completedRounds β colours) := by
  constructor
  · intro hi N
    obtain ⟨n, hn, hm⟩ := hi (N+1)
    refine ⟨n-1, by omega, ?_⟩
    have he : (n-1)+1 = n := by omega
    rw [← he, incomingMarks_succ] at hm
    exact hm
  · intro hi N
    obtain ⟨n, hn, hm⟩ := hi N
    exact ⟨n+1, by omega, by simpa only [incomingMarks_succ] using hm⟩

theorem incomingMarks_language (β : ColourDag m) (hp : PositiveColours β.eval)
    (colours : Nat → Fin m → Bool) :
    Inf (incomingMarks β colours) ↔ EmersonLei β.eval colours :=
  (incomingMarks_inf β colours).trans (completedRounds_language β hp colours)

/-- Numeric C priorities 0/1 use max-odd Büchi acceptance. The source mark is
1 on every outgoing edge of an accepting split state, and 0 otherwise. -/
def buchiPriority (β : ColourDag m) (colours : Nat → Fin m → Bool) (n : Nat) : Nat :=
  if incomingMarks β colours n then 1 else 0

theorem buchiPriority_exact (β : ColourDag m) (colours : Nat → Fin m → Bool) (n : Nat) :
    buchiPriority β colours n =
      (roundTransition β (roundRun β colours n) (colours n)).priority := rfl

theorem buchiPriority_language (β : ColourDag m) (hp : PositiveColours β.eval)
    (colours : Nat → Fin m → Bool) :
    MaxOdd (buchiPriority β colours) ↔ EmersonLei β.eval colours := by
  have he : MaxOdd (buchiPriority β colours) ↔ Inf (incomingMarks β colours) := by
    constructor
    · rintro ⟨k, hk, hi, _⟩ N
      have hk1 : k = 1 := by
        obtain ⟨n, _, he⟩ := hi 0
        cases hm : incomingMarks β colours n <;> simp [buchiPriority, hm] at he <;> omega
      obtain ⟨n, hn, he⟩ := hi N
      refine ⟨n, hn, ?_⟩
      cases hm : incomingMarks β colours n <;> simp_all [buchiPriority]
    · intro hi
      refine ⟨1, rfl, ?_, 0, ?_⟩
      · intro N
        obtain ⟨n, hn, hm⟩ := hi N
        exact ⟨n, hn, by simp [buchiPriority, hm]⟩
      · intro n _
        cases hm : incomingMarks β colours n <;> simp [buchiPriority, hm]
  exact he.trans (incomingMarks_language β hp colours)

/-- No monotonicity premise remains for the positive acceptance grammar. -/
theorem positive_buchi_language (β : PositiveAcceptance m)
    (colours : Nat → Fin m → Bool) :
    (Inf (completedRounds β.compile colours) ↔ EmersonLei β.compile.eval colours) ∧
    (Inf (incomingMarks β.compile colours) ↔ EmersonLei β.compile.eval colours) ∧
    (MaxOdd (buchiPriority β.compile colours) ↔ EmersonLei β.compile.eval colours) :=
  ⟨completedRounds_language β.compile β.positive colours,
   incomingMarks_language β.compile β.positive colours,
   buchiPriority_language β.compile β.positive colours⟩

end Tlsf.Dpa.Impl
