import TlsfProofs.Dpa.Validation.Construction
import TlsfProofs.Dpa.Validation.Equivalence

/-! Checked finite export of an executable symbolic machine. Exploration has
an explicit resource limit; exhaustion is failure. The independently checked
certificate covers the initial state and every transition of the returned
table, including terminal loops. Boolean class equality merges representatives
without identifying syntactically growing formulas. -/
namespace Tlsf.Dpa.Validation
variable {S K : Type} {alphabet : Nat}

structure Representatives (S : Type) where
  states : Array S
  nonempty : 0 < states.size

def Representatives.zero (r : Representatives S) : Fin r.states.size := ⟨0, r.nonempty⟩

def Representatives.locate (r : Representatives S) (eqb : S → S → Bool) (s : S) :
    Fin r.states.size :=
  ((List.finRange r.states.size).find? (fun i => eqb s r.states[i])).getD r.zero

def Representatives.parity (r : Representatives S) (A : Parity (Fin alphabet) S)
    (eqb : S → S → Bool) : Parity (Fin alphabet) (Fin r.states.size) where
  initial := r.zero
  step i a := let e := A.step r.states[i] a; (r.locate eqb e.1, e.2)

def Representatives.closed (r : Representatives S) (A : Parity (Fin alphabet) S)
    (eqb : S → S → Bool) : Bool :=
  eqb r.states[r.zero] A.initial &&
    (List.finRange r.states.size).all (fun i => (List.finRange alphabet).all (fun a =>
      eqb (A.step r.states[i] a).1 r.states[r.locate eqb (A.step r.states[i] a).1]))

/-- A Boolean equality test need only identify semantic keys. No equality of
formula representatives or state isomorphism is assumed. -/
theorem Representatives.parity_language (r : Representatives S)
    (A : Parity (Fin alphabet) S) (eqb : S → S → Bool) (key : S → K)
    (he : ∀ s t, eqb s t = true ↔ key s = key t)
    (hs : ∀ s t a, key s = key t →
      key (A.step s a).1 = key (A.step t a).1 ∧ (A.step s a).2 = (A.step t a).2)
    (hc : r.closed A eqb = true) (w : Nat → Fin alphabet) :
    (r.parity A eqb).Accepts w ↔ A.Accepts w := by
  obtain ⟨hi, ht⟩ := Bool.and_eq_true_iff.mp hc
  have hr (n : Nat) : key r.states[(r.parity A eqb).run w n] = key (A.run w n) := by
    induction n with
    | zero => exact (he _ _).mp hi
    | succ n ih =>
      have hh := (List.all_eq_true.mp ((List.all_eq_true.mp ht)
        ((r.parity A eqb).run w n) (by simp))) (w n) (by simp)
      exact ((he _ _).mp hh).symm.trans (hs _ _ _ ih).1
  have hp : (r.parity A eqb).priorities w = A.priorities w := by
    funext n
    exact (hs _ _ _ (hr n)).2
  change MaxOdd _ ↔ MaxOdd _
  rw [hp]

/-- Breadth-first discovery, in increasing letter order. The certificate is
checked separately, so no exploration implementation is in the proof boundary. -/
def discover (step : S → Fin alphabet → S) (eqb : S → S → Bool) (prepare : S → S) :
    Nat → Nat → Array S → Array S
  | 0, _, states => states
  | fuel+1, cursor, states =>
    if h : cursor < states.size then
      let next := (List.finRange alphabet).foldl (fun xs a =>
        let t := prepare (step states[cursor] a)
        if xs.any (eqb t) then xs else xs.push t) states
      discover step eqb prepare fuel (cursor+1) next
    else states

def exportParity (A : Parity (Fin alphabet) S) (eqb : S → S → Bool) (fuel : Nat)
    (prepare : S → S := id) :
    Option (Representatives S) :=
  let states := discover (fun s a => (A.step s a).1) eqb prepare fuel 0 #[prepare A.initial]
  if hn : 0 < states.size then
    let r : Representatives S := ⟨states, hn⟩
    if r.closed A eqb then some r else none
  else none

theorem exportParity_closed (A : Parity (Fin alphabet) S) (eqb : S → S → Bool)
    (fuel : Nat) (r : Representatives S) (prepare : S → S)
    (h : exportParity A eqb fuel prepare = some r) :
    r.closed A eqb = true := by
  unfold exportParity at h
  dsimp only at h
  split at h
  · split at h
    · cases h; assumption
    · contradiction
  · contradiction

theorem exportParity_language (A : Parity (Fin alphabet) S) (eqb : S → S → Bool)
    (key : S → K) (he : ∀ s t, eqb s t = true ↔ key s = key t)
    (hs : ∀ s t a, key s = key t →
      key (A.step s a).1 = key (A.step t a).1 ∧ (A.step s a).2 = (A.step t a).2)
    (fuel : Nat) (r : Representatives S) (prepare : S → S)
    (h : exportParity A eqb fuel prepare = some r)
    (w : Nat → Fin alphabet) : (r.parity A eqb).Accepts w ↔ A.Accepts w :=
  r.parity_language A eqb key he hs (exportParity_closed A eqb fuel r prepare h) w

def Representatives.buchi (r : Representatives S) (A : Buchi (Fin alphabet) S)
    (eqb : S → S → Bool) : Buchi (Fin alphabet) (Fin r.states.size) where
  initial := r.zero
  step i a := r.locate eqb (A.step r.states[i] a)
  accepting i := A.accepting r.states[i]

theorem exportBuchi_language (A : Buchi (Fin alphabet) S) (eqb : S → S → Bool)
    (key : S → K) (he : ∀ s t, eqb s t = true ↔ key s = key t)
    (hs : ∀ s t a, key s = key t →
      key (A.step s a) = key (A.step t a) ∧ A.accepting s = A.accepting t)
    (fuel : Nat) (r : Representatives S) (prepare : S → S)
    (h : exportParity A.toParity eqb fuel prepare = some r)
    (w : Nat → Fin alphabet) : (r.buchi A eqb).Accepts w ↔ A.Accepts w := by
  have hc : ∀ s t a, key s = key t →
      key (A.toParity.step s a).1 = key (A.toParity.step t a).1 ∧
        (A.toParity.step s a).2 = (A.toParity.step t a).2 := by
    intro s t a hh
    have ht := hs s t a hh
    exact ⟨ht.1, by simp only [Buchi.toParity, ht.2]⟩
  exact ((r.buchi A eqb).toParity_language w).symm.trans
    ((exportParity_language A.toParity eqb key he hc fuel r prepare h w).trans (A.toParity_language w))

end Tlsf.Dpa.Validation

namespace Tlsf.Dpa.Impl
variable {ap : Nat}

def State.same (s t : State ap) : Bool :=
  equivalent s.rejecting t.rejecting && equivalent s.all t.all

def State.representative (s : State ap) : State ap :=
  ⟨reduceProp s.all, reduceProp s.rejecting⟩

theorem State.representative_exact (s : State ap) : s.representative.denote = s.denote := by
  cases s
  simp [State.representative, State.denote, reduceProp_class]

theorem State.same_exact (s t : State ap) : s.same t = true ↔ s.denote = t.denote := by
  simp only [State.same, Bool.and_eq_true, equivalent_exact]
  constructor
  · rintro ⟨hr, ha⟩; cases s; cases t; simp_all [State.denote]
  · intro h; exact ⟨congrArg Pair.rejecting h, congrArg Pair.all h⟩

theorem State.transition_congr (s t : State ap) (v : Letter (Fin ap))
    (h : s.denote = t.denote) :
    (transition v s).target.denote = (transition v t).target.denote ∧
      (transition v s).mark = (transition v t).mark := by
  have he : (transition v s).denote = (transition v t).denote := by
    rw [transition_exact, transition_exact, h]
  exact ⟨congrArg Dpa.Edge.target he, congrArg Dpa.Edge.mark he⟩

def Assembly.configurationSame (r : Assembly ap) (s t : Configuration r) : Bool :=
  (List.finRange r.store.length).all (fun i => (s i).same (t i))

def Assembly.configurationKey (r : Assembly ap) (s : Configuration r) :
    Fin r.store.length → Pair ap := fun i => (s i).denote

theorem Assembly.configurationSame_exact (r : Assembly ap) (s t : Configuration r) :
    r.configurationSame s t = true ↔ r.configurationKey s = r.configurationKey t := by
  simp only [Assembly.configurationSame, List.all_eq_true, State.same_exact]
  exact ⟨fun h => funext (fun i => h i (by simp)), fun h i _ => congrFun h i⟩

theorem Assembly.productStep_congr (r : Assembly ap) (s t : Configuration r)
    (v : Letter (Fin ap)) (h : r.configurationKey s = r.configurationKey t) :
    r.configurationKey (r.productStep s v).1 = r.configurationKey (r.productStep t v).1 ∧
      (r.productStep s v).2 = (r.productStep t v).2 := by
  simp only [Assembly.productStep_exact]
  constructor
  · funext i; exact (State.transition_congr _ _ v (congrFun h i)).1
  · funext i; exact (State.transition_congr _ _ v (congrFun h i)).2

abbrev Alphabet (ap : Nat) := Fin (colourVectors ap).length
def decode (a : Alphabet ap) : Letter (Fin ap) := (colourVectors ap)[a.val]

@[noinline] def Assembly.finiteParitySource (r : Assembly ap) :
    Validation.Parity (Alphabet ap) (Configuration r × List Nat) :=
  let source := r.parity
  ⟨source.initial, fun s a => source.step s (decode a)⟩

def Assembly.paritySame (r : Assembly ap) (s t : Configuration r × List Nat) : Bool :=
  decide (s.2 = t.2) && r.configurationSame s.1 t.1

def Assembly.parityKey (r : Assembly ap) (s : Configuration r × List Nat) :=
  (r.configurationKey s.1, s.2)

theorem Assembly.paritySame_exact (r : Assembly ap) (s t : Configuration r × List Nat) :
    r.paritySame s t = true ↔ r.parityKey s = r.parityKey t := by
  simp only [Assembly.paritySame, Bool.and_eq_true, Assembly.configurationSame_exact,
    decide_eq_true_eq, Assembly.parityKey, Prod.mk.injEq]
  exact and_comm

theorem Assembly.finiteParitySource_congr (r : Assembly ap)
    (s t : Configuration r × List Nat) (a : Alphabet ap)
    (h : r.parityKey s = r.parityKey t) :
    r.parityKey (r.finiteParitySource.step s a).1 =
        r.parityKey (r.finiteParitySource.step t a).1 ∧
      (r.finiteParitySource.step s a).2 = (r.finiteParitySource.step t a).2 := by
  have hh := Prod.mk.inj h
  have hp := r.productStep_congr s.1 t.1 (decode a) hh.1
  simp [Assembly.finiteParitySource, Assembly.parity, Assembly.parityKey, hp.1, hp.2, hh.2]

/-- Materialize all coordinates before storing the pair. Returning a data pair
keeps the vector outside the coordinate function in compiled code. This does
not memoize construction calls or model any C cache. Closure still checks the
prepared representatives independently. -/
@[noinline] def Assembly.prepareParity (r : Assembly ap) (s : Configuration r × List Nat) :
    Configuration r × List Nat :=
  let coordinates := Vector.ofFn (fun i => (s.1 i).representative)
  (fun i => coordinates[i], s.2)

theorem Assembly.prepareParity_exact (r : Assembly ap) (s : Configuration r × List Nat) :
    r.parityKey (r.prepareParity s) = r.parityKey s := by
  apply Prod.ext
  · funext i
    change ((Vector.ofFn (fun j => (s.1 j).representative))[i]).denote = (s.1 i).denote
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact State.representative_exact _
  · rfl

def Assembly.exportParity (r : Assembly ap) (fuel : Nat) :=
  Validation.exportParity r.finiteParitySource r.paritySame fuel r.prepareParity

theorem Assembly.exportParity_language (r : Assembly ap) (fuel : Nat)
    (table : Validation.Representatives (Configuration r × List Nat))
    (h : r.exportParity fuel = some table) (w : Nat → Alphabet ap) :
    (table.parity r.finiteParitySource r.paritySame).Accepts w ↔
      r.parity.Accepts (fun n => decode (w n)) := by
  have he := Validation.exportParity_language r.finiteParitySource r.paritySame r.parityKey
    r.paritySame_exact r.finiteParitySource_congr fuel table r.prepareParity h w
  have hr (n : Nat) : r.finiteParitySource.run w n =
      r.parity.run (fun n => decode (w n)) n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Validation.Parity.run, ih]; rfl
  have hp : r.finiteParitySource.priorities w =
      r.parity.priorities (fun n => decode (w n)) := by
    funext n; simp only [Validation.Parity.priorities, hr]; rfl
  exact he.trans (by unfold Validation.Parity.Accepts; rw [hp])

@[noinline] def Assembly.finiteBuchiSource (r : Assembly ap) :
    Validation.Buchi (Alphabet ap) (Configuration r × RoundState r.store.length) :=
  let source := r.buchi
  ⟨source.initial, fun s a => source.step s (decode a), source.accepting⟩

def Assembly.buchiSame (r : Assembly ap)
    (s t : Configuration r × RoundState r.store.length) : Bool :=
  decide (s.2 = t.2) && r.configurationSame s.1 t.1

def Assembly.buchiKey (r : Assembly ap) (s : Configuration r × RoundState r.store.length) :=
  (r.configurationKey s.1, s.2)

theorem Assembly.buchiSame_exact (r : Assembly ap)
    (s t : Configuration r × RoundState r.store.length) :
    r.buchiSame s t = true ↔ r.buchiKey s = r.buchiKey t := by
  simp only [Assembly.buchiSame, Bool.and_eq_true, Assembly.configurationSame_exact,
    decide_eq_true_eq, Assembly.buchiKey, Prod.mk.injEq]
  exact and_comm

theorem Assembly.finiteBuchiSource_congr (r : Assembly ap)
    (s t : Configuration r × RoundState r.store.length) (a : Alphabet ap)
    (h : r.buchiKey s = r.buchiKey t) :
    r.buchiKey (r.finiteBuchiSource.step s a) = r.buchiKey (r.finiteBuchiSource.step t a) ∧
      r.finiteBuchiSource.accepting s = r.finiteBuchiSource.accepting t := by
  have hh := Prod.mk.inj h
  have hp := r.productStep_congr s.1 t.1 (decode a) hh.1
  simp [Assembly.finiteBuchiSource, Assembly.buchi, Assembly.buchiKey, hp.1, hp.2, hh.2]

@[noinline] def Assembly.prepareBuchi (r : Assembly ap)
    (s : Configuration r × RoundState r.store.length) :
    Configuration r × RoundState r.store.length :=
  let coordinates := Vector.ofFn (fun i => (s.1 i).representative)
  (fun i => coordinates[i], s.2)

theorem Assembly.prepareBuchi_exact (r : Assembly ap)
    (s : Configuration r × RoundState r.store.length) :
    r.buchiKey (r.prepareBuchi s) = r.buchiKey s := by
  apply Prod.ext
  · funext i
    change ((Vector.ofFn (fun j => (s.1 j).representative))[i]).denote = (s.1 i).denote
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact State.representative_exact _
  · rfl

def Assembly.exportBuchi (r : Assembly ap) (fuel : Nat) :=
  Validation.exportParity r.finiteBuchiSource.toParity r.buchiSame fuel r.prepareBuchi

theorem Assembly.exportBuchi_language (r : Assembly ap) (fuel : Nat)
    (table : Validation.Representatives (Configuration r × RoundState r.store.length))
    (h : r.exportBuchi fuel = some table) (w : Nat → Alphabet ap) :
    (table.buchi r.finiteBuchiSource r.buchiSame).Accepts w ↔
      r.buchi.Accepts (fun n => decode (w n)) := by
  have he := Validation.exportBuchi_language r.finiteBuchiSource r.buchiSame r.buchiKey
    r.buchiSame_exact r.finiteBuchiSource_congr fuel table r.prepareBuchi h w
  have hr (n : Nat) : r.finiteBuchiSource.run w n =
      r.buchi.run (fun n => decode (w n)) n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Validation.Buchi.run, ih]; rfl
  exact he.trans (by change Inf _ ↔ Inf _; simp only [hr]; rfl)

/-- Every successful finite export is covered by the admitted construction's
language theorem. A missing table or failed positivity check is a validation
failure, never an accepted validation verdict. -/
theorem uncached_finite_construction_language (rank atomRank : Formula (Fin ap) → Nat)
    (f : Formula (Fin ap)) (ha : transportedResearchCheck rank f = true)
    (r : Assembly ap) (hc : construct rank atomRank f = some r) :
    (∀ fuel table, r.exportParity fuel = some table → ∀ w,
      (table.parity r.finiteParitySource r.paritySame).Accepts w ↔
        Sat none (fun n => decode (w n)) f 0) ∧
    (positiveb r.skeleton = true → ∀ fuel table, r.exportBuchi fuel = some table → ∀ w,
      (table.buchi r.finiteBuchiSource r.buchiSame).Accepts w ↔
        Sat none (fun n => decode (w n)) f 0) := by
  obtain ⟨r', hc', hp, hb⟩ := uncached_construction_language rank atomRank f ha
  have he : r' = r := Option.some.inj (hc'.symm.trans hc)
  subst r'
  exact ⟨fun fuel table ht w => (r.exportParity_language fuel table ht w).trans (hp _),
    fun hpos fuel table ht w => (r.exportBuchi_language fuel table ht w).trans (hb hpos _)⟩

end Tlsf.Dpa.Impl
