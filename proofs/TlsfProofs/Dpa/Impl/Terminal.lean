import TlsfProofs.Dpa.Impl.Assembly
import TlsfProofs.Dpa.Impl.Buchi
import TlsfProofs.Dpa.Refinements

/-!
# Executable terminal product shortcut

`src/lib/dpa_dela.c:170` substitutes only available terminal target pairs,
leaving unavailable or nonterminal components symbolic. The epoch memo uses
canonical class keys. `:257` chooses the reserved absorbing state exactly
when the resulting class is constant; `src/lib/dpa.c:536` supplies its loop.
The decoded DAG reference permits either order of the two recursive ITE
arguments. BDD identities, numeric state IDs and epoch overflow remain
representation assumptions. This shortcut is disabled in C's Büchi mode.
-/
namespace Tlsf.Dpa.Impl
variable {ap m : Nat}

def colourDagEquivalent (f g : ColourDag m) : Bool :=
  (colourVectors m).all (fun v => f.eval v == g.eval v)

theorem colourDagEquivalent_exact (f g : ColourDag m) :
    colourDagEquivalent f g = true ↔ ∀ v, f.eval v = g.eval v := by
  simp only [colourDagEquivalent, List.all_eq_true, beq_iff_eq]
  exact ⟨fun h v => h v (colourVectors_complete v), fun h v _ => h v⟩

structure TerminalEntry (m : Nat) where
  epoch : Nat
  source : ColourDag m
  residual : ColourDag m

abbrev TerminalMemo (m : Nat) := List (TerminalEntry m)

def TerminalMemo.Valid (known : Fin m → Option Bool) (epoch : Nat)
    (memo : TerminalMemo m) : Prop :=
  ∀ e, e ∈ memo → e.epoch = epoch →
    ∀ v, e.residual.eval v = e.source.eval (fillConstants known v)

theorem TerminalMemo.fresh_valid (known : Fin m → Option Bool) (epoch : Nat)
    (memo : TerminalMemo m) (hfresh : ∀ e, e ∈ memo → e.epoch ≠ epoch) :
    memo.Valid known epoch := by
  intro e he hh
  exact False.elim (hfresh e he hh)

theorem TerminalMemo.empty_valid (known : Fin m → Option Bool) (epoch : Nat) :
    TerminalMemo.Valid known epoch ([] : TerminalMemo m) := by
  intro e he
  simp at he

def lookupTerminal (epoch : Nat) (f : ColourDag m) : TerminalMemo m → Option (ColourDag m)
  | [] => none
  | e :: memo =>
    if e.epoch == epoch && colourDagEquivalent e.source f then some e.residual
    else lookupTerminal epoch f memo

theorem lookupTerminal_spec (known : Fin m → Option Bool) (epoch : Nat)
    (memo : TerminalMemo m) (hm : memo.Valid known epoch)
    (he : lookupTerminal epoch f memo = some r) :
    ∀ v, r.eval v = f.eval (fillConstants known v) := by
  induction memo with
  | nil => simp [lookupTerminal] at he
  | cons e memo ih =>
    simp only [lookupTerminal] at he
    split at he
    · rename_i h
      cases Option.some.inj he
      obtain ⟨hepoch, hsource⟩ := Bool.and_eq_true_iff.mp h
      intro v
      exact (hm e (by simp) (beq_iff_eq.mp hepoch) v).trans
        ((colourDagEquivalent_exact _ _).mp hsource _)
    · exact ih (fun e he => hm e (by simp [he])) he

def rememberTerminal (epoch : Nat) (f r : ColourDag m) (memo : TerminalMemo m) :
    TerminalMemo m := ⟨epoch, f, r⟩ :: memo

theorem rememberTerminal_valid (known : Fin m → Option Bool) (epoch : Nat)
    (memo : TerminalMemo m) (hm : memo.Valid known epoch)
    (he : ∀ v, r.eval v = f.eval (fillConstants known v)) :
    (rememberTerminal epoch f r memo).Valid known epoch := by
  intro e hh hep
  rcases List.mem_cons.mp hh with rfl | hh
  · exact he
  · exact hm e hh hep

def terminalCondition (highFirst : ColourDag m → Bool) (epoch : Nat)
    (known : Fin m → Option Bool) : ColourDag m → TerminalMemo m → ColourDag m × TerminalMemo m
  | .leaf b, memo => (.leaf b, memo)
  | .node i low high, memo =>
    match lookupTerminal epoch (.node i low high) memo with
    | some r => (r, memo)
    | none =>
      let r := match known i with
        | some false => terminalCondition highFirst epoch known low memo
        | some true => terminalCondition highFirst epoch known high memo
        | none =>
          if highFirst (.node i low high) then
            let h := terminalCondition highFirst epoch known high memo
            let l := terminalCondition highFirst epoch known low h.2
            (.node i l.1 h.1, l.2)
          else
            let l := terminalCondition highFirst epoch known low memo
            let h := terminalCondition highFirst epoch known high l.2
            (.node i l.1 h.1, h.2)
      (r.1, rememberTerminal epoch (.node i low high) r.1 r.2)

theorem terminalCondition_spec (highFirst : ColourDag m → Bool) (epoch : Nat)
    (known : Fin m → Option Bool) (f : ColourDag m) (memo : TerminalMemo m)
    (hm : memo.Valid known epoch) :
    let r := terminalCondition highFirst epoch known f memo
    r.2.Valid known epoch ∧ ∀ v, r.1.eval v = f.eval (fillConstants known v) := by
  induction f generalizing memo with
  | leaf b => exact ⟨hm, fun _ => rfl⟩
  | node i low high il ih =>
    simp only [terminalCondition]
    cases he : lookupTerminal epoch (.node i low high) memo with
    | some r => exact ⟨hm, lookupTerminal_spec known epoch memo hm he⟩
    | none =>
      simp only
      have finish (r : ColourDag m × TerminalMemo m) (hr : r.2.Valid known epoch)
          (hl : ∀ v, r.1.eval v = (ColourDag.node i low high).eval (fillConstants known v)) :
          (rememberTerminal epoch (.node i low high) r.1 r.2).Valid known epoch ∧
            ∀ v, r.1.eval v = (ColourDag.node i low high).eval (fillConstants known v) :=
        ⟨rememberTerminal_valid known epoch r.2 hr hl, hl⟩
      cases hk : known i with
      | some b =>
        cases b
        · obtain ⟨hl, heval⟩ := il memo hm
          exact finish _ hl (fun v => by simpa [ColourDag.eval, fillConstants, hk] using heval v)
        · obtain ⟨hh, heval⟩ := ih memo hm
          exact finish _ hh (fun v => by simpa [ColourDag.eval, fillConstants, hk] using heval v)
      | none =>
        simp only
        split
        · obtain ⟨hh, heh⟩ := ih memo hm
          obtain ⟨hl, hel⟩ := il _ hh
          apply finish (.node i
            (terminalCondition highFirst epoch known low
              (terminalCondition highFirst epoch known high memo).2).1
            (terminalCondition highFirst epoch known high memo).1,
            (terminalCondition highFirst epoch known low
              (terminalCondition highFirst epoch known high memo).2).2) hl
          intro v
          cases hv : v i <;> simp [ColourDag.eval, fillConstants, hk, hv, hel, heh]
        · obtain ⟨hl, hel⟩ := il memo hm
          obtain ⟨hh, heh⟩ := ih _ hl
          apply finish (.node i
            (terminalCondition highFirst epoch known low memo).1
            (terminalCondition highFirst epoch known high
              (terminalCondition highFirst epoch known low memo).2).1,
            (terminalCondition highFirst epoch known high
              (terminalCondition highFirst epoch known low memo).2).2) hh
          intro v
          cases hv : v i <;> simp [ColourDag.eval, fillConstants, hk, hv, hel, heh]

def terminalConstant (f : ColourDag m) : Option Bool :=
  if f.constant false then some false else if f.constant true then some true else none

theorem terminalConstant_spec (f : ColourDag m) (he : terminalConstant f = some b) :
    ∀ v, f.eval v = b := by
  unfold terminalConstant at he
  split at he
  · rename_i hf
    cases Option.some.inj he
    exact (ColourDag.constant_exact _ _).mp hf
  · split at he
    · rename_i ht
      cases Option.some.inj he
      exact (ColourDag.constant_exact _ _).mp ht
    · simp at he

def terminalShortcut (highFirst : ColourDag m → Bool) (epoch : Nat)
    (known : Fin m → Option Bool) (f : ColourDag m) (memo : TerminalMemo m) :
    Option Bool × TerminalMemo m :=
  let r := terminalCondition highFirst epoch known f memo
  (terminalConstant r.1, r.2)

def productTerminalShortcut (buchi : Bool) (highFirst : ColourDag m → Bool) (epoch : Nat)
    (known : Fin m → Option Bool) (f : ColourDag m) (memo : TerminalMemo m) :
    Option Bool × TerminalMemo m :=
  if buchi then (none, memo) else terminalShortcut highFirst epoch known f memo

theorem productTerminalShortcut_buchi (highFirst : ColourDag m → Bool) (epoch : Nat)
    (known : Fin m → Option Bool) (f : ColourDag m) (memo : TerminalMemo m) :
    productTerminalShortcut true highFirst epoch known f memo = (none, memo) := rfl

theorem productTerminalShortcut_success (buchi : Bool) (highFirst : ColourDag m → Bool)
    (epoch : Nat) (known : Fin m → Option Bool) (f : ColourDag m) (memo : TerminalMemo m)
    (he : (productTerminalShortcut buchi highFirst epoch known f memo).1 = some b) :
    buchi = false ∧ (terminalShortcut highFirst epoch known f memo).1 = some b := by
  cases buchi
  · exact ⟨rfl, he⟩
  · simp [productTerminalShortcut] at he

theorem terminalShortcut_spec (highFirst : ColourDag m → Bool) (epoch : Nat)
    (known : Fin m → Option Bool) (f : ColourDag m) (memo : TerminalMemo m)
    (hm : memo.Valid known epoch)
    (he : (terminalShortcut highFirst epoch known f memo).1 = some b) :
    (terminalShortcut highFirst epoch known f memo).2.Valid known epoch ∧
      ∀ v, f.eval (fillConstants known v) = b := by
  obtain ⟨hv, hr⟩ := terminalCondition_spec highFirst epoch known f memo hm
  exact ⟨hv, fun v => (hr v).symm.trans (terminalConstant_spec _ he v)⟩

/-- The all-field alone determines a constant. Unavailable or nonterminal
target pairs remain unknown, independently of their rejecting fields. -/
def terminalValue (s : State ap) : Option Bool :=
  if equivalent s.all .ff then some false
  else if equivalent s.all .tt then some true else none

theorem terminalValue_spec (s : State ap) (he : terminalValue s = some b) :
    s.denote.all = if b then Class.top else Class.bot := by
  unfold terminalValue at he
  split at he
  · rename_i hf
    cases Option.some.inj he
    exact (equivalent_exact _ _).mp hf
  · split at he
    · rename_i ht
      cases Option.some.inj he
      exact (equivalent_exact _ _).mp ht
    · simp at he

def partialTerminalValues (targets : Fin m → Option (State ap)) (i : Fin m) : Option Bool :=
  (targets i).bind terminalValue

theorem partialTerminalValues_sound (targets : Fin m → Option (State ap))
    (xs : Fin m → Class ap) (w : Word (Fin ap)) (N : Nat)
    (htargets : ∀ i s, targets i = some s → s.denote = Dpa.run (xs i) w N) :
    ∀ i b, partialTerminalValues targets i = some b →
      (Dpa.run (xs i) w N).all = if b then Class.top else Class.bot := by
  intro i b he
  obtain ⟨s, hs, hb⟩ := Option.bind_eq_some_iff.mp he
  rw [← htargets i s hs]
  exact terminalValue_spec s hb

/-- The actual executable terminal test supplies the constant-substitution
hypothesis of terminal_product_decided, including complemented colours. -/
theorem terminalShortcut_product_language (highFirst : ColourDag m → Bool) (epoch : Nat)
    (f : ColourDag m) (targets : Fin m → Option (State ap)) (memo : TerminalMemo m)
    (hm : memo.Valid (partialTerminalValues targets) epoch)
    (he : (terminalShortcut highFirst epoch (partialTerminalValues targets) f memo).1 = some b)
    (xs : Fin m → Class ap) (w : Word (Fin ap)) (N : Nat)
    (htargets : ∀ i s, targets i = some s → s.denote = Dpa.run (xs i) w N) :
    EmersonLei f.eval (productColours xs w) ↔ b = true :=
  terminal_product_decided xs f.eval w N (partialTerminalValues targets) b
    (partialTerminalValues_sound targets xs w N htargets)
    (terminalShortcut_spec highFirst epoch _ f memo hm he).2

def terminalPriority (m : Nat) (b : Bool) : Nat := exportBound m - if b then 0 else 1

theorem terminalPriority_dual (m : Nat) (b : Bool) :
    exportBound m - terminalPriority m b = if b then 0 else 1 := by
  have hb := exportBound_large m
  cases b <;> simp only [terminalPriority, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem terminal_minEven (p : Nat → Nat) (N : Nat) (b : Bool)
    (hp : ∀ n, N ≤ n → p n = if b then 0 else 1) : MinEven p ↔ b = true := by
  constructor
  · rintro ⟨k, hk, hi, _⟩
    obtain ⟨n, hn, he⟩ := hi N
    have hh := hp n hn
    cases b <;> simp_all <;> omega
  · intro hb
    subst b
    refine ⟨0, rfl, ?_, N, fun _ _ => Nat.zero_le _⟩
    intro M
    exact ⟨max M N, Nat.le_max_left _ _, hp _ (Nat.le_max_right _ _)⟩

theorem terminalShortcut_parity (highFirst : ColourDag m → Bool) (epoch : Nat)
    (f : ColourDag m) (targets : Fin m → Option (State ap)) (memo : TerminalMemo m)
    (hm : memo.Valid (partialTerminalValues targets) epoch)
    (he : (terminalShortcut highFirst epoch (partialTerminalValues targets) f memo).1 = some b)
    (xs : Fin m → Class ap) (w : Word (Fin ap)) (N : Nat)
    (htargets : ∀ i s, targets i = some s → s.denote = Dpa.run (xs i) w N)
    (T : ZTree f.eval (fullColours m)) (p : Nat → Nat)
    (hp : ∀ n, N ≤ n → p n = terminalPriority m b) :
    (MaxOdd p ↔ EmersonLei f.eval (productColours xs w)) ∧
    (MaxOdd p ↔ MaxOdd (fun n => exportBound m - treePriority T (productColours xs w) n)) := by
  have ha : MaxOdd p ↔ b = true := by
    apply absorbing_maxOdd p (exportBound m) N b (exportBound_odd m)
    intro n hn
    rw [hp n hn]
    cases b <;> simp [terminalPriority]
  have hl := terminalShortcut_product_language highFirst epoch f targets memo hm he xs w N htargets
  exact ⟨ha.trans hl.symm, (ha.trans hl.symm).trans (tree_maxOdd T _).symm⟩

/-- Once a constructed product presentation is supplied, an executable
shortcut preserves its input language in both parity orientations. Earlier
priorities, including the entering edge, need no agreement with a tree. -/
theorem terminalShortcut_input_language (highFirst : ColourDag m → Bool) (epoch : Nat)
    (f : ColourDag m) (targets : Fin m → Option (State ap)) (memo : TerminalMemo m)
    (hm : memo.Valid (partialTerminalValues targets) epoch)
    (he : (terminalShortcut highFirst epoch (partialTerminalValues targets) f memo).1 = some b)
    (xs : Fin m → Class ap) (χ : Formula (Fin ap)) (hx : ProductPresentation χ xs f.eval)
    (w : Word (Fin ap)) (N : Nat)
    (htargets : ∀ i s, targets i = some s → s.denote = Dpa.run (xs i) w N)
    (p : Nat → Nat) (hp : ∀ n, N ≤ n → p n = terminalPriority m b) :
    (MaxOdd p ↔ Sat none w χ 0) ∧
    (MinEven (fun n => exportBound m - p n) ↔ Sat none w χ 0) := by
  have hl := (terminalShortcut_product_language highFirst epoch f targets memo hm he
    xs w N htargets).symm.trans
    ((product_language xs f.eval w (fun i => hx.1 i w)).trans (hx.2 w))
  constructor
  · apply Iff.trans ?_ hl
    apply absorbing_maxOdd p (exportBound m) N b (exportBound_odd m)
    intro n hn
    rw [hp n hn]
    cases b <;> simp [terminalPriority]
  · apply Iff.trans ?_ hl
    apply terminal_minEven _ N b
    intro n hn
    rw [hp n hn, terminalPriority_dual]

/-- Decoding of C's ordinary tuple state or reserved (DPA_BAD, truth) state. -/
inductive ShortcutState (σ : Type) where
  | active : σ → ShortcutState σ
  | absorbing : Bool → ShortcutState σ
  deriving DecidableEq

def shortcutStep (m : Nat) (ordinary : σ → α → σ × Nat)
    (check : σ → α → Option Bool) (v : α) : ShortcutState σ → ShortcutState σ × Nat
  | .absorbing b => (.absorbing b, terminalPriority m b)
  | .active s => match check s v with
    | some b => (.absorbing b, terminalPriority m b)
    | none => let r := ordinary s v; (.active r.1, r.2)

def shortcutRun (m : Nat) (ordinary : σ → α → σ × Nat)
    (check : σ → α → Option Bool) (initial : σ) (w : Nat → α) : Nat → ShortcutState σ
  | 0 => .active initial
  | n + 1 => (shortcutStep m ordinary check (w n)
      (shortcutRun m ordinary check initial w n)).1

def shortcutPriorities (m : Nat) (ordinary : σ → α → σ × Nat)
    (check : σ → α → Option Bool) (initial : σ) (w : Nat → α) (n : Nat) : Nat :=
  (shortcutStep m ordinary check (w n) (shortcutRun m ordinary check initial w n)).2

theorem shortcut_absorbing_suffix (m : Nat) (ordinary : σ → α → σ × Nat)
    (check : σ → α → Option Bool) (initial : σ) (w : Nat → α) (N : Nat)
    (hs : shortcutRun m ordinary check initial w N = .absorbing b) :
    ∀ n, N ≤ n → shortcutPriorities m ordinary check initial w n = terminalPriority m b := by
  have hstates (k : Nat) : shortcutRun m ordinary check initial w (N+k) = .absorbing b := by
    induction k with
    | zero => exact hs
    | succ k ih =>
      change (shortcutStep m ordinary check (w (N+k))
        (shortcutRun m ordinary check initial w (N+k))).1 = _
      rw [ih]
      rfl
  intro n hn
  have hh := hstates (n-N)
  rw [Nat.add_sub_cancel' hn] at hh
  unfold shortcutPriorities
  rw [hh]
  rfl

theorem shortcut_taken (m : Nat) (ordinary : σ → α → σ × Nat)
    (check : σ → α → Option Bool) (initial : σ) (w : Nat → α) (N : Nat)
    (hs : shortcutRun m ordinary check initial w N = .active s)
    (hc : check s (w N) = some b) :
    shortcutRun m ordinary check initial w (N+1) = .absorbing b := by
  simp only [shortcutRun, hs, shortcutStep, hc]

/-- The executable reserved-state step itself supplies the absorbing suffix.
The remaining simulation premise identifies available ordinary target pairs
with complete component runs; no priority-stream suffix is assumed. -/
theorem terminalExport_input_language (highFirst : ColourDag m → Bool) (epoch : Nat)
    (f : ColourDag m) (targets : Fin m → Option (State ap)) (memo : TerminalMemo m)
    (hm : memo.Valid (partialTerminalValues targets) epoch)
    (he : (terminalShortcut highFirst epoch (partialTerminalValues targets) f memo).1 = some b)
    (xs : Fin m → Class ap) (χ : Formula (Fin ap)) (hx : ProductPresentation χ xs f.eval)
    (ordinary : σ → Letter (Fin ap) → σ × Nat)
    (check : σ → Letter (Fin ap) → Option Bool) (initial s : σ)
    (w : Word (Fin ap)) (N : Nat)
    (hs : shortcutRun m ordinary check initial w N = .active s)
    (hc : check s (w N) = (terminalShortcut highFirst epoch (partialTerminalValues targets) f memo).1)
    (htargets : ∀ i target, targets i = some target → target.denote = Dpa.run (xs i) w (N+1)) :
    (MaxOdd (shortcutPriorities m ordinary check initial w) ↔ Sat none w χ 0) ∧
    (MinEven (fun n => exportBound m - shortcutPriorities m ordinary check initial w n) ↔
      Sat none w χ 0) :=
  terminalShortcut_input_language highFirst epoch f targets memo hm he xs χ hx w (N+1)
    htargets _ (shortcut_absorbing_suffix m ordinary check initial w (N+1)
      (shortcut_taken m ordinary check initial w N hs (hc.trans he)))

end Tlsf.Dpa.Impl
