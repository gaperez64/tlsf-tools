import TlsfProofs.Dpa.Impl.Extractor
import TlsfProofs.Dpa.GeneralConverse

/-!
# Executable complete research component

`initial` corresponds to `src/lib/dpa_dela.c:327`. `transition` is the ordered
table at `:5`, after simultaneous STEP at `src/lib/dpa_formula.c:664` and
unfolding at `:700`. The executable extractor supplies protection, DROP_X,
retry, and retained finite remainders. This is a component reference; it
does not yet model the C constructor's colour sharing or global product.
-/
namespace Tlsf.Dpa.Impl
open Formula
variable {ap : Nat}

structure State (ap : Nat) where
  all : Formula (Fin ap)
  rejecting : Formula (Fin ap)

def State.denote (s : State ap) : Pair ap :=
  ⟨Class.ofFormula s.all, Class.ofFormula s.rejecting⟩

structure Edge (ap : Nat) where
  target : State ap
  mark : Bool

def Edge.denote (e : Edge ap) : Dpa.Edge ap := ⟨e.target.denote, e.mark⟩

def initial (f : Formula (Fin ap)) : State ap :=
  let all := unfoldSyntax f
  if classTag .safety all || classTag .cosafety all then ⟨all, .ff⟩ else ⟨all, rho f⟩

def transition (v : Letter (Fin ap)) (s : State ap) : Edge ap :=
  let a := stepSyntax v s.all
  let next := unfoldSyntax a
  let r := unfoldSyntax (stepSyntax v s.rejecting)
  if equivalent next .ff then ⟨⟨.ff, .ff⟩, false⟩
  else if equivalent next .tt then ⟨⟨.tt, .ff⟩, true⟩
  else if classTag .safety next then ⟨⟨next, .ff⟩, true⟩
  else if classTag .cosafety next then ⟨⟨next, .ff⟩, false⟩
  else if equivalent r .ff then ⟨⟨next, rho a⟩, false⟩
  else if classTag .finite r then
    let q := Formula.conj r (rho a)
    if equivalent q .ff then ⟨⟨.ff, .ff⟩, false⟩ else ⟨⟨next, q⟩, true⟩
  else ⟨⟨next, r⟩, false⟩

theorem initial_exact (f : Formula (Fin ap)) :
    (initial f).denote = Dpa.initial (Class.ofFormula f) := by
  classical
  simp only [initial, Bool.or_eq_true, classTag_exact, fragmentSyntax, ← U_ofFormula,
    Dpa.initial]
  split <;> simp only [State.denote, rho_exact, ← U_ofFormula, Class.bot]

theorem transition_exact (v : Letter (Fin ap)) (s : State ap) :
    (transition v s).denote = Dpa.transition v s.denote := by
  classical
  have hc (f g : Formula (Fin ap)) : Class.ofFormula (.conj f g) = Class.meet (Class.ofFormula f) (Class.ofFormula g) := by
    apply Class.ext; intro σ; rfl
  simp only [transition, equivalent_exact, classTag_exact, fragmentSyntax, hc,
    ← U_ofFormula, ← D_ofFormula, rho_exact, Dpa.transition, State.denote]
  repeat' split
  all_goals simp_all only [Edge.denote, State.denote, ← U_ofFormula, ← D_ofFormula,
    rho_exact, Class.bot, Class.top, ↓reduceIte]

def run (f : Formula (Fin ap)) (w : Word (Fin ap)) : Nat → State ap
  | 0 => initial f
  | n+1 => (transition (w n) (run f w n)).target

def marks (f : Formula (Fin ap)) (w : Word (Fin ap)) (n : Nat) : Bool :=
  (transition (w n) (run f w n)).mark

theorem run_exact (f : Formula (Fin ap)) (w : Word (Fin ap)) (n : Nat) :
    (run f w n).denote = Dpa.run (Class.ofFormula f) w n := by
  induction n with
  | zero => exact initial_exact f
  | succ n ih =>
    have h := congrArg Dpa.Edge.target (transition_exact (w n) (run f w n))
    change (run f w (n+1)).denote = (Dpa.transition (w n) (Dpa.run (Class.ofFormula f) w n)).target
    rw [← ih]
    exact h

theorem marks_exact (f : Formula (Fin ap)) (w : Word (Fin ap)) :
    marks f w = Dpa.marks (Class.ofFormula f) w := by
  funext n
  have h := congrArg Dpa.Edge.mark (transition_exact (w n) (run f w n))
  change (transition (w n) (run f w n)).mark =
    (Dpa.transition (w n) (Dpa.run (Class.ofFormula f) w n)).mark
  rw [← run_exact f w n]
  exact h

/-- An executable complete component, with the same support, extraction,
retry and finite retention decisions as the proved semantic run. -/
theorem pi2_language (f : Formula (Fin ap)) (hn : NNF f)
    (hpi : classTag .pi2 f = true) (w : Word (Fin ap)) :
    Inf (marks f w) ↔ Sat none w f 0 := by
  rw [marks_exact]
  exact (general_pi2_language (Class.ofFormula f) ⟨f, hn, rfl⟩
    ((classTag_exact .pi2 f).mp hpi) w).trans (ofFormula_holds f)

/-- Complement acceptance on this identical complete run. The NNF transport
and the constructor's choice of the dual are separate remaining bridges. -/
theorem pi2_complement (f : Formula (Fin ap)) (hn : NNF f)
    (hpi : classTag .pi2 f = true) (w : Word (Fin ap)) :
    FinMarks (marks f w) ↔ ¬Sat none w f 0 :=
  (complete_complement _).trans (not_congr (pi2_language f hn hpi w))

/-- Stage 1's one-set numeric priorities, in both orientations. Identification
with C's constructed global tree and its terminal shortcut is still separate. -/
theorem pi2_parity (f : Formula (Fin ap)) (hn : NNF f)
    (hpi : classTag .pi2 f = true) (w : Word (Fin ap)) :
    (MinEven (oneSetMin false (marks f w)) ↔ Sat none w f 0) ∧
    (MaxOdd (oneSetExport false (marks f w)) ↔ Sat none w f 0) :=
  ⟨(oneSet_min_inf _).trans (pi2_language f hn hpi w),
    (oneSet_max_inf _).trans (pi2_language f hn hpi w)⟩

theorem pi2_complement_parity (f : Formula (Fin ap)) (hn : NNF f)
    (hpi : classTag .pi2 f = true) (w : Word (Fin ap)) :
    (MinEven (oneSetMin true (marks f w)) ↔ ¬Sat none w f 0) ∧
    (MaxOdd (oneSetExport true (marks f w)) ↔ ¬Sat none w f 0) :=
  ⟨(oneSet_min_fin _).trans (pi2_complement f hn hpi w),
    (oneSet_max_fin _).trans (pi2_complement f hn hpi w)⟩

end Tlsf.Dpa.Impl
