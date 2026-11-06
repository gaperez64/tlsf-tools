import TlsfProofs.Rewrites

/-!
Structural equality for pre-expansion set elements (expand.c, issue #108).
No temporal equivalence algorithm is needed: the comparison implies equality
of the entire semantic syntax. Consequently *any* deterministic interpretation,
substitution, or expansion in a fixed environment preserves equality. The
explicit lowering below records the core and bounded temporal cases; the
environment supplies the existing integer/guard evaluator and expansion of
names, calls, patterns, bus accesses, and reductions. Those evaluators are not
verified here. There is no claim about two different environments.
-/
namespace Tlsf.SetDedup

inductive UnaryKind where
  | neg | next | strongNext | eventually | globally
  | intNeg | setSize | setMin | setMax
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

inductive BinaryKind where
  | conj | disj | impl | equiv | release | weakUntil | «until» | strongRelease
  | intAdd | intSub | intMul | intDiv | intMod
  | cmpEq | cmpNe | cmpLt | cmpLe | cmpGt | cmpGe
  | setUnion | setInter | setDiff | mem | matchGuard
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

inductive CallKind where
  | definition | pattern
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

inductive QuantKind where
  | forall | exists | sum | product | setBigUnion | setBigInter
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

inductive RangeKind where
  | globally | eventually
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

inductive SetKind where
  | literal | enumeration
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

mutual
  /-- Active payloads only. `absent` represents a null optional child (qset or
  range endpoints). Names model interned identifiers. Array lengths model
  call_argc/set_size; array addresses and unused union arms are not syntax. -/
  inductive HNode where
    | absent | tt | ff
    | int (value : Int)
    | ap (name : String) | intVar (name : String) | sizeof (name : String)
    | unary (kind : UnaryKind) (arg : HNode)
    | busIndex (name : String) (index : HNode)
    | call (kind : CallKind) (callee : String) (args : HNodes)
    | ite (cond yes no : HNode)
    | quant (kind : QuantKind) (var : String) (lo hi set body : HNode)
        (loStrict hiStrict : Bool)
    | range (kind : RangeKind) (lo hi body : HNode) (strong : Bool)
    | set (kind : SetKind) (elems : HNodes)
    | nextN (strong : Bool) (count body : HNode)
    | binary (kind : BinaryKind) (lhs rhs : HNode)
  inductive HNodes where
    | nil | cons (head : HNode) (tail : HNodes)
end

def HNodes.length : HNodes → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

mutual
  /-- Same active fields and short-circuit order as node_structural_equal.
  Constructor/tag discrimination is the initial C kind check. Pointer identity
  is an optimization of this tree comparison, including null == null. -/
  def structEq : HNode → HNode → Bool
    | .absent, .absent | .tt, .tt | .ff, .ff => true
    | .int a, .int b => a == b
    | .ap a, .ap b | .intVar a, .intVar b | .sizeof a, .sizeof b => a == b
    | .unary k a, .unary l b => k == l && structEq a b
    | .busIndex n a, .busIndex m b => n == m && structEq a b
    | .call k n as, .call l m bs =>
        k == l && n == m && as.length == bs.length && nodesEq as bs
    | .ite c t e, .ite d u f => structEq c d && structEq t u && structEq e f
    | .quant k v lo hi s b ls hs, .quant l w lo' hi' s' b' ls' hs' =>
        k == l && v == w && structEq lo lo' && structEq hi hi' &&
          structEq s s' && structEq b b' && ls == ls' && hs == hs'
    | .range k lo hi b s, .range l lo' hi' b' s' =>
        k == l && structEq lo lo' && structEq hi hi' && structEq b b' && s == s'
    | .set k as, .set l bs => k == l && as.length == bs.length && nodesEq as bs
    | .nextN s n a, .nextN t m b => s == t && structEq n m && structEq a b
    | .binary k a b, .binary l c d => k == l && structEq a c && structEq b d
    | _, _ => false
  def nodesEq : HNodes → HNodes → Bool
    | .nil, .nil => true
    | .cons a as, .cons b bs => structEq a b && nodesEq as bs
    | _, _ => false
end

mutual
  theorem structEq_eq (a b : HNode) (h : structEq a b = true) : a = b := by
    cases a <;> cases b <;>
      simp only [structEq, Bool.and_eq_true, beq_iff_eq, and_assoc,
        Bool.false_eq_true] at h
    all_goals try first | contradiction | rfl | (obtain rfl := h; rfl)
    · obtain ⟨rfl, h⟩ := h
      rw [structEq_eq _ _ h]
    · obtain ⟨rfl, h⟩ := h
      rw [structEq_eq _ _ h]
    · obtain ⟨rfl, rfl, _, h⟩ := h
      rw [nodesEq_eq _ _ h]
    · obtain ⟨hc, ht, he⟩ := h
      rw [structEq_eq _ _ hc, structEq_eq _ _ ht, structEq_eq _ _ he]
    · obtain ⟨rfl, rfl, hlo, hhi, hs, hb, rfl, rfl⟩ := h
      rw [structEq_eq _ _ hlo, structEq_eq _ _ hhi,
        structEq_eq _ _ hs, structEq_eq _ _ hb]
    · obtain ⟨rfl, hlo, hhi, hb, rfl⟩ := h
      rw [structEq_eq _ _ hlo, structEq_eq _ _ hhi, structEq_eq _ _ hb]
    · obtain ⟨rfl, _, h⟩ := h
      rw [nodesEq_eq _ _ h]
    · obtain ⟨rfl, hn, hb⟩ := h
      rw [structEq_eq _ _ hn, structEq_eq _ _ hb]
    · obtain ⟨rfl, hl, hr⟩ := h
      rw [structEq_eq _ _ hl, structEq_eq _ _ hr]
  theorem nodesEq_eq (as bs : HNodes) (h : nodesEq as bs = true) : as = bs := by
    cases as <;> cases bs <;> simp only [nodesEq, Bool.and_eq_true] at h
    · rfl
    · contradiction
    · contradiction
    · obtain ⟨h, ht⟩ := h
      rw [structEq_eq _ _ h, nodesEq_eq _ _ ht]
end

/- The proof above is stronger than equality after temporal expansion. In
particular it applies before/after actual-argument substitution, and when a
formula-valued binder substitutes the element into a reduction body. -/
theorem structEq_congr (interpret : HNode → β) {a b : HNode}
    (h : structEq a b = true) : interpret a = interpret b :=
  congrArg interpret (structEq_eq a b h)

theorem structEq_substitution (substitute : HNode → HNode) {a b : HNode}
    (h : structEq a b = true) : substitute a = substitute b :=
  structEq_congr substitute h

def strongNextPower : Nat → Formula α → Formula α
  | 0, f => f
  | n+1, f => .strongNext (strongNextPower n f)

/-- Count-fold weak/strong next, including the identity at zero. -/
def indexedNext (strong : Bool) (n : Nat) (f : Formula α) : Formula α :=
  if strong then strongNextPower n f else Rewrites.next_power n f

/-- C's left-associated bounded fold, with no leading identity operand. -/
def rangeFold (all : Bool) : List (Formula α) → Formula α
  | [] => if all then .tt else .ff
  | f :: fs => fs.foldl (fun a b => if all then .conj a b else .disj a b) f

def boundedRange (kind : RangeKind) (strong : Bool) (lo hi : Nat)
    (body : Formula α) : Formula α :=
  rangeFold (kind == .globally)
    ((List.range' lo (hi + 1 - lo)).map (fun k => indexedNext strong k body))

/-- A fixed admitted expansion environment. `integer` gives successfully
evaluated nonnegative counts/bounds (negative bounds are rejected by C).
`guard` evaluates ordinary definition guards. `resolve` gives the expansion
of identifiers (including nullary definitions), bus accesses, calls, patterns,
comparisons and reductions. Pattern-guard ITEs also use it because selection
substitutes the captured formula into the branch. This interface deliberately
does not assume arithmetic, definition termination, or binder correctness. -/
structure LowerEnv (α : Type) where
  integer : HNode → Nat
  guard : HNode → Bool
  resolve : HNode → Formula α

/-- Temporal lowering in expand_node. Remaining evaluation is supplied by the
same fixed environment for both nodes. Formula-valued binders are included in
the stronger `structEq_congr` theorem, for any deterministic resolver. -/
def lower (env : LowerEnv α) : HNode → Formula α
  | .tt => .tt
  | .ff => .ff
  | .unary .neg f => .neg (lower env f)
  | .unary .next f => .next (lower env f)
  | .unary .strongNext f => .strongNext (lower env f)
  | .unary .eventually f => .eventually (lower env f)
  | .unary .globally f => .globally (lower env f)
  | .binary .conj a b => .conj (lower env a) (lower env b)
  | .binary .disj a b => .disj (lower env a) (lower env b)
  | .binary .impl a b => .impl (lower env a) (lower env b)
  | .binary .equiv a b => .equiv (lower env a) (lower env b)
  | .binary .release a b => .release (lower env a) (lower env b)
  | .binary .weakUntil a b => .weakUntil (lower env a) (lower env b)
  | .binary .until a b => .until (lower env a) (lower env b)
  | .binary .strongRelease a b => .strongRelease (lower env a) (lower env b)
  | .nextN strong count body => indexedNext strong (env.integer count) (lower env body)
  | .range kind lo hi body strong =>
      boundedRange kind strong (env.integer lo) (env.integer hi) (lower env body)
  | .ite (.binary .matchGuard a p) t e =>
      env.resolve (.ite (.binary .matchGuard a p) t e)
  | .ite c t e => if env.guard c then lower env t else lower env e
  | other => env.resolve other

theorem structEq_lower (env : LowerEnv α) {a b : HNode}
    (h : structEq a b = true) : lower env a = lower env b :=
  structEq_congr (lower env) h

/-- Both `none` (infinite) and `some n` (finite), at every position, including
terminal and out-of-range queries. No in-range premise hides a boundary. -/
theorem structEq_denotation (env : LowerEnv α) {a b : HNode}
    (h : structEq a b = true) :
    ∀ len w j, Sat len w (lower env a) j ↔ Sat len w (lower env b) j := by
  rw [structEq_lower env h]
  exact fun _ _ _ => Iff.rfl

/-- Dropping a structurally duplicate conjunct/disjunct preserves meaning.
These are the formula-valued FORALL/EXISTS folds used by the issue fixture. -/
theorem dedup_conj (env : LowerEnv α) {a b : HNode} (h : structEq a b = true) :
    Sat len w (.conj (lower env a) (lower env b)) j ↔ Sat len w (lower env a) j := by
  rw [structEq_lower env h]
  simp only [Sat, and_self]
  exact ⟨And.right, fun hs => ⟨sat_inRange hs, hs⟩⟩

theorem dedup_disj (env : LowerEnv α) {a b : HNode} (h : structEq a b = true) :
    Sat len w (.disj (lower env a) (lower env b)) j ↔ Sat len w (lower env a) j := by
  rw [structEq_lower env h]
  simp only [Sat, or_self]
  exact ⟨And.right, fun hs => ⟨sat_inRange hs, hs⟩⟩

def weakOne : HNode := .nextN false (.int 1) .tt
def strongOne : HNode := .nextN true (.int 1) .tt

theorem issue108_not_structEq : structEq weakOne strongOne = false := rfl

/-- The only bound in the counterexample is the literal 1. -/
def literalEnv : LowerEnv String where
  integer := fun n => match n with | .int i => i.toNat | _ => 0
  guard := fun _ => false
  resolve := fun n => match n with | .ap s => .ap s | _ => .ff

theorem issue108_terminal (w : Word String) :
    Sat (some 1) w (lower literalEnv weakOne) 0 ∧
    ¬Sat (some 1) w (lower literalEnv strongOne) 0 := by
  simp [weakOne, strongOne, lower, literalEnv, indexedNext,
    Rewrites.next_power, strongNextPower, Sat, InRange]

theorem issue108_denotations_differ (w : Word String) :
    ¬(Sat (some 1) w (lower literalEnv weakOne) 0 ↔
      Sat (some 1) w (lower literalEnv strongOne) 0) := by
  intro h
  exact (issue108_terminal w).2 (h.mp (issue108_terminal w).1)

end Tlsf.SetDedup
