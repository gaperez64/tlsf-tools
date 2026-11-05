import TlsfProofs.LTL

/-! Mathematical port of the record checks and topological decoding in
`tlsf_dpa_create_from_dag`. Naturals represent uint32_t values; `bounded`
records the representation premise. Pointers, allocation, admission, and the
subsequent automaton construction are outside this decoding theorem. -/
namespace Tlsf.Dpa.FormulaDag

def nil : Nat := 4294967295

inductive Op where
  | tt | ff | ap | neg | conj | disj | impl | equiv | next
  | eventually | globally | until | release | weakUntil | strongRelease | invalid
  deriving DecidableEq, Repr

/-- Public TlsfAstKind numbers, deliberately excluding X_STRONG (9). -/
def operator : Nat → Op
  | 0 => .tt | 1 => .ff | 2 => .ap | 3 => .neg | 4 => .conj
  | 5 => .disj | 6 => .impl | 7 => .equiv | 8 => .next
  | 10 => .eventually | 11 => .globally | 12 => .until | 13 => .release
  | 14 => .weakUntil | 15 => .strongRelease | _ => .invalid

def arity : Op → Nat
  | .tt | .ff | .ap | .invalid => 0
  | .neg | .next | .eventually | .globally => 1
  | _ => 2

structure Node where
  kind : Nat := 1
  left : Nat := nil
  right : Nat := nil
  ap : Nat := nil
  deriving DecidableEq, BEq, Repr, Inhabited

def Node.bounded (n : Node) : Prop :=
  n.kind ≤ nil ∧ n.left ≤ nil ∧ n.right ≤ nil ∧ n.ap ≤ nil

/-- Every record is checked, including records unreachable from the root.
Equal left/right indices are allowed: no tree or unique-parent premise. -/
def Node.valid (aps index : Nat) (n : Node) : Bool :=
  let op := operator n.kind
  op != .invalid &&
    (if arity op > 0 then n.left < index else n.left == nil) &&
    (if arity op == 2 then n.right < index else n.right == nil) &&
    (if op == .ap then n.ap < aps else n.ap == nil)

structure Dag (Name : Type) where
  inputs : Array Name
  outputs : Array Name
  nodes : Array Node
  root : Nat

def Dag.names (d : Dag Name) : Array Name := d.inputs ++ d.outputs

/-- `usable` models non-null, nonempty C strings (names are byte strings up to
the first NUL). Valid storage and non-null nodes/out pointers are preconditions
of this mathematical port, not claims about C memory safety. -/
def Accepted (usable : Name → Prop) (d : Dag Name) : Prop :=
  d.names.size ≤ nil ∧ d.nodes.size ≤ nil ∧ d.root < d.nodes.size ∧
  (∀ i : Fin d.names.size, usable d.names[i]) ∧
  (∀ i j : Fin d.names.size, d.names[i] = d.names[j] → i = j) ∧
  ∀ i : Fin d.nodes.size, d.nodes[i].bounded ∧ d.nodes[i].valid d.names.size i = true

def formulaOp (op : Op) (atom f g : Formula α) : Formula α :=
  match op with
  | .tt => .tt | .ff | .invalid => .ff | .ap => atom
  | .neg => .neg f | .conj => .conj f g | .disj => .disj f g
  | .impl => .impl f g | .equiv => .equiv f g | .next => .next f
  | .eventually => .eventually f | .globally => .globally f
  | .until => .until f g | .release => .release f g
  | .weakUntil => .weakUntil f g | .strongRelease => .strongRelease f g

/-- Direct infinite-word denotation, independent of Formula syntax. -/
def meaningOp (op : Op) (atom p q : Nat → Prop) (j : Nat) : Prop :=
  match op with
  | .tt => True | .ff | .invalid => False | .ap => atom j
  | .neg => ¬p j | .conj => p j ∧ q j | .disj => p j ∨ q j
  | .impl => p j → q j | .equiv => p j ↔ q j | .next => p (j+1)
  | .eventually => ∃ k, j ≤ k ∧ p k
  | .globally => ∀ k, j ≤ k → p k
  | .until => ∃ k, j ≤ k ∧ q k ∧ ∀ i, j ≤ i → i < k → p i
  | .release => ¬∃ k, j ≤ k ∧ ¬q k ∧ ∀ i, j ≤ i → i < k → ¬p i
  | .weakUntil => (∃ k, j ≤ k ∧ q k ∧ ∀ i, j ≤ i → i < k → p i) ∨
      ∀ k, j ≤ k → p k
  | .strongRelease => ¬((∃ k, j ≤ k ∧ ¬q k ∧ ∀ i, j ≤ i → i < k → ¬p i) ∨
      ∀ k, j ≤ k → ¬p k)

theorem formulaOp_meaning (op : Op) (atom f g : Formula α) (w : Word α) (j : Nat) :
    Sat none w (formulaOp op atom f g) j ↔
      meaningOp op (Sat none w atom) (Sat none w f) (Sat none w g) j := by
  cases op <;> simp [formulaOp, meaningOp, Sat, InRange, AllFuture, UntilAt]

/-- The decreasing index is the induction measure, regardless of sharing.
Defaults totalize the function only; accepted records never use them. -/
def decodeNode (nodes : Array Node) (atom : Nat → Formula α) (i : Nat) : Formula α :=
  let n := nodes.getD i {}
  formulaOp (operator n.kind) (atom n.ap)
    (if _h : n.left < i then decodeNode nodes atom n.left else .ff)
    (if _h : n.right < i then decodeNode nodes atom n.right else .ff)
termination_by i
decreasing_by all_goals exact _h

def denoteNode (nodes : Array Node) (w : Word Nat) (i : Nat) : Nat → Prop :=
  let n := nodes.getD i {}
  meaningOp (operator n.kind) (fun j => w j n.ap = true)
    (if _h : n.left < i then denoteNode nodes w n.left else fun _ => False)
    (if _h : n.right < i then denoteNode nodes w n.right else fun _ => False)
termination_by i
decreasing_by all_goals exact _h

theorem decodeNode_meaning (nodes : Array Node) (atom : Nat → Formula α)
    (v : Word α) (w : Word Nat) (ha : ∀ a j, Sat none v (atom a) j ↔ w j a = true)
    (i j : Nat) : Sat none v (decodeNode nodes atom i) j ↔ denoteNode nodes w i j := by
  induction i using Nat.strongRecOn generalizing j with
  | ind i ih =>
    rw [decodeNode, denoteNode, formulaOp_meaning]
    have hatom : Sat none v (atom (nodes.getD i {}).ap) =
        (fun j => w j (nodes.getD i {}).ap = true) :=
      funext fun k => propext (ha _ k)
    have child (a : Nat) :
        Sat none v (if _h : a < i then decodeNode nodes atom a else .ff) =
        (if _h : a < i then denoteNode nodes w a else fun _ => False) := by
      split <;> rename_i h
      · exact funext fun k => propext (ih a h k)
      · funext k; simp [Sat, InRange]
    rw [hatom, child, child]

/-- Root selection does not assume the last node is the root. The names array
retains every declaration in input-then-output order, even unused ones. -/
theorem decode_root_meaning (d : Dag Name) (usable : Name → Prop)
    (_accepted : Accepted usable d) (v : Word Name) (fallback : Name) (j : Nat) :
    Sat none v (decodeNode d.nodes (fun a => .ap (d.names.getD a fallback)) d.root) j ↔
      denoteNode d.nodes (fun k a => v k (d.names.getD a fallback)) d.root j :=
  decodeNode_meaning _ _ _ _ (by intro a k; simp [Sat, InRange]) _ _

theorem ordered_ap (d : Dag Name) (i : Fin d.names.size) (fallback : Name) :
    d.names.getD i.val fallback = d.names[i] := by
  simp [Array.getD, i.isLt]

theorem input_order (d : Dag Name) (i : Fin d.inputs.size) :
    d.names[i.val]'(by simp [Dag.names]; omega) = d.inputs[i] := by
  simp [Dag.names, Array.getElem_append_left, i.isLt]

theorem output_order (d : Dag Name) (i : Fin d.outputs.size) :
    d.names[d.inputs.size + i.val]'(by simp [Dag.names]) = d.outputs[i] := by
  simp [Dag.names, Array.getElem_append_right]

def indexedAtom (ap a : Nat) : Formula (Fin ap) :=
  if h : a < ap then .ap ⟨a, h⟩ else .ff

def indexedWord (w : Word (Fin ap)) : Word Nat :=
  fun j a => if h : a < ap then w j ⟨a, h⟩ else false

theorem decode_indexed_meaning (nodes : Array Node) (w : Word (Fin ap)) (i j : Nat) :
    Sat none w (decodeNode nodes (indexedAtom ap) i) j ↔
      denoteNode nodes (indexedWord w) i j := by
  apply decodeNode_meaning
  intro a k
  simp only [indexedAtom, indexedWord]
  split <;> simp [Sat, InRange]

end Tlsf.Dpa.FormulaDag
