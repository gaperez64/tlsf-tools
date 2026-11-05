import TlsfProofs.Dpa.Validation.Finite
import TlsfProofs.Dpa.Validation.Compact
import TlsfProofs.Dpa.Validation.Normalize
import TlsfProofs.Dpa.FormulaDag

/-! Strict offline decoding. Request and dump each carry their AP order and
formula; mismatches, incomplete rows, invalid indices and trailing tokens fail.
This parser is part of the explicit decoding boundary, not the kernel theorem. -/
namespace Tlsf.Dpa.Validation
open Impl

abbrev Parser := StateT (List String) (Except String)

private def takeToken : Parser String := do
  match ← get with
  | [] => throw "unexpected end of input"
  | x :: xs => set xs; pure x

private def expect (s : String) : Parser Unit := do
  let got ← takeToken
  unless got == s do throw s!"expected {s}, got {got}"

private def natural : Parser Nat := do
  let s ← takeToken
  match s.toNat? with
  | some n => pure n
  | none => throw s!"invalid natural number: {s}"

private def formula (names : Array String) : Nat → Parser (Formula (Fin names.size))
  | 0 => throw "formula depth exceeded"
  | fuel+1 => do
    let s ← takeToken
    match s with
    | "1" => pure .tt
    | "0" => pure .ff
    | "!" => return .neg (← formula names fuel)
    | "X" => return .next (← formula names fuel)
    | "x" => return .strongNext (← formula names fuel)
    | "F" => return .eventually (← formula names fuel)
    | "G" => return .globally (← formula names fuel)
    | "&" => return .conj (← formula names fuel) (← formula names fuel)
    | "|" => return .disj (← formula names fuel) (← formula names fuel)
    | "i" => return .impl (← formula names fuel) (← formula names fuel)
    | "e" => return .equiv (← formula names fuel) (← formula names fuel)
    | "^" => return .neg (.equiv (← formula names fuel) (← formula names fuel))
    | "U" => return .until (← formula names fuel) (← formula names fuel)
    | "R" => return .release (← formula names fuel) (← formula names fuel)
    | "W" => return .weakUntil (← formula names fuel) (← formula names fuel)
    | "M" => return .strongRelease (← formula names fuel) (← formula names fuel)
    | _ =>
      unless s.startsWith "$" do throw s!"unknown formula token: {s}"
      let name := (s.drop 1).toString
      match (List.finRange names.size).find? (fun i => names[i] == name) with
      | some i => pure (.ap i)
      | none => throw s!"undeclared AP: {name}"

structure Request where
  buchi : Bool
  general : Bool
  names : Array String
  astSource : Formula (Fin names.size)
  dag : Option (Array FormulaDag.Node × Nat × Nat) := none
  objective : Formula (Fin names.size) := .tt
  negative : Bool := false

/-- The DAG is the source of psi, rather than an unbound annotation on an AST. -/
def Request.source (r : Request) : Formula (Fin r.names.size) :=
  match r.dag with
  | some (nodes, root, _) => FormulaDag.decodeNode nodes (FormulaDag.indexedAtom r.names.size) root
  | none => r.astSource

private def dagData (aps : Nat) : Parser (Array FormulaDag.Node × Nat) := do
  expect "normalization"
  expect "caller-trusted"
  expect "dag"
  let count ← natural
  let root ← natural
  unless 0 < count && count ≤ 4096 && root < count do throw "invalid DAG size/root"
  let mut nodes := #[]
  for i in List.range count do
    let n : FormulaDag.Node := ⟨← natural, ← natural, ← natural, ← natural⟩
    unless n.kind ≤ FormulaDag.nil && n.left ≤ FormulaDag.nil &&
        n.right ≤ FormulaDag.nil && n.ap ≤ FormulaDag.nil && n.valid aps i do
      throw "invalid DAG record"
    nodes := nodes.push n
  pure (nodes, root)

private def readRequest : Parser Request := do
  let magic ← takeToken
  unless magic == "TV1" || magic == "TVD1" do throw "unknown entry point"
  let kind ← takeToken
  unless kind == "parity" || kind == "buchi" do throw "unknown acceptance kind"
  let admission ← takeToken
  unless admission == "default" || admission == "general" do throw "unknown admission mode"
  let inputs ← natural
  let outputs ← if magic == "TVD1" then natural else pure 0
  let count := inputs + outputs
  unless count ≤ 16 do throw "AP resource limit exceeded"
  let names := (← (List.range count).mapM (fun _ => takeToken)).toArray
  unless names.toList.eraseDups.length == names.size do throw "duplicate AP name"
  if magic == "TVD1" then
    let sign ← takeToken
    unless sign == "positive" || sign == "negative" do throw "invalid objective polarity"
    expect "objective"
    let objective ← formula names 1025
    let (nodes, root) ← dagData count
    pure { buchi := kind == "buchi"
           general := admission == "general"
           names := names
           astSource := .tt
           dag := some (nodes, root, inputs)
           objective := objective
           negative := sign == "negative" }
  else
    let source ← formula names 1025
    pure { buchi := kind == "buchi"
           general := admission == "general"
           names := names
           astSource := source
           objective := source }

private def tokens (s : String) : List String :=
  ((s.splitOn "\n").flatMap (fun line => (line.splitOn "\t").flatMap
    (fun part => part.splitOn " "))).filter (fun t => !t.isEmpty)

private def complete (p : Parser α) (s : String) : Except String α := do
  let (result, rest) ← p.run (tokens s)
  unless rest.isEmpty do throw "trailing tokens"
  pure result

def parseRequest (s : String) : Except String Request := complete readRequest s

structure Dump (ap : Nat) where
  size : Nat
  nonempty : 0 < size
  acceptance : Array Bool
  edges : Array (Fin size × Nat)

@[noinline] def Dump.parity (d : Dump ap) : Parity (Alphabet ap) (Fin d.size) :=
  let width := (colourVectors ap).length
  { initial := ⟨0, d.nonempty⟩
    step := fun i a => d.edges.getD (i.val * width + a.val) (⟨0, d.nonempty⟩, 0) }

@[noinline] def Dump.buchi (d : Dump ap) : Buchi (Alphabet ap) (Fin d.size) :=
  let source := d.parity
  { initial := ⟨0, d.nonempty⟩
    step := fun i a => (source.step i a).1
    accepting := fun i => d.acceptance.getD i.val false }

private def readDump (r : Request) : Parser (Dump r.names.size) := do
  expect (if r.dag.isSome then "TVD1" else "TV1")
  expect (if r.buchi then "buchi" else "parity")
  expect (if r.general then "general" else "default")
  let inputs ← natural
  let outputs ← if r.dag.isSome then natural else pure 0
  let count := inputs + outputs
  unless count == r.names.size do throw "AP count mismatch"
  for name in r.names do
    let got ← takeToken
    unless got == name do throw s!"AP order mismatch: expected {name}, got {got}"
  if let some (nodes, root, ni) := r.dag then
    unless inputs == ni do throw "AP partition mismatch"
    expect (if r.negative then "negative" else "positive")
    expect "objective"
    let objective ← formula r.names 1025
    unless objective == r.objective do throw "objective mismatch"
    let (actualNodes, actualRoot) ← dagData r.names.size
    unless actualNodes == nodes && actualRoot == root do throw "DAG mismatch"
  else
    let source ← formula r.names 1025
    unless source == r.source do throw "formula mismatch"
  expect "states"
  let size ← natural
  if hn : 0 < size then
    unless size ≤ 10000 do throw "state resource limit exceeded"
    let acceptance ← (List.range size).mapM (fun _ => do
      let bit ← natural
      unless bit ≤ 1 do throw "invalid acceptance bit"
      unless r.buchi || bit == 0 do throw "parity state acceptance must be zero"
      pure (bit == 1))
    let mut edges : Array (Fin size × Nat) := #[]
    for i in List.range size do
      for a in List.range (colourVectors r.names.size).length do
        let state ← natural
        let letter ← natural
        unless state == i && letter == a do throw "unsorted or incomplete transition row"
        let target ← natural
        let priority ← natural
        if ht : target < size then
          if r.buchi then
            unless priority == (if acceptance[i]! then 1 else 0) do
              throw "Buchi priority disagrees with source acceptance"
          edges := edges.push (⟨target, ht⟩, priority)
        else throw "transition target out of range"
    expect "end"
    pure ⟨size, hn, acceptance.toArray, edges⟩
  else throw "empty state table"

def parseDump (r : Request) (s : String) : Except String (Dump r.names.size) :=
  complete (readDump r) s

structure FrozenParity (alphabet size : Nat) where
  initial : Fin size
  rows : Vector (Vector (Fin size × Nat) alphabet) size

def FrozenParity.machine (t : FrozenParity alphabet size) : Parity (Fin alphabet) (Fin size) :=
  ⟨t.initial, fun i a => t.rows[i][a]⟩

@[noinline] def freeze (A : Parity (Fin alphabet) (Fin size)) : FrozenParity alphabet size :=
  ⟨A.initial, Vector.ofFn (fun i => Vector.ofFn (A.step i))⟩

theorem freeze_exact (A : Parity (Fin alphabet) (Fin size)) : (freeze A).machine = A := by
  cases A
  simp [freeze, FrozenParity.machine, Vector.getElem_ofFn]

structure FrozenBuchi (alphabet size : Nat) where
  initial : Fin size
  rows : Vector (Vector (Fin size) alphabet) size
  accepting : Vector Bool size

def FrozenBuchi.machine (t : FrozenBuchi alphabet size) : Buchi (Fin alphabet) (Fin size) :=
  ⟨t.initial, fun i a => t.rows[i][a], fun i => t.accepting[i]⟩

@[noinline] def freezeBuchi (A : Buchi (Fin alphabet) (Fin size)) : FrozenBuchi alphabet size :=
  ⟨A.initial, Vector.ofFn (fun i => Vector.ofFn (A.step i)), Vector.ofFn A.accepting⟩

theorem freezeBuchi_exact (A : Buchi (Fin alphabet) (Fin size)) :
    (freezeBuchi A).machine = A := by
  cases A
  simp [freezeBuchi, FrozenBuchi.machine, Vector.getElem_ofFn]

structure CertifiedParity (f : Formula (Fin ap)) where
  size : Nat
  machine : Parity (Alphabet ap) (Fin size)
  language : ∀ w, machine.Accepts w ↔ Sat none (fun n => decode (w n)) f 0

structure CertifiedBuchi (f : Formula (Fin ap)) where
  size : Nat
  machine : Buchi (Alphabet ap) (Fin size)
  language : ∀ w, machine.Accepts w ↔ Sat none (fun n => decode (w n)) f 0

def certifiedParity (f : Formula (Fin ap)) (fuel : Nat) : Except String (CertifiedParity f) :=
  let rank := fun _ : Formula (Fin ap) => 0
  if ha : transportedResearchCheck rank (Impl.normalize f) = true then
    match hc : construct rank rank (Impl.normalize f) with
    | none => .error "reference construction failure"
    | some reference =>
      match ht : reference.exportParity fuel with
      | none => .error "reference parity export failure"
      | some table =>
        .ok ⟨table.states.size,
          (freeze (table.parity reference.finiteParitySource reference.paritySame)).machine,
          fun w => by
            rw [freeze_exact]
            exact (normalized_finite_construction_language rank rank f ha reference hc).1
              fuel table ht w⟩
  else .error "reference admission failure"

def certifiedBuchi (f : Formula (Fin ap)) (fuel : Nat) : Except String (CertifiedBuchi f) :=
  let rank := fun _ : Formula (Fin ap) => 0
  if ha : transportedResearchCheck rank (Impl.normalize f) = true then
    match hc : construct rank rank (Impl.normalize f) with
    | none => .error "reference construction failure"
    | some reference =>
      if hpos : positiveb reference.skeleton = true then
        match ht : reference.exportBuchi fuel with
        | none => .error "reference Buchi export failure"
        | some table =>
          .ok ⟨table.states.size,
            (freezeBuchi (table.buchi reference.finiteBuchiSource reference.buchiSame)).machine,
            fun w => by
              rw [freezeBuchi_exact]
              exact (normalized_finite_construction_language rank rank f ha reference hc).2
                hpos fuel table ht w⟩
      else .error "positiveb failure"
  else .error "reference admission failure"

/-- The round factory checks positivity and carries its language proof. If its
skeleton is not positive, a certified parity comparison is still available.
Construction, export and language-comparison errors remain failing exits. -/
def validate (r : Request) (d : Dump r.names.size) (fuel : Nat) : Except String Unit := do
  if r.buchi then
    match certifiedBuchi r.source fuel with
    | .ok reference =>
      unless checkBuchiCompact d.buchi reference.machine do throw "Buchi language mismatch"
    | .error reason =>
      if reason == "positiveb failure" then
        -- Positivity is sufficient for the round construction, not necessary
        -- for the formula to have a Buchi recognizer. Compare its language to
        -- the general parity reference using the proved Buchi embedding.
        let reference ← certifiedParity r.source fuel
        unless checkCompact d.buchi.toParity reference.machine do throw "Buchi language mismatch"
      else throw reason
  else
    let reference ← certifiedParity r.source fuel
    unless checkCompact d.parity reference.machine do throw "parity language mismatch"

theorem validate_parity_sound (r : Request) (d : Dump r.names.size) (fuel : Nat)
    (hk : r.buchi = false) (h : validate r d fuel = .ok ()) (w : Nat → Alphabet r.names.size) :
    d.parity.Accepts w ↔ Sat none (fun n => decode (w n)) r.source 0 := by
  cases hp : certifiedParity r.source fuel with
  | error reason => simp [validate, hk, hp, bind, Except.bind] at h
  | ok reference =>
    have hc : checkCompact d.parity reference.machine = true := by
      cases hh : checkCompact d.parity reference.machine <;>
        simp_all [validate, bind, Except.bind, pure, throw]
    exact (checkCompact_sound _ _ hc w).trans (reference.language w)

theorem validate_buchi_sound (r : Request) (d : Dump r.names.size) (fuel : Nat)
    (hk : r.buchi = true) (h : validate r d fuel = .ok ()) (w : Nat → Alphabet r.names.size) :
    d.buchi.Accepts w ↔ Sat none (fun n => decode (w n)) r.source 0 := by
  cases hp : certifiedBuchi r.source fuel with
  | error reason =>
    by_cases hs : reason == "positiveb failure"
    · cases hq : certifiedParity r.source fuel with
      | error why => simp [validate, hk, hp, hs, hq, bind, Except.bind] at h
      | ok reference =>
        have hc : checkCompact d.buchi.toParity reference.machine = true := by
          cases hh : checkCompact d.buchi.toParity reference.machine <;>
            simp_all [validate, bind, Except.bind, pure, throw]
        exact (d.buchi.toParity_language w).symm.trans
          ((checkCompact_sound _ _ hc w).trans (reference.language w))
    · simp [validate, hk, hp, hs, throw] at h
  | ok reference =>
    have hc : checkBuchiCompact d.buchi reference.machine = true := by
      cases hh : checkBuchiCompact d.buchi reference.machine <;>
        simp_all [validate, pure, throw]
    exact (checkBuchiCompact_sound _ _ hc w).trans (reference.language w)

theorem validate_dag_parity_sound (r : Request) (d : Dump r.names.size) (fuel : Nat)
    (hk : r.buchi = false) (h : validate r d fuel = .ok ())
    (hd : r.dag = some (nodes, root, inputs)) (w : Nat → Alphabet r.names.size) :
    d.parity.Accepts w ↔
      FormulaDag.denoteNode nodes (FormulaDag.indexedWord (fun n => decode (w n))) root 0 := by
  apply (validate_parity_sound r d fuel hk h w).trans
  simp only [Request.source, hd]
  exact FormulaDag.decode_indexed_meaning _ _ _ _

theorem validate_dag_buchi_sound (r : Request) (d : Dump r.names.size) (fuel : Nat)
    (hk : r.buchi = true) (h : validate r d fuel = .ok ())
    (hd : r.dag = some (nodes, root, inputs)) (w : Nat → Alphabet r.names.size) :
    d.buchi.Accepts w ↔
      FormulaDag.denoteNode nodes (FormulaDag.indexedWord (fun n => decode (w n))) root 0 := by
  apply (validate_buchi_sound r d fuel hk h w).trans
  simp only [Request.source, hd]
  exact FormulaDag.decode_indexed_meaning _ _ _ _

/-- Caller-supplied equivalence of normalized psi and the signed WHOLE phi.
The parser records this trust boundary; validation does not discharge it. -/
def NormalizationPremise (r : Request) : Prop :=
  ∀ w j, Sat none w r.source j ↔
    Sat none w (if r.negative then .neg r.objective else r.objective) j

theorem validate_signed_parity_sound (r : Request) (d : Dump r.names.size) (fuel : Nat)
    (hk : r.buchi = false) (h : validate r d fuel = .ok ())
    (premise : NormalizationPremise r) (w : Nat → Alphabet r.names.size) :
    d.parity.Accepts w ↔ Sat none (fun n => decode (w n))
      (if r.negative then .neg r.objective else r.objective) 0 :=
  (validate_parity_sound r d fuel hk h w).trans (premise _ 0)

theorem validate_signed_buchi_sound (r : Request) (d : Dump r.names.size) (fuel : Nat)
    (hk : r.buchi = true) (h : validate r d fuel = .ok ())
    (premise : NormalizationPremise r) (w : Nat → Alphabet r.names.size) :
    d.buchi.Accepts w ↔ Sat none (fun n => decode (w n))
      (if r.negative then .neg r.objective else r.objective) 0 :=
  (validate_buchi_sound r d fuel hk h w).trans (premise _ 0)

end Tlsf.Dpa.Validation
