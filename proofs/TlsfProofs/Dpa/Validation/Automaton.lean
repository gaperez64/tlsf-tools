import TlsfProofs.Dpa.Stage1

/-! Total deterministic machines. Finite tables instantiate the state type with
`Fin n`; the symbolic reference uses executable formula representatives. -/
namespace Tlsf.Dpa.Validation
variable {Letter State : Type}

structure Parity (Letter State : Type) where
  initial : State
  step : State → Letter → State × Nat

def Parity.run (A : Parity Letter State) (w : Nat → Letter) : Nat → State
  | 0 => A.initial
  | n+1 => (A.step (A.run w n) (w n)).1

def Parity.priorities (A : Parity Letter State) (w : Nat → Letter) (n : Nat) : Nat :=
  (A.step (A.run w n) (w n)).2

def Parity.Accepts (A : Parity Letter State) (w : Nat → Letter) : Prop :=
  MaxOdd (A.priorities w)

structure Buchi (Letter State : Type) where
  initial : State
  step : State → Letter → State
  accepting : State → Bool

def Buchi.run (A : Buchi Letter State) (w : Nat → Letter) : Nat → State
  | 0 => A.initial
  | n+1 => A.step (A.run w n) (w n)

def Buchi.Accepts (A : Buchi Letter State) (w : Nat → Letter) : Prop :=
  Inf (fun n => A.accepting (A.run w n))

end Tlsf.Dpa.Validation
