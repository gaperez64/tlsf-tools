import TlsfProofs.LTL

namespace Tlsf
abbrev Strategy (α : Type) := List (Letter α) → Letter α → Letter α

def mask (isIn : α → Bool) (v : Letter α) : Letter α :=
  fun a => if isIn a then v a else false

def move (isIn : α → Bool) (s : Strategy α) (h : List (Letter α))
    (i : Letter α) : Letter α :=
  fun a => if isIn a then i a else s h (mask isIn i) a

-- Histories are stored with the newest letter first.
def history (isIn : α → Bool) (s : Strategy α) (i : Word α) : Nat → List (Letter α)
  | 0 => []
  | n+1 => move isIn s (history isIn s i n) (i n) :: history isIn s i n

def play (isIn : α → Bool) (s : Strategy α) (i : Word α) : Word α :=
  fun n => move isIn s (history isIn s i n) (i n)

def replay (isIn : α → Bool) (s : Strategy α) : List (Letter α) → List (Letter α)
  | [] => []
  | l :: h => move isIn s (replay isIn s h) l :: replay isIn s h

theorem mask_move : mask isIn (move isIn s h i) = mask isIn i := by
  funext a; cases hi : isIn a <;> simp [mask, move, hi]

theorem mask_mask : mask isIn (mask isIn i) = mask isIn i := by
  funext a; cases hi : isIn a <;> simp [mask, hi]

theorem move_mask (h : mask isIn i = mask isIn i') :
    move isIn s hs i = move isIn s hs i' := by
  funext a
  have ha := congrFun h a
  cases hi : isIn a <;> simp_all [move, mask]

theorem replay_history (s t : Strategy α) (i : Word α) (n : Nat) :
    replay isIn s (history isIn t i n) = history isIn s i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, replay, ih]
    rw [move_mask (mask_move (isIn := isIn) (s := t))]

theorem replay_ignores_outputs {h h' : List (Letter α)}
    (hm : h.map (mask isIn) = h'.map (mask isIn)) :
    replay isIn s h = replay isIn s h' := by
  induction h generalizing h' with
  | nil => cases h' <;> simp_all [replay]
  | cons l h ih =>
    cases h' with
    | nil => simp at hm
    | cons l' h' =>
      simp only [List.map_cons, List.cons.injEq] at hm
      simp only [replay, ih hm.2]
      rw [move_mask hm.1]

def KeepsInputs (isIn : α → Bool) (T : Letter α → Letter α) : Prop :=
  ∀ v a, isIn a = true → T v a = v a

def decorate (isIn : α → Bool) (T : Letter α → Letter α) (s : Strategy α) : Strategy α :=
  fun h i => T (move isIn s (replay isIn s h) i)

variable {isIn : α → Bool} {T : Letter α → Letter α}

theorem play_decorate (hT : KeepsInputs isIn T) (s : Strategy α) (i : Word α) :
    play isIn (decorate isIn T s) i = fun n => T (play isIn s i n) := by
  funext n a
  simp only [play, move, decorate, replay_history]
  rw [move_mask (mask_mask (isIn := isIn) (i := i n))]
  cases ha : isIn a with
  | false => rfl
  | true =>
    rw [hT _ a ha]
    simp [move, ha]

def Wins (isIn : α → Bool) (Φ : Word α → Prop) : Prop :=
  ∃ s : Strategy α, ∀ i : Word α, Φ (play isIn s i)

def InfWin (isIn : α → Bool) (Φ : Option Nat → Word α → Prop) : Prop :=
  Wins isIn (Φ none)

def FinWin (isIn : α → Bool) (Φ : Option Nat → Word α → Prop) : Prop :=
  Wins isIn (fun w => ∃ n, Φ (some (n+1)) w)

def Realizable (isIn : α → Bool) (f : Formula α) : Prop :=
  InfWin isIn (fun len w => Sat len w f 0)

def FinRealizable (isIn : α → Bool) (f : Formula α) : Prop :=
  FinWin isIn (fun len w => Sat len w f 0)

theorem transfer (hT : KeepsInputs isIn T)
    (forward : ∀ w, Φr w → Φo (fun n => T (w n)))
    (backward : ∀ w, Φo w → Φr w) : Wins isIn Φo ↔ Wins isIn Φr := by
  constructor
  · rintro ⟨s, hs⟩; exact ⟨s, fun i => backward _ (hs i)⟩
  · rintro ⟨s, hs⟩
    refine ⟨decorate isIn T s, fun i => ?_⟩
    rw [play_decorate hT]
    exact forward _ (hs i)

theorem transfer_inf (hT : KeepsInputs isIn T)
    (forward : ∀ w, Φr none w → Φo none (fun n => T (w n)))
    (backward : ∀ w, Φo none w → Φr none w) :
    InfWin isIn Φo ↔ InfWin isIn Φr := transfer hT forward backward

theorem transfer_fin (hT : KeepsInputs isIn T)
    (forward : ∀ n w, Φr (some (n+1)) w → Φo (some (n+1)) (fun j => T (w j)))
    (backward : ∀ n w, Φo (some (n+1)) w → Φr (some (n+1)) w) :
    FinWin isIn Φo ↔ FinWin isIn Φr := by
  apply transfer hT
  · rintro w ⟨n, hn⟩; exact ⟨n, forward n w hn⟩
  · rintro w ⟨n, hn⟩; exact ⟨n, backward n w hn⟩

-- An output belongs to exactly one key. Each component replays its own history.
def productStrategy (isIn : α → Bool) (key : α → κ) (ss : κ → Strategy α) : Strategy α :=
  fun h i a => ss (key a) (replay isIn (ss (key a)) h) i a

theorem product_plays (ss : κ → Strategy α) (key : α → κ) (i : Word α)
    (a : α) (n : Nat) :
    play isIn (productStrategy isIn key ss) i n a = play isIn (ss (key a)) i n a := by
  simp only [play, move, productStrategy, replay_history]
end Tlsf
