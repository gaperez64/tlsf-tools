import TlsfProofs.SetDedup
import TlsfProofs.IntegerLiteral

/-!
Port of normalize.c's pre_indexed_x, after #118 (issue #117).
Use the high-level syntax and lowering from #108, including bounded.strong.
The result preserves the entire expanded Formula, not just infinite Sat.
Only successfully allocated ASTs are modelled; pointer reuse is syntax identity.
-/
namespace Tlsf.NextStrength

open SetDedup IntegerLiteral

/-- Nonnegative literal counts have their exact value in the fixed lowering
environment. Negative counts are rejected by expansion, never merged here. -/
def LiteralCounts (env : LowerEnv α) : Prop :=
  ∀ i, 0 ≤ i → env.integer (.int i) = i.toNat

def nextCtor (strong : Bool) (f : Formula α) : Formula α :=
  if strong then .strongNext f else .next f

theorem indexedNext_zero : indexedNext s 0 f = f := by cases s <;> rfl

theorem indexedNext_succ :
    indexedNext s (n + 1) f = nextCtor s (indexedNext s n f) := by cases s <;> rfl

/-- Equality of constructor sequences, for either strength and all counts. -/
theorem indexedNext_add (s : Bool) (m n : Nat) (f : Formula α) :
    indexedNext s m (indexedNext s n f) = indexedNext s (m + n) f := by
  induction m with
  | zero => simp only [indexedNext_zero, Nat.zero_add]
  | succ m ih => rw [Nat.succ_add, indexedNext_succ, indexedNext_succ, ih]

theorem increment_fits (hc : 0 ≤ c) (hmax : c < max64) :
    Fits (c + 1) ∧ (c + 1).toNat = c.toNat + 1 := by
  simp only [Fits, min64, max64] at *
  omega

theorem addition_fits (hc : 0 ≤ c) (hd : 0 ≤ d) (hmax : c ≤ max64 - d) :
    Fits (c + d) ∧ (c + d).toNat = c.toNat + d.toNat := by
  simp only [Fits, min64, max64] at *
  omega

/-- The guard's subtraction itself cannot overflow for a nonnegative C count. -/
theorem addition_guard_exact (hc : 0 ≤ c) (hd : 0 ≤ d) (hfit : Fits d) :
    Fits (max64 - d) ∧ (c ≤ max64 - d ↔ Fits (c + d)) := by
  simp only [Fits, min64, max64] at *
  omega

theorem increment_guard_exact (hc : 0 ≤ c) : c < max64 ↔ Fits (c + 1) := by
  simp only [Fits, min64, max64] at *
  omega

/-- NODE_NEXT_N local branches, after recursively rewriting the body.
Strong unary next deliberately has no merge branch in the C implementation. -/
def indexed (strong : Bool) (count body : HNode) : HNode :=
  match count with
  | .int c =>
      if c = 0 then body else
      match body with
      | .unary .next p =>
          if strong = false ∧ 0 ≤ c ∧ c < max64 then
            .nextN strong (.int (c + 1)) p
          else .nextN strong count body
      | .nextN t (.int d) p =>
          if strong = t ∧ 0 ≤ c ∧ 0 ≤ d ∧ c ≤ max64 - d then
            .nextN strong (.int (c + d)) p
          else .nextN strong count body
      | _ => .nextN strong count body
  | _ => .nextN strong count body

/-- NODE_X local branches; NODE_X_STRONG only reconstructs. -/
def weakUnary (arg : HNode) : HNode :=
  match arg with
  | .nextN false (.int d) p =>
      if 0 ≤ d ∧ d < max64 then .nextN false (.int (d + 1)) p
      else .unary .next arg
  | _ => .unary .next arg

theorem indexed_zero : indexed s (.int 0) body = body := by simp [indexed]

theorem indexed_unary_merge (hc : c ≠ 0) (hlo : 0 ≤ c) (hhi : c < max64) :
    indexed false (.int c) (.unary .next body) = .nextN false (.int (c + 1)) body := by
  simp [indexed, hc, hlo, hhi]

theorem indexed_indexed_merge (hc : c ≠ 0) (hlo : 0 ≤ c) (hd : 0 ≤ d)
    (hhi : c ≤ max64 - d) :
    indexed s (.int c) (.nextN s (.int d) body) = .nextN s (.int (c + d)) body := by
  simp [indexed, hc, hlo, hd, hhi]

theorem unary_indexed_merge (hlo : 0 ≤ d) (hhi : d < max64) :
    weakUnary (.nextN false (.int d) body) = .nextN false (.int (d + 1)) body := by
  simp [weakUnary, hlo, hhi]

theorem indexed_mixed (hc : c ≠ 0) (hs : s ≠ t) :
    indexed s (.int c) (.nextN t (.int d) body) =
      .nextN s (.int c) (.nextN t (.int d) body) := by
  simp [indexed, hc, hs]

theorem indexed_strongUnary (hc : c ≠ 0) :
    indexed s (.int c) (.unary .strongNext body) =
      .nextN s (.int c) (.unary .strongNext body) := by
  simp [indexed, hc]

theorem weakUnary_strongIndexed :
    weakUnary (.nextN true count body) = .unary .next (.nextN true count body) := rfl

/-- Every fallback reconstructs the original outer strength and count. -/
theorem indexed_lower (env : LowerEnv α) (hl : LiteralCounts env)
    (s : Bool) (count body : HNode) :
    lower env (indexed s count body) = lower env (.nextN s count body) := by
  cases count <;> try rfl
  case int c =>
    by_cases hz : c = 0
    · subst c
      simp [indexed, lower, hl 0 (by decide), indexedNext_zero]
    · simp only [indexed, hz, ↓reduceIte]
      cases body <;> try rfl
      case unary k p =>
        cases k <;> try rfl
        case next =>
          by_cases h : s = false ∧ 0 ≤ c ∧ c < max64
          · obtain ⟨rfl, hc, hmax⟩ := h
            simp only [hc, hmax, and_self, ↓reduceIte, lower,
              hl c hc, hl (c + 1) (by omega), (increment_fits hc hmax).2]
            exact (indexedNext_add false c.toNat 1 (lower env p)).symm
          · simp only [h, ↓reduceIte]
      case nextN t count p =>
        cases count <;> try rfl
        case int d =>
          by_cases h : s = t ∧ 0 ≤ c ∧ 0 ≤ d ∧ c ≤ max64 - d
          · obtain ⟨rfl, hc, hd, hmax⟩ := h
            simp only [hc, hd, hmax, and_self, ↓reduceIte, lower,
              hl c hc, hl d hd, hl (c + d) (by omega), (addition_fits hc hd hmax).2]
            exact (indexedNext_add s c.toNat d.toNat (lower env p)).symm
          · simp only [h, ↓reduceIte]

theorem weakUnary_lower (env : LowerEnv α) (hl : LiteralCounts env) (arg : HNode) :
    lower env (weakUnary arg) = lower env (.unary .next arg) := by
  cases arg <;> try rfl
  case nextN s count p =>
    cases s <;> try rfl
    cases count <;> try rfl
    case int d =>
      by_cases h : 0 ≤ d ∧ d < max64
      · obtain ⟨hd, hmax⟩ := h
        simp only [weakUnary, hd, hmax, and_self, ↓reduceIte, lower,
          hl d hd, hl (d + 1) (by omega), (increment_fits hd hmax).2, indexedNext_succ]
        rfl
      · simp only [weakUnary, h, ↓reduceIte]

theorem indexed_zero_sat (env : LowerEnv α) (hl : LiteralCounts env) :
    Sat len w (lower env body) j ↔ Sat len w (lower env (.nextN s (.int 0) body)) j := by
  rw [← indexed_lower env hl s (.int 0) body, indexed_zero]

theorem indexed_unary_sat (env : LowerEnv α) (hl : LiteralCounts env)
    (hc : c ≠ 0) (hlo : 0 ≤ c) (hhi : c < max64) :
    Sat len w (lower env (.nextN false (.int (c + 1)) body)) j ↔
      Sat len w (lower env (.nextN false (.int c) (.unary .next body))) j := by
  rw [← indexed_unary_merge hc hlo hhi, indexed_lower env hl]

theorem indexed_indexed_sat (env : LowerEnv α) (hl : LiteralCounts env)
    (hc : c ≠ 0) (hlo : 0 ≤ c) (hd : 0 ≤ d) (hhi : c ≤ max64 - d) :
    Sat len w (lower env (.nextN s (.int (c + d)) body)) j ↔
      Sat len w (lower env (.nextN s (.int c) (.nextN s (.int d) body))) j := by
  rw [← indexed_indexed_merge hc hlo hd hhi, indexed_lower env hl]

theorem unary_indexed_sat (env : LowerEnv α) (hl : LiteralCounts env)
    (hlo : 0 ≤ d) (hhi : d < max64) :
    Sat len w (lower env (.nextN false (.int (d + 1)) body)) j ↔
      Sat len w (lower env (.unary .next (.nextN false (.int d) body))) j := by
  rw [← unary_indexed_merge hlo hhi, weakUnary_lower env hl]

/-- Applies even when the count is symbolic, negative, or too large to merge. -/
theorem indexed_rebuild_sat (env : LowerEnv α)
    (hb : lower env body' = lower env body) :
    Sat len w (lower env (.nextN s count body')) j ↔
      Sat len w (lower env (.nextN s count body)) j := by
  simp only [lower, hb]

theorem strongUnary_rebuild_sat (env : LowerEnv α)
    (hb : lower env body' = lower env body) :
    Sat len w (lower env (.unary .strongNext body')) j ↔
      Sat len w (lower env (.unary .strongNext body)) j := by
  simp only [lower, hb]

/-- Same recursion frontier as C: count expressions, U/R/W/M, ranges,
binders and other high-level nodes are returned untouched. -/
def preIndexedX : HNode → HNode
  | .nextN s count body => indexed s count (preIndexedX body)
  | .unary .next arg => weakUnary (preIndexedX arg)
  | .unary .strongNext arg => .unary .strongNext (preIndexedX arg)
  | .unary .neg arg => .unary .neg (preIndexedX arg)
  | .unary .globally arg => .unary .globally (preIndexedX arg)
  | .unary .eventually arg => .unary .eventually (preIndexedX arg)
  | .binary .conj l r => .binary .conj (preIndexedX l) (preIndexedX r)
  | .binary .disj l r => .binary .disj (preIndexedX l) (preIndexedX r)
  | .binary .impl l r => .binary .impl (preIndexedX l) (preIndexedX r)
  | .binary .equiv l r => .binary .equiv (preIndexedX l) (preIndexedX r)
  | n => n

/-- Whole-pass correspondence, including nested child rewrites/reconstruction.
The full weak/strong sequence and each expanded count are identical. -/
theorem preIndexedX_lower (env : LowerEnv α) (hl : LiteralCounts env) (n : HNode) :
    lower env (preIndexedX n) = lower env n := by
  cases n <;> try rfl
  case unary k arg =>
    cases k <;> try rfl
    all_goals simp only [preIndexedX]
    case next => simp only [weakUnary_lower env hl, lower, preIndexedX_lower env hl arg]
    all_goals simp only [lower, preIndexedX_lower env hl arg]
  case nextN s count body =>
    simp only [preIndexedX, indexed_lower env hl, lower, preIndexedX_lower env hl body]
  case binary k l r =>
    cases k <;> try rfl
    all_goals simp only [preIndexedX, lower, preIndexedX_lower env hl l,
      preIndexedX_lower env hl r]
termination_by sizeOf n

theorem preIndexedX_sat (env : LowerEnv α) (hl : LiteralCounts env) (n : HNode)
    (len : Option Nat) (w : Word α) (j : Nat) :
    Sat len w (lower env (preIndexedX n)) j ↔ Sat len w (lower env n) j := by
  rw [preIndexedX_lower env hl]

theorem preIndexedX_finite (env : LowerEnv α) (hl : LiteralCounts env) (f : HNode)
    (n : Nat) : ∀ w j, j < n →
    (Sat (some n) w (lower env (preIndexedX f)) j ↔ Sat (some n) w (lower env f) j) :=
  fun w j _ => preIndexedX_sat env hl f (some n) w j

theorem preIndexedX_infinite (env : LowerEnv α) (hl : LiteralCounts env) (f : HNode) :
    ∀ w j, Sat none w (lower env (preIndexedX f)) j ↔ Sat none w (lower env f) j :=
  fun w j => preIndexedX_sat env hl f none w j

/-- Kernel-computed boundary/reconstruction witnesses mirrored in next_strength.c.
No expansion of max64 next constructors is needed to check the guards. -/
theorem branch_witnesses (s : Bool) :
    preIndexedX (.nextN s (.int 0) .tt) = .tt ∧
    preIndexedX (.nextN s (.int 1) (.nextN s (.int 2) .tt)) = .nextN s (.int 3) .tt ∧
    preIndexedX (.nextN s (.int (max64 - 1)) (.nextN s (.int 1) .tt)) =
      .nextN s (.int max64) .tt ∧
    preIndexedX (.nextN s (.int max64) (.nextN s (.int 1) .tt)) =
      .nextN s (.int max64) (.nextN s (.int 1) .tt) ∧
    preIndexedX (.nextN s (.ap "k") (.unary .neg (.nextN false (.int 0) .tt))) =
      .nextN s (.ap "k") (.unary .neg .tt) ∧
    preIndexedX (.nextN s (.int 1) (.unary .neg (.nextN false (.int 0) .tt))) =
      .nextN s (.int 1) (.unary .neg .tt) ∧
    preIndexedX (.unary .strongNext (.unary .neg (.nextN s (.int 0) .tt))) =
      .unary .strongNext (.unary .neg .tt) := by
  cases s <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original #117 loss of strength is visible on every one-letter word. -/
theorem issue117_terminal (w : Word α) :
    ¬Sat (some 1) w (.strongNext (.next .tt)) 0 ∧
      Sat (some 1) w (.next (.next .tt)) 0 ∧
      Sat (some 1) w (.next (.strongNext .tt)) 0 ∧
      ¬Sat (some 2) w (.next (.strongNext .tt)) 0 := by
  simp [Sat, InRange]

end Tlsf.NextStrength
