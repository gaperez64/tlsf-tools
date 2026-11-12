import Init

namespace Tlsf.IntegerLiteral

def min64 : Int := -9223372036854775808
def max64 : Int := 9223372036854775807
def magnitudeLimit : Nat := 9223372036854775808
def Fits (i : Int) : Prop := min64 ≤ i ∧ i ≤ max64

/-- Mathematical signed-64 payloads, without a wrapping machine cast. -/
abbrev I64 := { i : Int // Fits i }

instance (i : Int) : Decidable (Fits i) :=
  inferInstanceAs (Decidable (min64 ≤ i ∧ i ≤ max64))

def checked (i : Int) : Option I64 :=
  if h : Fits i then some ⟨i, h⟩ else none

/-- Nonempty lists of decimal digits model the lexer's [0-9]+ tokens.
Leading zeroes are retained; whitespace/comments have already been skipped. -/
abbrev Digits := List (Fin 10)

def decimal (ds : Digits) : Nat :=
  ds.foldl (fun n d => 10 * n + d.val) 0

inductive Token where
  | integer (n : Nat)
  | minMagnitude
  deriving DecidableEq

/-- Port of the strtoull/ERANGE guard, not a verification of libc strtoull.
Its mathematical result cannot saturate, even for arbitrarily long tokens. -/
def lex (ds : Digits) : Option Token :=
  if ds = [] then none
  else if decimal ds > magnitudeLimit then none
  else if decimal ds = magnitudeLimit then some .minMagnitude
  else some (.integer (decimal ds))

theorem lex_rejects_large (h : magnitudeLimit < decimal ds) : lex ds = none := by
  simp [lex, h]

theorem lex_min_magnitude (hne : ds ≠ []) (h : decimal ds = magnitudeLimit) :
    lex ds = some .minMagnitude := by simp [lex, hne, h]

theorem leading_zero (ds : Digits) : decimal (⟨0, by decide⟩ :: ds) = decimal ds := rfl

inductive Syntax where
  | digits (ds : Digits)
  | minus (s : Syntax)
  | paren (s : Syntax)
  deriving DecidableEq

def sourceValue : Syntax → Int
  | .digits ds => (decimal ds : Int)
  | .minus s => -sourceValue s
  | .paren s => sourceValue s

inductive Node where
  | integer (i : Int)
  | neg (n : Node)
  deriving DecidableEq

def nodeValue : Node → Int
  | .integer i => i
  | .neg n => -nodeValue n

/-- The ordinary unary rule makes NODE_INT_NEG. Only the direct token rule
MINUS MIN_MAGNITUDE makes NODE_INT(INT64_MIN); parentheses block that rule. -/
def parse : Syntax → Option Node
  | .digits ds => match lex ds with
      | some (.integer n) => some (.integer (Int.ofNat n))
      | _ => none
  | .minus (.digits ds) => match lex ds with
      | some .minMagnitude => some (.integer min64)
      | some (.integer n) => some (.neg (.integer (Int.ofNat n)))
      | none => none
  | .minus s => (parse s).map .neg
  | .paren s => parse s

/-- NODE_INT and checked 0-a from eval_int. This also rejects --2^63. -/
def eval : Node → Option I64
  | .integer i => checked i
  | .neg n => (eval n).bind (fun i => checked (-i.val))

def decode (s : Syntax) : Option I64 := (parse s).bind eval

theorem checked_value (h : checked i = some v) : v.val = i := by
  unfold checked at h
  split at h
  · simp only [Option.some.injEq] at h
    cases h
    rfl
  · contradiction

theorem eval_exact (h : eval n = some v) : v.val = nodeValue n := by
  induction n generalizing v with
  | integer i => exact checked_value h
  | neg n ih =>
      simp only [eval] at h
      cases he : eval n with
      | none => simp [he] at h
      | some a =>
          simp only [he, Option.bind_some] at h
          exact (checked_value h).trans (congrArg Neg.neg (ih he))

theorem lex_integer_iff : lex ds = some (.integer n) ↔
    ds ≠ [] ∧ decimal ds < magnitudeLimit ∧ decimal ds = n := by
  by_cases h : decimal ds = magnitudeLimit <;> simp [lex, h] <;> omega

theorem lex_min_iff : lex ds = some .minMagnitude ↔
    ds ≠ [] ∧ decimal ds = magnitudeLimit := by
  simp [lex]
  omega

theorem parse_exact (h : parse s = some n) : nodeValue n = sourceValue s := by
  induction s generalizing n with
  | digits ds =>
      simp only [parse] at h
      cases ht : lex ds with
      | none => simp [ht] at h
      | some t =>
          cases t with
          | minMagnitude => simp [ht] at h
          | integer a =>
              simp only [ht, Option.some.injEq] at h
              cases h
              exact congrArg Int.ofNat (lex_integer_iff.mp ht).2.2.symm
  | paren s ih => exact ih h
  | minus s ih =>
      cases s with
      | digits ds =>
          simp only [parse] at h
          cases ht : lex ds with
          | none => simp [ht] at h
          | some t =>
              cases t with
              | integer a =>
                  simp only [ht, Option.some.injEq] at h
                  cases h
                  simp only [nodeValue, sourceValue, (lex_integer_iff.mp ht).2.2]
                  rfl
              | minMagnitude =>
                  simp only [ht, Option.some.injEq] at h
                  cases h
                  simp only [nodeValue, sourceValue, (lex_min_iff.mp ht).2]
                  rfl
      | minus s =>
          simp only [parse] at h
          cases hp : parse (.minus s) with
          | none => simp [hp] at h
          | some a =>
              simp only [hp, Option.map_some, Option.some.injEq] at h
              cases h
              exact congrArg Neg.neg (ih hp)
      | paren s =>
          simp only [parse] at h
          cases hp : parse s with
          | none => simp [hp] at h
          | some a =>
              simp only [hp, Option.map_some, Option.some.injEq] at h
              cases h
              exact congrArg Neg.neg (ih hp)

def PayloadsFit : Node → Prop
  | .integer i => Fits i
  | .neg n => PayloadsFit n

theorem lex_integer_fits (h : lex ds = some (.integer n)) : Fits (n : Int) := by
  have ht := lex_integer_iff.mp h
  simp only [Fits, min64, max64, magnitudeLimit] at *
  omega

/-- Every parsed NODE_INT payload fits already. The mathematical check at a
leaf in eval is redundant, matching C's unconditional NODE_INT return. -/
theorem parse_payloads_fit (h : parse s = some n) : PayloadsFit n := by
  induction s generalizing n with
  | digits ds =>
      simp only [parse] at h
      cases ht : lex ds with
      | none => simp [ht] at h
      | some t =>
          cases t with
          | minMagnitude => simp [ht] at h
          | integer a =>
              simp only [ht, Option.some.injEq] at h
              cases h
              exact lex_integer_fits ht
  | paren s ih => exact ih h
  | minus s ih =>
      cases s with
      | digits ds =>
          simp only [parse] at h
          cases ht : lex ds with
          | none => simp [ht] at h
          | some t =>
              cases t with
              | integer a =>
                  simp only [ht, Option.some.injEq] at h
                  cases h
                  exact lex_integer_fits ht
              | minMagnitude =>
                  simp only [ht, Option.some.injEq] at h
                  cases h
                  change Fits min64
                  decide
      | minus s =>
          simp only [parse] at h
          cases hp : parse (.minus s) with
          | none => simp [hp] at h
          | some a =>
              simp only [hp, Option.map_some, Option.some.injEq] at h
              cases h
              change PayloadsFit a
              exact ih hp
      | paren s =>
          simp only [parse] at h
          cases hp : parse s with
          | none => simp [hp] at h
          | some a =>
              simp only [hp, Option.map_some, Option.some.injEq] at h
              cases h
              change PayloadsFit a
              exact ih hp

/-- Every successfully evaluated parsed spelling has its mathematical value
and is representable; syntactic acceptance alone need not imply evaluation. -/
theorem decode_exact (h : decode s = some v) : v.val = sourceValue s ∧ Fits v.val := by
  simp only [decode] at h
  cases hp : parse s with
  | none => simp [hp] at h
  | some n =>
      simp only [hp, Option.bind_some] at h
      exact ⟨(eval_exact h).trans (parse_exact hp), v.property⟩

/-- Complete admission rules for unsigned and directly negated tokens. -/
theorem positive_acceptance : (decode (.digits ds)).isSome = true ↔
    ds ≠ [] ∧ decimal ds < magnitudeLimit := by
  by_cases hn : ds = []
  · simp [hn, decode, parse, lex]
  by_cases hg : magnitudeLimit < decimal ds
  · simp [decode, parse, lex, hn, hg] <;> omega
  by_cases he : decimal ds = magnitudeLimit
  · simp [decode, parse, lex, hn, he]
  have hf : Fits (decimal ds : Int) := by
    simp only [Fits, min64, max64, magnitudeLimit] at *
    omega
  have hlt : decimal ds < magnitudeLimit := by omega
  simp [decode, parse, lex, hn, hg, he, eval, checked, hf, hlt]

theorem negative_acceptance : (decode (.minus (.digits ds))).isSome = true ↔
    ds ≠ [] ∧ decimal ds ≤ magnitudeLimit := by
  by_cases hn : ds = []
  · simp [hn, decode, parse, lex]
  by_cases hg : magnitudeLimit < decimal ds
  · simp [decode, parse, lex, hn, hg] <;> omega
  by_cases he : decimal ds = magnitudeLimit
  · simp [decode, parse, lex, hn, he, eval, checked, Fits, min64, max64]
    rfl
  have hf : Fits (decimal ds : Int) := by
    simp only [Fits, min64, max64, magnitudeLimit] at *
    omega
  have hneg : Fits (-(decimal ds : Int)) := by
    simp only [Fits, min64, max64, magnitudeLimit] at *
    omega
  have hle : decimal ds ≤ magnitudeLimit := by omega
  simp [decode, parse, lex, hn, hg, he, eval, checked, hf, hneg, hle]

theorem minimum_direct (hne : ds ≠ []) (hm : decimal ds = magnitudeLimit) :
    parse (.minus (.digits ds)) = some (.integer min64) ∧
      (decode (.minus (.digits ds))).isSome = true := by
  simp [parse, lex_min_magnitude hne hm, decode, eval, checked, Fits, min64, max64]
  rfl

theorem minimum_positive_rejected (hne : ds ≠ []) (hm : decimal ds = magnitudeLimit) :
    parse (.digits ds) = none ∧ parse (.minus (.paren (.digits ds))) = none := by
  simp [parse, lex_min_magnitude hne hm]

theorem minimum_negation_rejected : eval (.neg (.integer min64)) = none := by
  decide

/-- C's empty-domain guard precedes both strict endpoint shifts. -/
def endpoints (lo hi : Int) (ls us : Bool) : Option (Int × Int) :=
  if (ls = true ∧ lo = max64) ∨ (us = true ∧ hi = min64) then none
  else some (if ls then lo + 1 else lo, if us then hi - 1 else hi)

def Member (bounds : Option (Int × Int)) (k : Int) : Prop :=
  match bounds with
  | none => False
  | some (first, last) => first ≤ k ∧ k ≤ last

def SourceMember (lo hi : Int) (ls us : Bool) (k : Int) : Prop :=
  (if ls then lo < k else lo ≤ k) ∧ (if us then k < hi else k ≤ hi)

theorem endpoints_safe (hl : Fits lo) (hh : Fits hi)
    (h : endpoints lo hi ls us = some (first, last)) : Fits first ∧ Fits last := by
  cases ls <;> cases us <;>
    simp_all [endpoints, Fits, min64, max64] <;> omega

/-- Exact membership for all mathematical integers, including outside int64.
Inverted and strict-extreme ranges are empty, never saturated intervals. -/
theorem endpoints_exact (hl : Fits lo) (hh : Fits hi) :
    Member (endpoints lo hi ls us) k ↔ SourceMember lo hi ls us k := by
  cases ls <;> cases us <;>
    simp_all [endpoints, Member, SourceMember, Fits, min64, max64] <;>
    split <;> simp_all <;> omega

/-- Mathematical materialization of an inclusive interval, including first>last. -/
def values (first last : Int) : List Int :=
  (List.range (last - first + 1).toNat).map (fun (n : Nat) => first + (n : Int))

theorem values_exact : k ∈ values first last ↔ first ≤ k ∧ k ≤ last := by
  simp only [values, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro ⟨hlo, hhi⟩
    refine ⟨(k - first).toNat, ?_, ?_⟩ <;> omega

/-- The C loop's MAX guard prevents an overflowing successor. -/
theorem successor_safe (h : Fits k) (hne : k ≠ max64) : Fits (k + 1) := by
  simp only [Fits, min64, max64] at *
  omega

theorem decoded_range_exact (hl : decode l = some lo) (hh : decode h = some hi) :
    Member (endpoints lo.val hi.val ls us) k ↔
      SourceMember (sourceValue l) (sourceValue h) ls us k := by
  have el := decode_exact hl
  have eh := decode_exact hh
  rw [endpoints_exact el.2 eh.2, el.1, eh.1]

def domainValues (lo hi : Int) (ls us : Bool) : List Int :=
  match endpoints lo hi ls us with
  | none => []
  | some (first, last) => values first last

theorem domain_values_exact (hl : Fits lo) (hh : Fits hi) :
    k ∈ domainValues lo hi ls us ↔ SourceMember lo hi ls us k := by
  rw [← endpoints_exact hl hh]
  unfold domainValues
  cases endpoints lo hi ls us with
  | none => simp [Member]
  | some pair => cases pair; exact values_exact

theorem decoded_values_exact (hl : decode l = some lo) (hh : decode h = some hi) :
    k ∈ domainValues lo.val hi.val ls us ↔
      SourceMember (sourceValue l) (sourceValue h) ls us k := by
  have el := decode_exact hl
  have eh := decode_exact hh
  rw [domain_values_exact el.2 eh.2, el.1, eh.1]

/-- Same position guard as LTL.Sat; no dependency on game semantics. -/
def inWord (len : Option Nat) (j : Nat) : Prop :=
  match len with | none => True | some n => j < n

/-- Formula-language preservation before game reduction. body is the original
body's denotation with k bound, on any finite/infinite word and position.
No ownership, Mealy/Moore, or player-complement convention occurs here. -/
theorem range_all_denotation (hl : decode l = some lo) (hh : decode h = some hi)
    (body : Int → Option Nat → (Nat → α → Bool) → Nat → Prop)
    (len : Option Nat) (w : Nat → α → Bool) (j : Nat) :
    (inWord len j ∧ ∀ k, k ∈ domainValues lo.val hi.val ls us → body k len w j) ↔
      (inWord len j ∧
        ∀ k, SourceMember (sourceValue l) (sourceValue h) ls us k → body k len w j) := by
  simp only [decoded_values_exact hl hh]

theorem range_any_denotation (hl : decode l = some lo) (hh : decode h = some hi)
    (body : Int → Option Nat → (Nat → α → Bool) → Nat → Prop)
    (len : Option Nat) (w : Nat → α → Bool) (j : Nat) :
    (inWord len j ∧ ∃ k, k ∈ domainValues lo.val hi.val ls us ∧ body k len w j) ↔
      (inWord len j ∧
        ∃ k, SourceMember (sourceValue l) (sourceValue h) ls us k ∧ body k len w j) := by
  simp only [decoded_values_exact hl hh]

/-- Kernel-computed witnesses matching the C unit's boundary spellings. -/
def maxDigits : Digits := [9,2,2,3,3,7,2,0,3,6,8,5,4,7,7,5,8,0,7]
def minDigits : Digits := [9,2,2,3,3,7,2,0,3,6,8,5,4,7,7,5,8,0,8]
def largeDigits : Digits := [9,2,2,3,3,7,2,0,3,6,8,5,4,7,7,5,8,0,9]

theorem boundary_witnesses :
    (decode (.digits maxDigits)).isSome = true ∧
    parse (.digits minDigits) = none ∧
    parse (.minus (.digits minDigits)) = some (.integer min64) ∧
    parse (.minus (.digits (0 :: minDigits))) = some (.integer min64) ∧
    parse (.minus (.paren (.digits minDigits))) = none ∧
    lex largeDigits = none := by decide

end Tlsf.IntegerLiteral
