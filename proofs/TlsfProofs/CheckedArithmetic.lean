import Init
import TlsfProofs.IntegerLiteral

namespace Tlsf.CheckedArithmetic

open IntegerLiteral

inductive Op where
  | add | sub | mul | div | mod
  deriving DecidableEq

/-- C division truncates toward zero; Lean's ordinary / and % use Euclidean division. -/
def operation : Op → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a.tdiv b
  | .mod, a, b => a.tmod b

/-- Remainder must reject MIN / -1 too, even though its mathematical result is zero. -/
def Allowed (op : Op) (a b : Int) : Prop :=
  match op with
  | .div | .mod => b ≠ 0 ∧ ¬(a = min64 ∧ b = -1)
  | _ => True

instance : Decidable (Allowed op a b) := by cases op <;> unfold Allowed <;> infer_instance

def apply (op : Op) (a b : I64) : Option I64 :=
  if Allowed op a.val b.val then checked (operation op a.val b.val) else none

theorem checked_iff : checked i = some v ↔ Fits i ∧ v.val = i := by
  constructor
  · intro h
    exact ⟨(checked_value h) ▸ v.property, checked_value h⟩
  · rintro ⟨hi, hv⟩
    simp only [checked, dite_eq_left hi, Option.some.injEq]
    exact Subtype.ext hv.symm

theorem apply_iff : apply op a b = some v ↔
    Allowed op a.val b.val ∧ Fits (operation op a.val b.val) ∧
      v.val = operation op a.val b.val := by
  simp only [apply]
  split <;> simp_all [checked_iff]

theorem negation_as_sub (i : Int) : 0 - i = -i := by omega

private theorem abs_bound (h : Fits i) : i.natAbs ≤ magnitudeLimit := by
  cases i <;> simp_all [Fits, min64, max64, magnitudeLimit, Int.natAbs] <;> omega

private theorem fits_of_abs_lt {i : Int} (h : i.natAbs < magnitudeLimit) : Fits i := by
  cases i <;> simp_all [Fits, min64, max64, magnitudeLimit, Int.natAbs] <;> omega

/-- The C division branch needs only its two explicit guards; a second result
range check in apply is redundant for int64 inputs. -/
theorem division_fits (ha : Fits a) (h : Allowed .div a b) : Fits (a.tdiv b) := by
  by_cases hm : a = min64
  · subst a
    by_cases hb : b = 1
    · simpa [hb] using ha
    have hn : b ≠ -1 := fun hb => h.2 ⟨rfl, hb⟩
    have hg : 1 < b.natAbs := by
      have hz := h.1
      cases b <;> simp_all [Int.natAbs] <;> omega
    apply fits_of_abs_lt
    rw [Int.natAbs_tdiv]
    exact Nat.div_lt_self (by decide) hg
  · have ht : a.natAbs < magnitudeLimit := by
      cases a <;> simp_all [Fits, min64, max64, magnitudeLimit, Int.natAbs] <;> omega
    exact fits_of_abs_lt (Nat.lt_of_le_of_lt (Int.natAbs_tdiv_le_natAbs a b) ht)

/-- The mathematical remainder fits even for MIN % -1; C still forbids that operation. -/
theorem remainder_fits {a : Int} (hb : Fits b) (hz : b ≠ 0) : Fits (a.tmod b) := by
  apply fits_of_abs_lt
  rw [Int.natAbs_tmod]
  have hp : 0 < b.natAbs := by cases b <;> simp_all [Int.natAbs] <;> omega
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) (abs_bound hb)

theorem division_guard_exact (a b v : I64) : apply .div a b = some v ↔
    Allowed .div a.val b.val ∧ v.val = a.val.tdiv b.val := by
  rw [apply_iff]
  constructor
  · intro h; exact ⟨h.1, h.2.2⟩
  · intro h; exact ⟨h.1, division_fits a.property h.1, h.2⟩

theorem remainder_guard_exact (a b v : I64) : apply .mod a b = some v ↔
    Allowed .mod a.val b.val ∧ v.val = a.val.tmod b.val := by
  rw [apply_iff]
  constructor
  · intro h; exact ⟨h.1, h.2.2⟩
  · intro h; exact ⟨h.1, remainder_fits b.property h.1.1, h.2⟩

/-- The reduction's left-to-right accumulator, also used for supplied set domains. -/
def foldValue (op : Op) (body : Int → Int) : List Int → Int → Int
  | [], acc => acc
  | k :: ks, acc => foldValue op body ks (operation op acc (body k))

/-- Every intermediate prefix must fit, even if later cancellation/zero would fit. -/
def FoldDefined (op : Op) (body : Int → Int) (bodyDefined : Int → Prop) :
    List Int → Int → Prop
  | [], _ => True
  | k :: ks, acc => bodyDefined k ∧ Allowed op acc (body k) ∧
      Fits (operation op acc (body k)) ∧
      FoldDefined op body bodyDefined ks (operation op acc (body k))

def evalFold (op : Op) (body : Int → Option I64) : List Int → I64 → Option I64
  | [], acc => some acc
  | k :: ks, acc => (body k).bind (fun value =>
      (apply op acc value).bind (fun next => evalFold op body ks next))

theorem evalFold_iff
    (hb : ∀ k v, run k = some v ↔ defined k ∧ v.val = body k)
    (hfitBody : ∀ k, defined k → Fits (body k)) :
    evalFold op run ks acc = some v ↔
      FoldDefined op body defined ks acc.val ∧ v.val = foldValue op body ks acc.val := by
  induction ks generalizing acc with
  | nil => simp [evalFold, FoldDefined, foldValue, Subtype.ext_iff, eq_comm]
  | cons k ks ih =>
      simp only [evalFold, FoldDefined, foldValue]
      constructor
      · intro h
        cases hr : run k with
        | none => simp [hr] at h
        | some a =>
            have ha := (hb k a).mp hr
            cases hn : apply op acc a with
            | none => simp [hr, hn] at h
            | some next =>
                simp only [hr, hn, Option.bind_some] at h
                have hp := apply_iff.mp hn
                have ht := (ih (acc := next)).mp h
                rw [ha.2] at hp
                rw [hp.2.2] at ht
                exact ⟨⟨ha.1, hp.1, hp.2.1, ht.1⟩, ht.2⟩
      · rintro ⟨⟨hd, hop, hfit, htail⟩, hv⟩
        let a : I64 := ⟨body k, hfitBody k hd⟩
        have hr := (hb k a).mpr ⟨hd, rfl⟩
        let next : I64 := ⟨operation op acc.val (body k), hfit⟩
        have hn : apply op acc a = some next := apply_iff.mpr ⟨hop, hfit, rfl⟩
        simp only [hr, hn, Option.bind_some]
        exact (ih (acc := next)).mpr ⟨htail, hv⟩

theorem fold_defined_fits (ha : Fits acc)
    (h : FoldDefined op body defined ks acc) : Fits (foldValue op body ks acc) := by
  induction ks generalizing acc with
  | nil => exact ha
  | cons k ks ih => exact ih h.2.2.1 h.2.2.2

/-- Only addition and multiplication are reduction accumulator operations. -/
def accumulator (product : Bool) : Op := if product then .mul else .add

def seed (product : Bool) : I64 :=
  if product then ⟨1, by decide⟩ else ⟨0, by decide⟩

abbrev Environment := Nat → Int

def bind (rho : Environment) (name : Nat) (value : Int) : Environment :=
  fun x => if x = name then value else rho x

/-- Numeric AST after trusted definition/ITE/bus/set resolution. suppliedReduce
retains the materialized set's order; rangeReduce evaluates its endpoints itself.
Names abstract interned identifiers; binding masks an outer name. -/
inductive Expr where
  | integer (value : Int)
  | lookup (name : Nat)
  | neg (arg : Expr)
  | binary (op : Op) (lhs rhs : Expr)
  | rangeReduce (product : Bool) (name : Nat) (lo hi : Expr) (ls us : Bool) (body : Expr)
  | suppliedReduce (product : Bool) (name : Nat) (domain : List Int) (body : Expr)

/-- Unbounded integer denotation, with C's truncating quotient and remainder.
For defined range endpoints, #116 establishes the list's source membership. -/
def denote : Expr → Environment → Int
  | .integer i, _ => i
  | .lookup x, rho => rho x
  | .neg e, rho => -denote e rho
  | .binary op l r, rho => operation op (denote l rho) (denote r rho)
  | .rangeReduce p x lo hi ls us body, rho =>
      foldValue (accumulator p) (fun k => denote body (bind rho x k))
        (domainValues (denote lo rho) (denote hi rho) ls us) (seed p).val
  | .suppliedReduce p x domain body, rho =>
      foldValue (accumulator p) (fun k => denote body (bind rho x k)) domain (seed p).val

/-- Independent safety predicate: every evaluated child and accumulator prefix
is defined and representable, not merely the final mathematical result. -/
def Defined : Expr → Environment → Prop
  | .integer i, _ => Fits i
  | .lookup x, rho => Fits (rho x)
  | .neg e, rho => Defined e rho ∧ Fits (-denote e rho)
  | .binary op l r, rho => Defined l rho ∧ Defined r rho ∧
      Allowed op (denote l rho) (denote r rho) ∧ Fits (operation op (denote l rho) (denote r rho))
  | .rangeReduce p x lo hi ls us body, rho => Defined lo rho ∧ Defined hi rho ∧
      FoldDefined (accumulator p) (fun k => denote body (bind rho x k))
        (fun k => Defined body (bind rho x k))
        (domainValues (denote lo rho) (denote hi rho) ls us) (seed p).val
  | .suppliedReduce p x domain body, rho =>
      FoldDefined (accumulator p) (fun k => denote body (bind rho x k))
        (fun k => Defined body (bind rho x k)) domain (seed p).val

def eval : Expr → Environment → Option I64
  | .integer i, _ => checked i
  | .lookup x, rho => checked (rho x)
  | .neg e, rho => (eval e rho).bind (fun a => checked (-a.val))
  | .binary op l r, rho => (eval l rho).bind (fun a =>
      (eval r rho).bind (fun b => apply op a b))
  | .rangeReduce p x lo hi ls us body, rho => (eval lo rho).bind (fun l =>
      (eval hi rho).bind (fun h =>
        evalFold (accumulator p) (fun k => eval body (bind rho x k))
          (domainValues l.val h.val ls us) (seed p)))
  | .suppliedReduce p x domain body, rho =>
      evalFold (accumulator p) (fun k => eval body (bind rho x k)) domain (seed p)

theorem defined_fits (h : Defined e rho) : Fits (denote e rho) := by
  cases e with
  | integer _ => exact h
  | lookup _ => exact h
  | neg _ => exact h.2
  | binary _ _ _ => exact h.2.2.2
  | rangeReduce p _ _ _ _ _ _ => exact fold_defined_fits (seed p).property h.2.2
  | suppliedReduce p _ _ _ => exact fold_defined_fits (seed p).property h

/-- Complete contract for numeric evaluation, including every reduction prefix. -/
theorem eval_iff : eval e rho = some v ↔ Defined e rho ∧ v.val = denote e rho := by
  induction e generalizing rho v with
  | integer i => exact checked_iff
  | lookup x => exact checked_iff
  | neg e ih =>
      simp only [eval]
      constructor
      · intro h
        cases he : eval e rho with
        | none => simp [he] at h
        | some a =>
            simp only [he, Option.bind_some] at h
            have ha := ih.mp he
            have hv := checked_iff.mp h
            rw [ha.2] at hv
            exact ⟨⟨ha.1, hv.1⟩, hv.2⟩
      · rintro ⟨⟨hd, hf⟩, hv⟩
        let a : I64 := ⟨denote e rho, defined_fits hd⟩
        rw [(ih (v := a)).mpr ⟨hd, rfl⟩]
        exact checked_iff.mpr ⟨hf, hv⟩
  | binary op l r il ir =>
      simp only [eval]
      constructor
      · intro h
        cases hl : eval l rho with
        | none => simp [hl] at h
        | some a =>
            cases hr : eval r rho with
            | none => simp [hl, hr] at h
            | some b =>
                simp only [hl, hr, Option.bind_some] at h
                have ha := il.mp hl
                have hb := ir.mp hr
                have hp := apply_iff.mp h
                rw [ha.2, hb.2] at hp
                exact ⟨⟨ha.1, hb.1, hp.1, hp.2.1⟩, hp.2.2⟩
      · rintro ⟨⟨hl, hr, hop, hf⟩, hv⟩
        let a : I64 := ⟨denote l rho, defined_fits hl⟩
        let b : I64 := ⟨denote r rho, defined_fits hr⟩
        rw [(il (v := a)).mpr ⟨hl, rfl⟩, (ir (v := b)).mpr ⟨hr, rfl⟩]
        exact apply_iff.mpr ⟨hop, hf, hv⟩
  | rangeReduce p x lo hi ls us body il ih ib =>
      simp only [eval]
      constructor
      · intro h
        cases hl : eval lo rho with
        | none => simp [hl] at h
        | some a =>
            cases hh : eval hi rho with
            | none => simp [hl, hh] at h
            | some b =>
                simp only [hl, hh, Option.bind_some] at h
                have ha := il.mp hl
                have hb := ih.mp hh
                have ht := (evalFold_iff (fun k v => ib) (fun k => defined_fits)).mp h
                rw [ha.2, hb.2] at ht
                exact ⟨⟨ha.1, hb.1, ht.1⟩, ht.2⟩
      · rintro ⟨⟨hl, hh, ht⟩, hv⟩
        let a : I64 := ⟨denote lo rho, defined_fits hl⟩
        let b : I64 := ⟨denote hi rho, defined_fits hh⟩
        rw [(il (v := a)).mpr ⟨hl, rfl⟩, (ih (v := b)).mpr ⟨hh, rfl⟩]
        exact (evalFold_iff (fun k v => ib) (fun k => defined_fits)).mpr ⟨ht, hv⟩
  | suppliedReduce p x domain body ib =>
      exact evalFold_iff (fun k v => ib) (fun k => defined_fits)

theorem eval_exact (h : eval e rho = some v) :
    v.val = denote e rho ∧ Fits v.val ∧ Defined e rho :=
  ⟨(eval_iff.mp h).2, v.property, (eval_iff.mp h).1⟩

/-- Failure carries no numeric result; no partial accumulator is returned. C
builtin scratch writes on false are not published values (callers test bool). -/
theorem eval_rejects : eval e rho = none ↔ ¬Defined e rho := by
  constructor
  · intro h hd
    have hv := (eval_iff (v := ⟨denote e rho, defined_fits hd⟩)).mpr ⟨hd, rfl⟩
    rw [h] at hv
    contradiction
  · intro h
    cases he : eval e rho with
    | none => rfl
    | some v => exact False.elim (h (eval_iff.mp he).1)

/-- Reuse #116's parsed AST and decoding result at the numeric frontend boundary. -/
def literalExpr : IntegerLiteral.Node → Expr
  | .integer i => .integer i
  | .neg n => .neg (literalExpr n)

theorem literal_eval : eval (literalExpr n) rho = IntegerLiteral.eval n := by
  induction n with
  | integer _ => rfl
  | neg n ih => simp only [literalExpr, eval, IntegerLiteral.eval, ih]

theorem literal_denote : denote (literalExpr n) rho = nodeValue n := by
  induction n with
  | integer _ => rfl
  | neg n ih => simp only [literalExpr, denote, nodeValue, ih]

theorem parsed_literal_exact (hp : parse s = some n) (he : eval (literalExpr n) rho = some v) :
    v.val = sourceValue s := by
  exact (eval_exact he).1.trans (literal_denote.trans (parse_exact hp))

/-- Domain publication happens only after both endpoint evaluations succeed. -/
def evalDomain (lo hi : Expr) (rho : Environment) (ls us : Bool) : Option (List Int) :=
  (eval lo rho).bind (fun l => (eval hi rho).map (fun h => domainValues l.val h.val ls us))

theorem eval_domain_exact (h : evalDomain lo hi rho ls us = some domain) :
    Defined lo rho ∧ Defined hi rho ∧
    (∀ k, k ∈ domain ↔ Fits k ∧ SourceMember (denote lo rho) (denote hi rho) ls us k) := by
  unfold evalDomain at h
  cases hl : eval lo rho with
  | none => simp [hl] at h
  | some a =>
      cases hh : eval hi rho with
      | none => simp [hl, hh] at h
      | some b =>
          simp only [hl, hh, Option.bind_some, Option.map_some, Option.some.injEq] at h
          have ha := eval_iff.mp hl
          have hb := eval_iff.mp hh
          refine ⟨ha.1, hb.1, ?_⟩
          intro k
          rw [← h, domain_values_exact a.property b.property, ha.2, hb.2]
          have hf := defined_fits ha.1
          have hg := defined_fits hb.1
          cases ls <;> cases us <;>
            simp only [SourceMember, Bool.false_eq_true, ↓reduceIte, Fits] at * <;> omega

theorem domain_rejects_endpoint
    (h : eval lo rho = none ∨ eval hi rho = none) : evalDomain lo hi rho ls us = none := by
  rcases h with h | h <;> simp [evalDomain, h]


/-- This is the same domain consumed by the numeric loop, not a second endpoint implementation. -/
theorem eval_range_reduction :
    eval (.rangeReduce p x lo hi ls us body) rho =
      (evalDomain lo hi rho ls us).bind (fun domain =>
        evalFold (accumulator p) (fun k => eval body (bind rho x k)) domain (seed p)) := by
  cases hl : eval lo rho <;> cases hh : eval hi rho <;> simp [eval, evalDomain, hl, hh]

theorem sum_exact (h : eval (.rangeReduce false x lo hi ls us body) rho = some v) :
    Defined (.rangeReduce false x lo hi ls us body) rho ∧
    v.val = foldValue .add (fun k => denote body (bind rho x k))
      (domainValues (denote lo rho) (denote hi rho) ls us) 0 := eval_iff.mp h

theorem product_exact (h : eval (.rangeReduce true x lo hi ls us body) rho = some v) :
    Defined (.rangeReduce true x lo hi ls us body) rho ∧
    v.val = foldValue .mul (fun k => denote body (bind rho x k))
      (domainValues (denote lo rho) (denote hi rho) ls us) 1 := eval_iff.mp h

/-- The C formula loop starts at the first term, with true/false for an empty domain. -/
def formulaReduce (all : Bool) (domain : List Int) (body : Int → Prop) : Prop :=
  match domain with
  | [] => all = true
  | k :: ks => ks.foldl (fun acc k => if all then acc ∧ body k else acc ∨ body k) (body k)

theorem all_fold (ks : List Int) (body : Int → Prop) (initial : Prop) :
    ks.foldl (fun acc k => acc ∧ body k) initial ↔ initial ∧ ∀ k ∈ ks, body k := by
  induction ks generalizing initial with
  | nil => simp
  | cons k ks ih => simp only [List.foldl_cons, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem any_fold (ks : List Int) (body : Int → Prop) (initial : Prop) :
    ks.foldl (fun acc k => acc ∨ body k) initial ↔ initial ∨ ∃ k ∈ ks, body k := by
  induction ks generalizing initial with
  | nil => simp
  | cons k ks ih => simp only [List.foldl_cons, ih, List.mem_cons, exists_eq_or_imp, or_assoc]

theorem forall_exact : formulaReduce true domain body ↔ ∀ k ∈ domain, body k := by
  cases domain <;> simp [formulaReduce, all_fold]

theorem exists_exact : formulaReduce false domain body ↔ ∃ k ∈ domain, body k := by
  cases domain <;> simp [formulaReduce, any_fold]

/-- Original frontend formula denotations, at all positions of either word kind.
The arbitrary fixed body resolver is a stated trust boundary, not a game construction. -/
theorem range_all_denotation (h : evalDomain lo hi rho ls us = some domain)
    (body : Int → Option Nat → (Nat → α → Bool) → Nat → Prop)
    (len : Option Nat) (w : Nat → α → Bool) (j : Nat) :
    (inWord len j ∧ formulaReduce true domain (fun k => body k len w j)) ↔
      (inWord len j ∧ ∀ k, Fits k ∧ SourceMember (denote lo rho) (denote hi rho) ls us k →
        body k len w j) := by
  simp only [forall_exact, (eval_domain_exact h).2.2]

theorem range_any_denotation (h : evalDomain lo hi rho ls us = some domain)
    (body : Int → Option Nat → (Nat → α → Bool) → Nat → Prop)
    (len : Option Nat) (w : Nat → α → Bool) (j : Nat) :
    (inWord len j ∧ formulaReduce false domain (fun k => body k len w j)) ↔
      (inWord len j ∧ ∃ k, (Fits k ∧ SourceMember (denote lo rho) (denote hi rho) ls us k) ∧
        body k len w j) := by
  simp only [exists_exact, (eval_domain_exact h).2.2]

abbrev SetValue (α : Type) := α → Prop

/-- Extensional set-fold model; C equality/deduplication/storage remain trusted. -/
def setReduce (inter : Bool) (domain : List Int) (body : Int → SetValue α) :
    Option (SetValue α) :=
  match domain with
  | [] => if inter then none else some (fun _ => False)
  | k :: ks => some (fun value =>
      ks.foldl (fun acc k => if inter then acc ∧ body k value else acc ∨ body k value)
        (body k value))

/-- C union starts from the empty set; first-term seeding is extensionally identical. -/
theorem union_empty_seed :
    (setReduce false domain body).map (fun result => result value) =
      some (domain.foldl (fun acc k => acc ∨ body k value) False) := by
  cases domain <;> simp [setReduce]

theorem union_exact (h : setReduce false domain body = some result) :
    result value ↔ ∃ k ∈ domain, body k value := by
  cases domain with
  | nil => simp only [setReduce, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
           rw [← h]; simp
  | cons k ks =>
      simp only [setReduce, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      rw [← h]
      exact (any_fold ks (fun k => body k value) (body k value)).trans (by simp)

theorem intersection_exact (h : setReduce true domain body = some result) :
    domain ≠ [] ∧ (∀ value, result value ↔ ∀ k ∈ domain, body k value) := by
  cases domain with
  | nil => simp [setReduce] at h
  | cons k ks =>
      simp only [setReduce, ↓reduceIte, Option.some.injEq] at h
      refine ⟨by simp, ?_⟩
      intro value
      rw [← h]
      exact (all_fold ks (fun k => body k value) (body k value)).trans (by simp)

theorem range_union_exact (hd : evalDomain lo hi rho ls us = some domain)
    (h : setReduce false domain body = some result) :
    result value ↔ ∃ k, (Fits k ∧ SourceMember (denote lo rho) (denote hi rho) ls us k) ∧
      body k value := by
  simp only [union_exact h, (eval_domain_exact hd).2.2]

theorem range_intersection_exact (hd : evalDomain lo hi rho ls us = some domain)
    (h : setReduce true domain body = some result) :
    domain ≠ [] ∧ (∀ value, result value ↔
      ∀ k, Fits k ∧ SourceMember (denote lo rho) (denote hi rho) ls us k → body k value) := by
  simpa only [(eval_domain_exact hd).2.2] using intersection_exact h

/-- All six documented empty cases, including rejected empty intersection. -/
theorem six_empty_cases (numericBody : Int → Option I64) (formulaBody : Int → Prop)
    (setBody : Int → SetValue α) :
    formulaReduce true [] formulaBody ∧ ¬formulaReduce false [] formulaBody ∧
    evalFold .add numericBody [] (seed false) = some (seed false) ∧
    evalFold .mul numericBody [] (seed true) = some (seed true) ∧
    setReduce false [] setBody = some (fun _ => False) ∧ setReduce true [] setBody = none := by
  exact ⟨rfl, Bool.noConfusion, rfl, rfl, rfl, rfl⟩

/-- Kernel-computed boundary witnesses mirrored by checked_arithmetic.c. -/
theorem boundary_witnesses (rho : Environment) :
    eval (.binary .add (.integer max64) (.integer 0)) rho = checked max64 ∧
    eval (.binary .sub (.integer min64) (.integer 0)) rho = checked min64 ∧
    eval (.binary .mul (.integer min64) (.integer 1)) rho = checked min64 ∧
    eval (.binary .add (.integer max64) (.integer 1)) rho = none ∧
    eval (.binary .sub (.integer min64) (.integer 1)) rho = none ∧
    eval (.binary .mul (.integer max64) (.integer 2)) rho = none ∧
    eval (.neg (.integer min64)) rho = none ∧
    eval (.binary .div (.integer min64) (.integer (-1))) rho = none ∧
    eval (.binary .mod (.integer min64) (.integer (-1))) rho = none ∧
    eval (.binary .div (.integer (-7)) (.integer 3)) rho = checked (-2) ∧
    eval (.binary .mod (.integer (-7)) (.integer 3)) rho = checked (-1) := by
  simp only [eval]
  decide

/-- The final endpoints fit mathematically, but their overflowing children must fail. -/
def issue115 (op : Op) : Expr :=
  .binary .div (.binary op (.integer max64) (.integer (if op = .add then 1 else 2)))
    (.integer max64)

def issue115neg : Expr :=
  .binary .div (.neg (.binary .sub (.integer (-max64)) (.integer 1))) (.integer max64)

theorem issue115_rejected (rho : Environment) :
    denote (issue115 .add) rho = 1 ∧ denote (issue115 .mul) rho = 2 ∧
    denote issue115neg rho = 1 ∧
    eval (issue115 .add) rho = none ∧ eval (issue115 .mul) rho = none ∧
    eval issue115neg rho = none := by
  simp only [issue115, issue115neg, denote, eval]
  decide

def cancelledSum : Expr := .suppliedReduce false 0 [max64, 1, -1] (.lookup 0)
def zeroedProduct : Expr := .suppliedReduce true 0 [max64, 2, 0] (.lookup 0)

theorem prefix_overflow_rejected (rho : Environment) :
    denote cancelledSum rho = max64 ∧ denote zeroedProduct rho = 0 ∧
    eval cancelledSum rho = none ∧ eval zeroedProduct rho = none := by
  simp only [cancelledSum, zeroedProduct, denote, eval, evalFold, foldValue, bind,
    accumulator, seed, Bool.false_eq_true, ↓reduceIte]
  decide

end Tlsf.CheckedArithmetic
