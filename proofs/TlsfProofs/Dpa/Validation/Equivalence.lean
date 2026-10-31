import TlsfProofs.Dpa.Validation.Automaton
import TlsfProofs.Dpa.Zielonka

/-! Language comparison of finite complete deterministic max-odd automata.
For each pair of opposite-parity priority thresholds, search the product for
a reachable closed walk visiting both thresholds. Floyd closure is computed
and checked for reflexivity, edge inclusion and transitivity. The soundness
proof uses those checked properties, not a state correspondence. -/
namespace Tlsf.Dpa.Validation
variable {na nb alphabet : Nat}
abbrev Vertex (na nb : Nat) := Fin na × Fin nb
abbrev Matrix (na nb : Nat) := Vertex na nb → Vertex na nb → Bool
abbrev Arc (na nb alphabet : Nat) := Vertex na nb × Fin alphabet

def vertices (na nb : Nat) : List (Vertex na nb) :=
  (List.finRange na).flatMap (fun a => (List.finRange nb).map (fun b => (a,b)))

theorem mem_vertices (v : Vertex na nb) : v ∈ vertices na nb := by
  rcases v with ⟨a,b⟩
  simp [vertices]

def arcs (na nb alphabet : Nat) : List (Arc na nb alphabet) :=
  (vertices na nb).flatMap (fun v => (List.finRange alphabet).map (fun a => (v,a)))

theorem mem_arcs (e : Arc na nb alphabet) : e ∈ arcs na nb alphabet := by
  rcases e with ⟨⟨a,b⟩,c⟩
  simp [arcs, vertices]

/-- A data value prevents function eta expansion from recomputing earlier
Floyd layers at every matrix lookup in compiled code. -/
structure FrozenMatrix (na nb : Nat) where
  cells : Array Bool

def FrozenMatrix.get (R : FrozenMatrix na nb) : Matrix na nb :=
  fun x y => R.cells.getD ((x.1.val * nb + x.2.val) * (na*nb) + y.1.val * nb + y.2.val) false

def tabulate (R : Matrix na nb) : FrozenMatrix na nb :=
  let vs := vertices na nb
  ⟨(vs.flatMap (fun x => vs.map (R x))).toArray⟩

@[noinline] def closure (edge : Matrix na nb) : FrozenMatrix na nb :=
  (vertices na nb).foldl
    (fun R z => tabulate (fun x y => R.get x y || (R.get x z && R.get z y)))
    (tabulate (fun x y => decide (x = y) || edge x y))

def closedCheck (edge R : Matrix na nb) : Bool :=
  (vertices na nb).all (fun x => R x x && (vertices na nb).all (fun y =>
    (!edge x y || R x y) && (vertices na nb).all (fun z => !(R x y && R y z) || R x z)))

structure Closed (edge R : Matrix na nb) : Prop where
  refl : ∀ x, R x x = true
  edge : ∀ x y, edge x y = true → R x y = true
  trans : ∀ x y z, R x y = true → R y z = true → R x z = true

theorem closedCheck_sound (edge R : Matrix na nb) (h : closedCheck edge R = true) :
    Closed edge R := by
  have imp (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
    cases a <;> cases b <;> decide
  simp only [closedCheck, List.all_eq_true, Bool.and_eq_true, imp] at h
  exact ⟨fun x => (h x (mem_vertices x)).1,
    fun x y he => ((h x (mem_vertices x)).2 y (mem_vertices y)).1 he,
    fun x y z hxy hyz => ((h x (mem_vertices x)).2 y (mem_vertices y)).2
      z (mem_vertices z) ⟨hxy, hyz⟩⟩

variable (A : Parity (Fin alphabet) (Fin na)) (B : Parity (Fin alphabet) (Fin nb))

def target (e : Arc na nb alphabet) : Vertex na nb :=
  ((A.step e.1.1 e.2).1, (B.step e.1.2 e.2).1)

def leftPriority (e : Arc na nb alphabet) : Nat := (A.step e.1.1 e.2).2

def rightPriority (e : Arc na nb alphabet) : Nat := (B.step e.1.2 e.2).2

def graph (allow : Arc na nb alphabet → Bool) : Matrix na nb :=
  fun x y => (List.finRange alphabet).any (fun a => allow (x,a) && decide (target A B (x,a) = y))

def bounded (p q : Nat) (e : Arc na nb alphabet) : Bool :=
  decide (leftPriority A e ≤ p ∧ rightPriority B e ≤ q)

def badWalk (R C : Matrix na nb) (p q : Nat) (e f : Arc na nb alphabet) : Bool :=
  R (A.initial, B.initial) e.1 && bounded A B p q e && bounded A B p q f &&
    decide (leftPriority A e = p) && decide (rightPriority B f = q) &&
    C (target A B e) f.1 && C (target A B f) e.1

def thresholdCheck (R : Matrix na nb) (p q : Nat) : Bool :=
  if p % 2 = q % 2 then true else
    let edge := graph A B (bounded A B p q)
    let C := (closure edge).get
    closedCheck edge C &&
      (arcs na nb alphabet).all (fun e => (arcs na nb alphabet).all (fun f => !badWalk A B R C p q e f))

def leftPriorities : List Nat := ((arcs na nb alphabet).map (leftPriority A)).eraseDups

def rightPriorities : List Nat := ((arcs na nb alphabet).map (rightPriority B)).eraseDups

/-- Full finite-graph language check, with independently checked closures. -/
def check : Bool :=
  let edge := graph A B (fun _ => true)
  let R := (closure edge).get
  closedCheck edge R &&
    (leftPriorities (nb := nb) A).all (fun p => (rightPriorities (na := na) B).all (thresholdCheck A B R p))

variable {A B}

private theorem finite_often (xs : List α) (f : Nat → α) (P : Nat → Prop)
    (hf : ∀ n, f n ∈ xs) (hp : Often P) :
    ∃ x, x ∈ xs ∧ Often (fun n => f n = x ∧ P n) := by
  classical
  apply Classical.byContradiction
  intro h
  have hn : ∀ x, x ∈ xs → ∃ N, ∀ n, N ≤ n → ¬(f n = x ∧ P n) := by
    intro x hx
    apply (not_often _).mp
    intro ho
    exact h ⟨x, hx, ho⟩
  obtain ⟨N,hN⟩ := finite_eventually xs _ hn
  obtain ⟨n,hn,hp⟩ := hp N
  exact hN n hn (f n) (hf n) ⟨rfl,hp⟩

private theorem greatest_often (xs : List Nat) (f : Nat → Nat)
    (h : ∃ x, x ∈ xs ∧ Often (fun n => f n = x)) :
    ∃ p, p ∈ xs ∧ Often (fun n => f n = p) ∧
      ∀ q, q ∈ xs → Often (fun n => f n = q) → q ≤ p := by
  classical
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases ht : ∃ x, x ∈ xs ∧ Often (fun n => f n = x)
    · obtain ⟨p,hp,ho,hm⟩ := ih ht
      by_cases ha : Often (fun n => f n = a) ∧ p < a
      · refine ⟨a, by simp, ha.1, ?_⟩
        intro q hq hqf
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Nat.le_refl _
        · exact Nat.le_trans (hm q hq hqf) (by omega)
      · refine ⟨p, by simp [hp], ho, ?_⟩
        intro q hq hqf
        rcases List.mem_cons.mp hq with rfl | hq
        · have hh : ¬p < q := fun hh => ha ⟨hqf, hh⟩; omega
        · exact hm q hq hqf
    · obtain ⟨x,hx,ho⟩ := h
      have he : x = a := (List.mem_cons.mp hx).elim id (fun hx => False.elim (ht ⟨x,hx,ho⟩))
      subst x
      refine ⟨a, by simp, ho, ?_⟩
      intro q hq hqf
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Nat.le_refl _
      · exact False.elim (ht ⟨q,hq,hqf⟩)

private theorem recurrent_max (xs : List Nat) (f : Nat → Nat) (hf : ∀ n, f n ∈ xs) :
    ∃ p, p ∈ xs ∧ Often (fun n => f n = p) ∧ ∃ N, ∀ n, N ≤ n → f n ≤ p := by
  classical
  obtain ⟨x,hx,ho⟩ := finite_often xs f (fun _ => True) hf (fun N => ⟨N, Nat.le_refl _, trivial⟩)
  obtain ⟨p,hp,ho,hm⟩ := greatest_often xs f ⟨x,hx,fun N => by
    obtain ⟨n,hn,h⟩ := ho N; exact ⟨n,hn,h.1⟩⟩
  have he : ∀ q, q ∈ xs → ∃ N, ∀ n, N ≤ n → f n = q → q ≤ p := by
    intro q hq
    by_cases hqp : q ≤ p
    · exact ⟨0, fun _ _ _ => hqp⟩
    · obtain ⟨N,hN⟩ := (not_often _).mp (fun h => hqp (hm q hq h))
      exact ⟨N, fun n hn he => False.elim (hN n hn he)⟩
  obtain ⟨N,hN⟩ := finite_eventually xs _ he
  exact ⟨p,hp,ho,N,fun n hn => hN n hn (f n) (hf n) rfl⟩

private theorem maxOdd_recurrent_max (f : Nat → Nat) (p : Nat)
    (ho : Often (fun n => f n = p)) (hb : ∃ N, ∀ n, N ≤ n → f n ≤ p) :
    MaxOdd f ↔ p % 2 = 1 := by
  constructor
  · rintro ⟨q,hq,hqinf,M,hM⟩
    obtain ⟨N,hN⟩ := hb
    obtain ⟨n,hn,he⟩ := ho M
    have hpq : p ≤ q := by have hh := hM n hn; omega
    obtain ⟨k,hk,he'⟩ := hqinf N
    have hqp : q ≤ p := by have hh := hN k hk; omega
    have heq : p = q := by omega
    simpa [heq] using hq
  · intro hp; exact ⟨p,hp,ho,hb⟩

def pairRun (A : Parity (Fin alphabet) (Fin na)) (B : Parity (Fin alphabet) (Fin nb))
    (w : Nat → Fin alphabet) (n : Nat) : Vertex na nb := (A.run w n, B.run w n)

def observed (A : Parity (Fin alphabet) (Fin na)) (B : Parity (Fin alphabet) (Fin nb))
    (w : Nat → Fin alphabet) (n : Nat) : Arc na nb alphabet := (pairRun A B w n, w n)

private theorem graph_contains (allow : Arc na nb alphabet → Bool) (e : Arc na nb alphabet)
    (he : allow e = true) : graph A B allow e.1 (target A B e) = true := by
  apply List.any_eq_true.mpr
  exact ⟨e.2, by simp, by simp [he]⟩

private theorem closed_run (allow : Arc na nb alphabet → Bool) (R : Matrix na nb)
    (hR : Closed (graph A B allow) R) (w : Nat → Fin alphabet) (N n : Nat) (hn : N ≤ n)
    (ha : ∀ k, N ≤ k → allow (observed A B w k) = true) :
    R (pairRun A B w N) (pairRun A B w n) = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction d with
  | zero => simpa only [Nat.add_zero] using hR.refl (pairRun A B w N)
  | succ d ih =>
    apply hR.trans _ (pairRun A B w (N+d)) _ ih
    exact hR.edge _ _ (graph_contains allow (observed A B w (N+d)) (ha (N+d) (by omega)))

/-- Accepted checks imply equality on every infinite word over the common
finite alphabet. State cardinalities and transition structures may differ. -/
theorem check_sound (A : Parity (Fin alphabet) (Fin na)) (B : Parity (Fin alphabet) (Fin nb))
    (h : check A B = true) : ∀ w, A.Accepts w ↔ B.Accepts w := by
  intro w
  let R := (closure (graph A B (fun _ => true))).get
  obtain ⟨hR,hchecks⟩ := Bool.and_eq_true_iff.mp h
  have hr : Closed (graph A B (fun _ => true)) R := closedCheck_sound _ _ hR
  have hlmem (n : Nat) : A.priorities w n ∈ leftPriorities (nb := nb) A := by
    apply List.mem_eraseDups.mpr
    exact List.mem_map.mpr ⟨observed A B w n, mem_arcs _, rfl⟩
  have hrmem (n : Nat) : B.priorities w n ∈ rightPriorities (na := na) B := by
    apply List.mem_eraseDups.mpr
    exact List.mem_map.mpr ⟨observed A B w n, mem_arcs _, rfl⟩
  obtain ⟨p,hp,hop,N,hN⟩ := recurrent_max _ _ hlmem
  obtain ⟨q,hq,hoq,M,hM⟩ := recurrent_max _ _ hrmem
  have hpar : p % 2 = q % 2 := by
    apply Classical.byContradiction
    intro hne
    have ht := (List.all_eq_true.mp ((List.all_eq_true.mp hchecks) p hp)) q hq
    simp only [thresholdCheck, hne, ↓reduceIte, Bool.and_eq_true] at ht
    let C := (closure (graph A B (bounded A B p q))).get
    have hc : Closed (graph A B (bounded A B p q)) C := closedCheck_sound _ _ ht.1
    have hab (k : Nat) (hk : max N M ≤ k) : bounded A B p q (observed A B w k) = true := by
      apply decide_eq_true
      exact ⟨hN k (by omega), hM k (by omega)⟩
    obtain ⟨e,he,hoe⟩ := finite_often (arcs na nb alphabet) (observed A B w)
      (fun n => A.priorities w n = p) (fun _ => mem_arcs _) hop
    obtain ⟨f,hf,hof⟩ := finite_often (arcs na nb alphabet) (observed A B w)
      (fun n => B.priorities w n = q) (fun _ => mem_arcs _) hoq
    obtain ⟨i,hi,hei,hpi⟩ := hoe (max N M)
    obtain ⟨j,hj,hfj,hqj⟩ := hof (i+1)
    obtain ⟨k,hk,hek,_⟩ := hoe (j+1)
    have hre : R (A.initial,B.initial) e.1 = true := by
      have hh := closed_run (fun _ => true) R hr w 0 i (by omega) (by intros; rfl)
      simpa only [observed, ← hei, pairRun, Parity.run] using hh
    have hef : C (target A B e) f.1 = true := by
      have hh := closed_run (bounded A B p q) C hc w (i+1) j hj
        (fun t ht => hab t (by omega))
      change C (target A B (observed A B w i)) (observed A B w j).1 = true at hh
      simpa only [hei, hfj] using hh
    have hfe : C (target A B f) e.1 = true := by
      have hh := closed_run (bounded A B p q) C hc w (j+1) k hk
        (fun t ht => hab t (by omega))
      change C (target A B (observed A B w j)) (observed A B w k).1 = true at hh
      simpa only [hfj, hek] using hh
    have hbe : bounded A B p q e = true := hei ▸ hab i hi
    have hbf : bounded A B p q f = true := hfj ▸ hab j (by omega)
    have hpe : leftPriority A e = p := by rw [← hei]; exact hpi
    have hqf : rightPriority B f = q := by rw [← hfj]; exact hqj
    have hbad : badWalk A B R C p q e f = true := by
      simp only [badWalk, hre, hbe, hbf, hpe, hqf, decide_true, hef, hfe, Bool.and_self]
    have hno := (List.all_eq_true.mp ((List.all_eq_true.mp ht.2) e he)) f hf
    rw [hbad] at hno
    contradiction
  exact (maxOdd_recurrent_max _ p hop ⟨N,hN⟩).trans
    ((by rw [hpar] : p % 2 = 1 ↔ q % 2 = 1).trans
      (maxOdd_recurrent_max _ q hoq ⟨M,hM⟩).symm)

/-- Language equality as equality of predicates on infinite words. -/
theorem check_language (A : Parity (Fin alphabet) (Fin na)) (B : Parity (Fin alphabet) (Fin nb))
    (h : check A B = true) : A.Accepts = B.Accepts :=
  funext (fun w => propext (check_sound A B h w))

variable {Letter State : Type}

def Buchi.toParity (A : Buchi Letter State) : Parity Letter State where
  initial := A.initial
  step s a := (A.step s a, if A.accepting s then 1 else 0)

theorem Buchi.toParity_run (A : Buchi Letter State) (w : Nat → Letter) (n : Nat) :
    A.toParity.run w n = A.run w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Parity.run, ih]; rfl

private theorem boolean_maxOdd (m : Nat → Bool) :
    MaxOdd (fun n => if m n then 1 else 0) ↔ Inf m := by
  constructor
  · rintro ⟨p,hp,ho,_⟩ N
    have hp1 : p = 1 := by
      obtain ⟨n,_,he⟩ := ho 0
      cases hm : m n <;> simp [hm] at he <;> omega
    obtain ⟨n,hn,he⟩ := ho N
    refine ⟨n,hn,?_⟩
    cases hm : m n <;> simp_all
  · intro h
    refine ⟨1,rfl,?_,0,?_⟩
    · intro N
      obtain ⟨n,hn,he⟩ := h N
      exact ⟨n,hn,by simp [he]⟩
    · intro n _; cases hm : m n <;> simp [hm]

theorem Buchi.toParity_language (A : Buchi Letter State) (w : Nat → Letter) :
    A.toParity.Accepts w ↔ A.Accepts w := by
  have he : A.toParity.priorities w = fun n => if A.accepting (A.run w n) then 1 else 0 := by
    funext n
    unfold Parity.priorities
    rw [Buchi.toParity_run]
    rfl
  change MaxOdd _ ↔ Inf _
  rw [he]
  exact boolean_maxOdd _

def checkBuchi (A : Buchi (Fin alphabet) (Fin na)) (B : Buchi (Fin alphabet) (Fin nb)) : Bool :=
  check A.toParity B.toParity

theorem checkBuchi_sound (A : Buchi (Fin alphabet) (Fin na)) (B : Buchi (Fin alphabet) (Fin nb))
    (h : checkBuchi A B = true) : A.Accepts = B.Accepts := by
  funext w
  apply propext
  exact (A.toParity_language w).symm.trans ((check_sound _ _ h w).trans (B.toParity_language w))

end Tlsf.Dpa.Validation
