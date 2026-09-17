/-
  Sparse multivariate polynomials over `Int`, with evaluation proved to be a
  ring homomorphism. This is the substrate the certificate checkers are built
  on.

  CORE LEAN ONLY. No Mathlib import, deliberately: every Mathlib-importing file
  in this repository is unchecked, and the point of this development is to be
  checked. Coefficients are integers rather than rationals for the same reason
  --- `Int` is in core and `Rat` arithmetic lemmas largely are not --- and the
  producer clears denominators before emitting a certificate.

  Polynomials are UNNORMALISED term lists. Nothing here maintains a canonical
  form, because none of the algebraic lemmas need one; only the zero TEST needs
  to collect like terms, and `collect` does that where it is needed.
-/
namespace Forge.Checker

/-- An exponent vector. Position `i` holds the exponent of variable `i`.
Trailing zeros may be omitted, so `[2]` and `[2,0]` denote the same monomial. -/
abbrev Mono := List Nat

/-- A polynomial: a formal sum of `(monomial, coefficient)` terms.
Repeated monomials are permitted and mean what they say --- their
contributions add. -/
abbrev Poly := List (Mono × Int)

/-- An assignment of an integer to every variable. Total, which avoids every
length-mismatch case that a list-valued environment would introduce. -/
abbrev Env := Nat → Int

/-- Evaluate a monomial whose head is the exponent of variable `i`. -/
def monoEvalFrom (x : Env) : Nat → Mono → Int
  | _, [] => 1
  | i, e :: es => x i ^ e * monoEvalFrom x (i + 1) es

/-- Evaluate a monomial, starting at variable `0`. -/
def monoEval (x : Env) (m : Mono) : Int := monoEvalFrom x 0 m

/-- Evaluate a polynomial. -/
def eval (x : Env) : Poly → Int
  | [] => 0
  | (m, c) :: p => c * monoEval x m + eval x p

/-- Multiply monomials by adding exponents pointwise. The shorter vector is
padded with the implicit trailing zeros. -/
def addMono : Mono → Mono → Mono
  | [], m => m
  | m, [] => m
  | a :: as, b :: bs => (a + b) :: addMono as bs

/-! ### Arithmetic -/

def add (p q : Poly) : Poly := p ++ q

def neg (p : Poly) : Poly := p.map (fun t => (t.1, -t.2))

def sub (p q : Poly) : Poly := p ++ neg q

def smul (c : Int) (p : Poly) : Poly := p.map (fun t => (t.1, c * t.2))

/-- One term times a polynomial. -/
def mulTerm (m : Mono) (c : Int) (q : Poly) : Poly :=
  q.map (fun s => (addMono m s.1, c * s.2))

def mul : Poly → Poly → Poly
  | [], _ => []
  | (m, c) :: p, q => mulTerm m c q ++ mul p q

/-! ### Collecting like terms

The only place a canonical form is needed. `isZero` is the decision procedure
the checkers call: a polynomial is identically zero exactly when its collected
coefficients all vanish. -/

/-- Add `c * m` into a polynomial, merging with an existing `m` if present. -/
def insertTerm (m : Mono) (c : Int) : Poly → Poly
  | [] => [(m, c)]
  | (m', c') :: p => if m = m' then (m', c + c') :: p else (m', c') :: insertTerm m c p

/-- Drop trailing zero exponents, so `[2]` and `[2, 0]` become the same list.

Without this `collect` compared monomials by list equality, and
`isZero [([2], 1), ([2, 0], -1)]` returned `false` for a polynomial that is
identically zero. That never affected soundness -- a `false` only rejects -- but
it was a real completeness defect, invisible while every producer emitted
fixed-width vectors, and the first thing a reification tactic would have hit. -/
def trimMono : Mono → Mono
  | [] => []
  | e :: es =>
    match trimMono es with
    | [] => if e = 0 then [] else [e]
    | t => e :: t

/-- Collect like terms, identifying monomials up to trailing zeros. -/
def collect : Poly → Poly
  | [] => []
  | (m, c) :: p => insertTerm (trimMono m) c (collect p)

/-- Decide whether a polynomial is identically zero. -/
def isZero (p : Poly) : Bool := (collect p).all (fun t => t.2 == 0)

/-! ### Evaluation is a homomorphism

Everything below is the proof obligation this file exists to discharge. -/

/-- A stand-in for Mathlib's `ring`, built from core `Int` lemmas.

Associativity and commutativity are given to `simp only` together, which
normalises both operations by its own term ordering; the distributive and
negation lemmas put the goal into a sum-of-products shape first. This is not a
decision procedure and it is not `ring`. It closes the goals in this file, and
when it fails the proof says so by failing to compile. -/
macro "int_ring" : tactic =>
  `(tactic| simp only [Int.mul_add, Int.add_mul, Int.mul_neg, Int.neg_mul,
                       Int.sub_eq_add_neg, Int.neg_add, Int.mul_assoc,
                       Int.add_assoc, Int.mul_comm, Int.mul_left_comm,
                       Int.add_comm, Int.add_left_comm])

theorem monoEvalFrom_addMono (x : Env) :
    ∀ (i : Nat) (m m' : Mono),
      monoEvalFrom x i (addMono m m') = monoEvalFrom x i m * monoEvalFrom x i m'
  | _, [], m' => by simp [addMono, monoEvalFrom]
  | _, a :: as, [] => by simp [addMono, monoEvalFrom]
  | i, a :: as, b :: bs => by
    show monoEvalFrom x i ((a + b) :: addMono as bs) = _
    simp only [monoEvalFrom, monoEvalFrom_addMono x (i + 1) as bs, Int.pow_add]
    int_ring

theorem monoEval_addMono (x : Env) (m m' : Mono) :
    monoEval x (addMono m m') = monoEval x m * monoEval x m' :=
  monoEvalFrom_addMono x 0 m m'

theorem eval_append (x : Env) : ∀ p q : Poly, eval x (p ++ q) = eval x p + eval x q
  | [], q => by simp [eval]
  | (m, c) :: p, q => by
    show eval x ((m, c) :: (p ++ q)) = _
    simp only [eval, eval_append x p q]
    int_ring

theorem eval_add (x : Env) (p q : Poly) : eval x (add p q) = eval x p + eval x q :=
  eval_append x p q

theorem eval_neg (x : Env) : ∀ p : Poly, eval x (neg p) = -eval x p
  | [] => by simp [neg, eval]
  | (m, c) :: p => by
    show eval x ((m, -c) :: neg p) = _
    simp only [eval, eval_neg x p]
    int_ring

theorem eval_sub (x : Env) (p q : Poly) : eval x (sub p q) = eval x p - eval x q := by
  simp only [sub, eval_append, eval_neg]
  int_ring

theorem eval_smul (x : Env) (c : Int) : ∀ p : Poly, eval x (smul c p) = c * eval x p
  | [] => by simp [smul, eval]
  | (m, d) :: p => by
    show eval x ((m, c * d) :: smul c p) = _
    simp only [eval, eval_smul x c p]
    int_ring

theorem eval_mulTerm (x : Env) (m : Mono) (c : Int) :
    ∀ q : Poly, eval x (mulTerm m c q) = c * monoEval x m * eval x q
  | [] => by simp [mulTerm, eval]
  | (m', c') :: q => by
    show eval x ((addMono m m', c * c') :: mulTerm m c q) = _
    simp only [eval, eval_mulTerm x m c q, monoEval_addMono]
    int_ring

theorem eval_mul (x : Env) : ∀ p q : Poly, eval x (mul p q) = eval x p * eval x q
  | [], q => by simp [mul, eval]
  | (m, c) :: p, q => by
    show eval x (mulTerm m c q ++ mul p q) = _
    simp only [eval_append, eval_mulTerm, eval_mul x p q, eval]
    int_ring

theorem eval_insertTerm (x : Env) (m : Mono) (c : Int) :
    ∀ p : Poly, eval x (insertTerm m c p) = c * monoEval x m + eval x p
  | [] => by simp [insertTerm, eval]
  | (m', c') :: p => by
    simp only [insertTerm]
    split
    · next h =>
        subst h
        simp only [eval]
        int_ring
    · next h =>
        simp only [eval, eval_insertTerm x m c p]
        int_ring

theorem monoEvalFrom_trimMono (x : Env) :
    ∀ (i : Nat) (m : Mono), monoEvalFrom x i (trimMono m) = monoEvalFrom x i m
  | _, [] => rfl
  | i, e :: es => by
    have ih := monoEvalFrom_trimMono x (i + 1) es
    simp only [trimMono]
    split
    · next h =>
        rw [h] at ih
        simp only [monoEvalFrom] at ih
        split
        · next he => simp [monoEvalFrom, he, ← ih]
        · simp [monoEvalFrom, ← ih]
    · next t ht =>
        simp only [monoEvalFrom]
        rw [← ih]

theorem monoEval_trimMono (x : Env) (m : Mono) :
    monoEval x (trimMono m) = monoEval x m :=
  monoEvalFrom_trimMono x 0 m

theorem eval_collect (x : Env) : ∀ p : Poly, eval x (collect p) = eval x p
  | [] => by simp [collect]
  | (m, c) :: p => by
    simp only [collect, eval_insertTerm, eval_collect x p, eval, monoEval_trimMono]

theorem eval_eq_zero_of_coeffs (x : Env) :
    ∀ p : Poly, (∀ t ∈ p, t.2 = 0) → eval x p = 0
  | [], _ => by simp [eval]
  | (m, c) :: p, h => by
    have hc : c = 0 := h (m, c) (by simp)
    have hp : eval x p = 0 :=
      eval_eq_zero_of_coeffs x p (fun t ht => h t (by simp [ht]))
    simp [eval, hc, hp]

/-- **The lemma the checkers rest on.** If `isZero p` says yes, then `p`
evaluates to zero at every assignment --- not merely at the ones anyone tried. -/
theorem eval_eq_zero_of_isZero (x : Env) (p : Poly) (h : isZero p = true) :
    eval x p = 0 := by
  have hall : ∀ t ∈ collect p, t.2 = 0 := by
    intro t ht
    have := List.all_eq_true.mp h t ht
    exact of_decide_eq_true (by simpa using this)
  have := eval_eq_zero_of_coeffs x (collect p) hall
  rwa [eval_collect] at this

/-- Two polynomials agree at every assignment when their difference collects to
zero. This is the form the certificate checkers use: they verify an identity,
and identity of polynomials is stronger than agreement at any finite set of
points. -/
theorem eval_eq_of_sub_isZero (x : Env) (p q : Poly) (h : isZero (sub p q) = true) :
    eval x p = eval x q := by
  have := eval_eq_zero_of_isZero x (sub p q) h
  rw [eval_sub] at this
  omega

end Forge.Checker
