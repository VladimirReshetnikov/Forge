import Forge.Checker.Poly
/-
  A checked certificate checker for nonnegativity over a basic semialgebraic
  set: sums of squares, products of the inequality constraints, and equality
  multipliers.

  THE CLAIM. Given a polynomial `p`, inequality constraints `ineqs`, equality
  constraints `eqs`, and a certificate, `Cert.check` returns a `Bool`.
  `Cert.sound` proves that when it returns `true`, `p` is nonnegative at every
  assignment where the `ineqs` are nonnegative and the `eqs` vanish.

  The checker performs no search. The theorem quantifies over every assignment,
  not over any tested set, and says nothing about where the certificate came
  from: found by search, written by hand, or produced adversarially, it faces
  the same check and the conclusion follows from the check alone.

  WHAT IS CERTIFIED. The polynomial identity

      D * p  =  sum_i w_i * (prod_k g_k ^ e_ik) * q_i^2  +  sum_j h_j * f_j

  with `D > 0` and every `w_i >= 0`, where `g_k` are the inequality constraints
  and `f_j` the equality constraints. At a point of the feasible set every
  `g_k >= 0`, so each product of their powers is nonnegative, each square is
  nonnegative, and the equality terms vanish -- leaving `D * p >= 0`, hence
  `p >= 0`.

  This shape covers all three certificate families the prototype emits: plain
  sums of squares (no powers, no multipliers), equality-constrained cones, and
  guard products where `e_ik` is nonzero.

  CORE LEAN ONLY, deliberately. Every Mathlib-importing file in this repository
  is unchecked; the point of this development is to be checked. Coefficients are
  integers because `Int` is in core: the producer clears denominators, which is
  a change of representation and not a weakening of the method.

  SCOPE. `Env` assigns integers to variables, so what is proved here is
  nonnegativity at integer points. The IDENTITY the checker verifies holds in
  every commutative ring; lifting the conclusion to the reals needs an ordered
  field and therefore Mathlib, and is stated separately in `Real.lean`.
-/
namespace Forge.Checker

/-- The constant polynomial `1`. -/
def one : Poly := [([], 1)]

@[simp] theorem eval_one (x : Env) : eval x one = 1 := by
  simp [one, eval, monoEval, monoEvalFrom]

/-- Repeated multiplication. -/
def polyPow (q : Poly) : Nat → Poly
  | 0 => one
  | n + 1 => mul q (polyPow q n)

theorem eval_polyPow (x : Env) (q : Poly) : ∀ n, eval x (polyPow q n) = (eval x q) ^ n
  | 0 => by simp [polyPow, Int.pow_zero]
  | n + 1 => by
    show eval x (mul q (polyPow q n)) = _
    rw [eval_mul, eval_polyPow x q n, Int.pow_succ, Int.mul_comm]

/-- `prod_k g_k ^ e_k`, stopping at the shorter list. The checker separately
requires the exponent list to match the constraint list, so nothing is
silently dropped. -/
def powerProduct : List Nat → List Poly → Poly
  | [], _ => one
  | _ :: _, [] => one
  | e :: es, g :: gs => mul (polyPow g e) (powerProduct es gs)

theorem eval_powerProduct_nonneg (x : Env) :
    ∀ (es : List Nat) (gs : List Poly), (∀ g ∈ gs, 0 ≤ eval x g) →
      0 ≤ eval x (powerProduct es gs)
  | [], _, _ => by simp [powerProduct]
  | _ :: _, [], _ => by simp [powerProduct]
  | e :: es, g :: gs, h => by
    have hg : 0 ≤ eval x g := h g (by simp)
    have hrest : 0 ≤ eval x (powerProduct es gs) :=
      eval_powerProduct_nonneg x es gs (fun g' hg' => h g' (by simp [hg']))
    show 0 ≤ eval x (mul (polyPow g e) (powerProduct es gs))
    rw [eval_mul, eval_polyPow]
    exact Int.mul_nonneg (Int.pow_nonneg hg) hrest

/-- One cone term: `w * (prod_k g_k ^ e_k) * q^2`. -/
def coneTerm (w : Int) (es : List Nat) (q : Poly) (ineqs : List Poly) : Poly :=
  smul w (mul (powerProduct es ineqs) (mul q q))

/-- A weighted square with the exponents of the inequality constraints it is
multiplied by. -/
structure Square where
  weight : Int
  powers : List Nat
  poly : Poly
  deriving Repr

def sumCone : List Square → List Poly → Poly
  | [], _ => []
  | s :: ts, ineqs => add (coneTerm s.weight s.powers s.poly ineqs) (sumCone ts ineqs)

/-- `sum_j h_j * f_j`. -/
def dot : List Poly → List Poly → Poly
  | [], _ => []
  | _ :: _, [] => []
  | h :: hs, f :: fs => add (mul h f) (dot hs fs)

/-- A cone certificate. -/
structure Cert where
  /-- The positive integer the producer multiplied the identity through by. -/
  scale : Int
  /-- Weighted squares, each with its inequality exponents. -/
  squares : List Square
  /-- One multiplier per equality constraint, in the same order. -/
  multipliers : List Poly
  deriving Repr

/-- The checker. Total, search-free, and decidable by kernel reduction. -/
def Cert.check (c : Cert) (p : Poly) (ineqs eqs : List Poly) : Bool :=
  (0 < c.scale) &&
  c.squares.all (fun s => 0 ≤ s.weight) &&
  c.squares.all (fun s => s.powers.length == ineqs.length) &&
  (c.multipliers.length == eqs.length) &&
  isZero (sub (smul c.scale p)
              (add (sumCone c.squares ineqs) (dot c.multipliers eqs)))

/-! ### Soundness -/

private theorem int_mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ (-a) * (-a) := Int.mul_nonneg (by omega) (by omega)
    rwa [Int.neg_mul_neg] at hn

theorem eval_sumCone_nonneg (x : Env) (ineqs : List Poly)
    (hg : ∀ g ∈ ineqs, 0 ≤ eval x g) :
    ∀ ts : List Square, (∀ s ∈ ts, 0 ≤ s.weight) → 0 ≤ eval x (sumCone ts ineqs)
  | [], _ => by simp [sumCone, eval]
  | s :: ts, h => by
    have hw : 0 ≤ s.weight := h s (by simp)
    have hrest : 0 ≤ eval x (sumCone ts ineqs) :=
      eval_sumCone_nonneg x ineqs hg ts (fun s' hs' => h s' (by simp [hs']))
    have hterm : 0 ≤ eval x (coneTerm s.weight s.powers s.poly ineqs) := by
      show 0 ≤ eval x (smul s.weight (mul (powerProduct s.powers ineqs) (mul s.poly s.poly)))
      rw [eval_smul, eval_mul, eval_mul]
      exact Int.mul_nonneg hw
        (Int.mul_nonneg (eval_powerProduct_nonneg x s.powers ineqs hg)
          (int_mul_self_nonneg _))
    show 0 ≤ eval x (add (coneTerm s.weight s.powers s.poly ineqs) (sumCone ts ineqs))
    rw [eval_add]
    exact Int.add_nonneg hterm hrest

theorem eval_dot_eq_zero (x : Env) :
    ∀ (hs fs : List Poly), (∀ f ∈ fs, eval x f = 0) → eval x (dot hs fs) = 0
  | [], _, _ => by simp [dot, eval]
  | _ :: _, [], _ => by simp [dot, eval]
  | h :: hs, f :: fs, hz => by
    have hf : eval x f = 0 := hz f (by simp)
    have hrest : eval x (dot hs fs) = 0 :=
      eval_dot_eq_zero x hs fs (fun f' hf' => hz f' (by simp [hf']))
    show eval x (add (mul h f) (dot hs fs)) = 0
    rw [eval_add, eval_mul, hf, hrest]
    simp

/-- **Soundness.** If the checker accepts, `p` is nonnegative everywhere on the
set cut out by the constraints. -/
theorem Cert.sound (c : Cert) (p : Poly) (ineqs eqs : List Poly)
    (hcheck : c.check p ineqs eqs = true) (x : Env)
    (hge : ∀ g ∈ ineqs, 0 ≤ eval x g)
    (hz : ∀ f ∈ eqs, eval x f = 0) : 0 ≤ eval x p := by
  simp only [Cert.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
  obtain ⟨⟨⟨⟨hpos, hw⟩, _⟩, _⟩, hid⟩ := hcheck
  have hEq : eval x (smul c.scale p)
      = eval x (add (sumCone c.squares ineqs) (dot c.multipliers eqs)) :=
    eval_eq_of_sub_isZero x _ _ hid
  rw [eval_smul, eval_add, eval_dot_eq_zero x _ _ hz] at hEq
  have hnn : 0 ≤ eval x (sumCone c.squares ineqs) :=
    eval_sumCone_nonneg x ineqs hge c.squares (fun s hs => by
      have := List.all_eq_true.mp hw s hs
      exact of_decide_eq_true this)
  have hscaled : 0 ≤ c.scale * eval x p := by omega
  by_cases hp : 0 ≤ eval x p
  · exact hp
  · exact absurd hscaled (Int.not_le.mpr
      (Int.mul_neg_of_pos_of_neg hpos (Int.not_le.mp hp)))

end Forge.Checker
