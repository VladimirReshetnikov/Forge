/-
Status: NOT_RUN. This authoring environment had no Lean executable.
These are proof-reconstruction targets, not an implemented reifier or tactic.
They introduce no axioms and contain no sorry/admit placeholders.
Compile in a compatible, already built Mathlib project; do not infer acceptance
from the existence of this file. See tools/check_lean.py.
-/
import Mathlib

namespace ForgeNC

/-- The single local proof rule behind two-sided ideal receipts. -/
theorem sandwich_zero {R : Type*} [Ring R]
    (u r v : R) (hr : r = 0) : u * r * v = 0 := by
  simp [hr]

/-- A finite equality certificate only needs a checked identity and zero terms. -/
theorem sum_certificate_sound {R : Type*} [Ring R] {I : Type*}
    (s : Finset I) (p : R) (term : I -> R)
    (hidentity : p = s.sum term)
    (hzero : forall i, i ∈ s -> term i = 0) : p = 0 := by
  exact hidentity.trans (Finset.sum_eq_zero hzero)

/-- A small replay does not need a noncommutative Groebner-basis theorem. -/
theorem commuted_square {R : Type*} [Semiring R]
    (x y : R) (h : x * y = y * x) : (x * x) * y = y * (x * x) := by
  calc
    (x * x) * y = x * (x * y) := mul_assoc x x y
    _ = x * (y * x) := congrArg (fun t => x * t) h
    _ = (x * y) * x := (mul_assoc x y x).symm
    _ = (y * x) * x := congrArg (fun t => t * x) h
    _ = y * (x * x) := mul_assoc y x x

theorem resolvent_identity {R : Type*} [Ring R]
    (U A B V : R) (hUA : U * A = 1) (hBV : B * V = 1) :
    U - V = U * (B - A) * V := by
  have h1 : U * (B * V) = U := by rw [hBV, mul_one]
  have h2 : (U * A) * V = V := by rw [hUA, one_mul]
  calc
    U - V = U * (B * V) - (U * A) * V := by rw [h1, h2]
    _ = U * (B - A) * V := by noncomm_ring

theorem push_through {R : Type*} [Ring R]
    (U A B V : R) (hU : U * (1 - A * B) = 1)
    (hV : (1 - B * A) * V = 1) : U * A = A * V := by
  apply sub_eq_zero.mp
  calc
    U * A - A * V =
        (U * (1 - A * B) - 1) * A * V -
        U * A * ((1 - B * A) * V - 1) := by noncomm_ring
    _ = 0 := by rw [hU, hV]; simp

/-- The already-library-proved positivity rule needed by an operator receipt. -/
theorem positive_congruence {n : Type*} [Fintype n] [DecidableEq n]
    (G Q : Matrix n n Real) (hG : G.PosSemidef) :
    (Q.conjTranspose * G * Q).PosSemidef := by
  exact hG.conjTranspose_mul_mul_same Q

end ForgeNC

#print axioms ForgeNC.sandwich_zero
#print axioms ForgeNC.sum_certificate_sound
#print axioms ForgeNC.commuted_square
#print axioms ForgeNC.resolvent_identity
#print axioms ForgeNC.push_through
#print axioms ForgeNC.positive_congruence
