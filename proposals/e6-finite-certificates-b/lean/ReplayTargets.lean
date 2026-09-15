/-
  NOT_RUN. These are concrete Mathlib replay targets, not compiled evidence.
  The finite identities are independently checked by the Python artifacts.
  A complete Lean worker still needs source bridges and certificate elaboration.
-/
import Mathlib

namespace ForgeExtensions

theorem nonlinearCurveIdentity (x y : ℚ) :
    (x ^ 2) ^ 2 - y ^ 2 = (x ^ 2 + y) * (x ^ 2 - y) := by
  ring

theorem nonlinearCurveStep (x y : ℚ) (h : x ^ 2 - y = 0) :
    (x ^ 2) ^ 2 - y ^ 2 = 0 := by
  rw [nonlinearCurveIdentity, h, mul_zero]

theorem binomialFirstIdentity (n k : ℚ) :
    (-2) * (n + 1 - k) + (n + 1) =
      (n + 1 - k) * (-1) - k * (-1) := by
  ring

theorem binomialSquareIdentity (n k : ℚ) :
    (-2 * (2*n + 1)) * (n + 1 - k)^2 + (n + 1) * (n + 1)^2 =
      (n + 1 - k)^2 * (2*(k+1) - 3*n - 3) - k^2 * (2*k - 3*n - 3) := by
  ring

def franelU (n k : ℚ) : ℚ :=
  (n + 1)^2 * (4*k^3 - 18*k^2*n - 30*k^2 + 27*k*n^2 + 93*k*n + 78*k
    - 14*n^3 - 74*n^2 - 128*n - 72)

theorem franelInteriorIdentity (n k : ℚ) :
    (-8*(n+1)^2) * (n+1-k)^3 * (n+2-k)^3 +
    (-7*n^2-21*n-16) * (n+1)^3 * (n+2-k)^3 +
    (n+2)^2 * (n+1)^3 * (n+2)^3 =
    (n+2-k)^3 * franelU n (k+1) - k^3 * franelU n k := by
  unfold franelU
  ring

#print axioms nonlinearCurveIdentity
#print axioms nonlinearCurveStep
#print axioms binomialFirstIdentity
#print axioms binomialSquareIdentity
#print axioms franelInteriorIdentity
end ForgeExtensions
