/-
Status: WRITTEN, NOT COMPILED in the accompanying run.
These are ordinary replay examples, not an implemented tactic or verified parser.
-/
import Mathlib
set_option autoImplicit false

namespace ForgeExtensions

/-- The scaled graph relation, a non-conserved invariant. -/
theorem scaled_graph_step (x y z : ℚ) (h : z - x*y = 0) :
    6*z - (2*x)*(3*y) = 0 := by
  calc
    6*z - (2*x)*(3*y) = 6*(z-x*y) := by ring
    _ = 0 := by rw [h]; ring

/-- Two mutually preserved components need not be individually conserved. -/
theorem mutual_family_step (x y : ℚ) (hx : x = 0) (hy : y = 0) :
    y = 0 ∧ 2*x = 0 := by
  constructor
  · exact hy
  · rw [hx]; ring

/-- An ordinary finite telescoping combinator. -/
theorem telescope_range (t G : ℕ → ℚ)
    (hstep : ∀ k, G (k+1) - G k = t k) (N : ℕ) :
    (∑ k ∈ Finset.range N, t k) = G N - G 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, ← hstep n]
      ring

/-- Polynomial part of the factorial-weight antidifference certificate. -/
theorem factorial_weight_identity (k : ℚ) :
    (k+1)^2 * 1 * k - k * 1 * (k+1) = k*k*(k+1) := by
  ring

/-- Singular boundary k=n of the binomial-square flux identity. -/
theorem binomial_boundary_n (n : ℚ) :
    (n+1)^3 - 2*(2*n+1) = n^2*(n+3) - (n+1) := by
  ring

end ForgeExtensions
#print axioms ForgeExtensions.scaled_graph_step
#print axioms ForgeExtensions.mutual_family_step
#print axioms ForgeExtensions.telescope_range
#print axioms ForgeExtensions.factorial_weight_identity
#print axioms ForgeExtensions.binomial_boundary_n
