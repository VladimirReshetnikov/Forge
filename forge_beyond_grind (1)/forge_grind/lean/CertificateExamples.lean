/-
Reference proof scripts illustrating certificate replay with Mathlib.
NOT compiled here. Use a compatible, pinned Mathlib workspace.
These are explicit mathematical proofs, not an implemented `forge` tactic.
-/
import Mathlib

namespace ForgeExamples

theorem quartic_nonnegative (x y z : ℝ) :
    0 ≤ x^4 + y^4 + z^4 - x^2*y^2 - y^2*z^2 - z^2*x^2 := by
  have hxy := sq_nonneg (x^2 - y^2)
  have hyz := sq_nonneg (y^2 - z^2)
  have hzx := sq_nonneg (z^2 - x^2)
  nlinarith only [hxy, hyz, hzx]

theorem polynomial_majorant (x : ℝ) : ∃ y : ℝ, x ≤ y ∧ -x ≤ y := by
  refine ⟨x^2 + 1, ?_, ?_⟩
  · have h := sq_nonneg (x - (1 / 2 : ℝ))
    nlinarith only [h]
  · have h := sq_nonneg (x + (1 / 2 : ℝ))
    nlinarith only [h]

theorem interval_positive (x : ℝ) : 0 < x^2 - x + (3 / 10 : ℝ) := by
  have h := sq_nonneg (x - (1 / 2 : ℝ))
  nlinarith only [h]

-- The preceding theorem is globally true. The Python box experiment proves
-- its restriction to [0,1], deliberately exercising a different checker.

#print axioms quartic_nonnegative
#print axioms polynomial_majorant

end ForgeExamples
