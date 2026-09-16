/- GENERATED / NOT COMPILED. See lean/STATUS.md. -/
import LadderBridge

namespace ForgeAnalytic.Generated.log_lower_rational_chart
private noncomputable def q0 (x : ℝ) : ℝ := (((2 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((1 : ℝ) / 1) * x ^ 1 * Real.exp (((0 : ℝ) / 1) * x)) + (((-2 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((1 : ℝ) / 1) * x ^ 1 * Real.exp (((1 : ℝ) / 1) * x))
private noncomputable def q1 (x : ℝ) : ℝ := (((1 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((-1 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((1 : ℝ) / 1) * x ^ 1 * Real.exp (((1 : ℝ) / 1) * x))
private noncomputable def q2 (x : ℝ) : ℝ := (((1 : ℝ) / 1) * x ^ 1 * Real.exp (((1 : ℝ) / 1) * x))
private noncomputable def q3 (x : ℝ) : ℝ := (((1 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x))
private noncomputable def q4 (x : ℝ) : ℝ := (0 : ℝ)

private theorem h4 (x : ℝ) (_hx : 0 ≤ x) : 0 ≤ q4 x := by
  simp [q4]

private theorem h3 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q3 x := by
  apply ladder_step (f := q3) (g := q4) (a := 0) (rho := ((1 : ℝ) / 1))
  · intro x
    convert (((((hasDerivAt_id x).pow 0).const_mul ((1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))) using 1 <;>
      dsimp [q3, q4] <;> norm_num <;> ring
  · norm_num [q3]
  · exact h4
  · exact hx

private theorem h2 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q2 x := by
  apply ladder_step (f := q2) (g := q3) (a := 0) (rho := ((1 : ℝ) / 1))
  · intro x
    convert (((((hasDerivAt_id x).pow 1).const_mul ((1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))) using 1 <;>
      dsimp [q2, q3] <;> norm_num <;> ring
  · norm_num [q2]
  · exact h3
  · exact hx

private theorem h1 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q1 x := by
  apply ladder_step (f := q1) (g := q2) (a := 0) (rho := ((0 : ℝ) / 1))
  · intro x
    convert (((((((hasDerivAt_id x).pow 0).const_mul ((1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 0).const_mul ((-1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 1).const_mul ((1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q1, q2] <;> norm_num <;> ring
  · norm_num [q1]
  · exact h2
  · exact hx

private theorem h0 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q0 x := by
  apply ladder_step (f := q0) (g := q1) (a := 0) (rho := ((0 : ℝ) / 1))
  · intro x
    convert ((((((((hasDerivAt_id x).pow 0).const_mul ((2 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 1).const_mul ((1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 0).const_mul ((-2 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 1).const_mul ((1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q0, q1] <;> norm_num <;> ring
  · norm_num [q0]
  · exact h1
  · exact hx

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (((2 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((1 : ℝ) / 1) * x ^ 1 * Real.exp (((0 : ℝ) / 1) * x)) + (((-2 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((1 : ℝ) / 1) * x ^ 1 * Real.exp (((1 : ℝ) / 1) * x)) := h0 x hx

#print axioms nonnegative
end ForgeAnalytic.Generated.log_lower_rational_chart
