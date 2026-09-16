/- GENERATED / NOT COMPILED. See lean/STATUS.md. -/
import LadderBridge

namespace ForgeAnalytic.Generated.ghost_eps_1
private noncomputable def q0 (x : ℝ) : ℝ := (((5 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((-4 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((1 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x))
private noncomputable def q1 (x : ℝ) : ℝ := (((20 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((-20 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((6 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x))
private noncomputable def q2 (x : ℝ) : ℝ := (((80 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((-100 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((36 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x))
private noncomputable def q3 (x : ℝ) : ℝ := (((320 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((-500 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((216 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x))
private noncomputable def q4 (x : ℝ) : ℝ := (((1280 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((-2500 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((1296 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x))
private noncomputable def q5 (x : ℝ) : ℝ := (((-2500 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((2592 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x))
private noncomputable def q6 (x : ℝ) : ℝ := (((2592 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x))
private noncomputable def q7 (x : ℝ) : ℝ := (0 : ℝ)

private theorem h7 (x : ℝ) (_hx : 0 ≤ x) : 0 ≤ q7 x := by
  simp [q7]

private theorem h6 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q6 x := by
  apply ladder_step (f := q6) (g := q7) (a := 0) (rho := ((2 : ℝ) / 1))
  · intro x
    convert (((((hasDerivAt_id x).pow 0).const_mul ((2592 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((2 : ℝ) / 1)).exp))) using 1 <;>
      dsimp [q6, q7] <;> norm_num <;> ring
  · norm_num [q6]
  · exact h7
  · exact hx

private theorem h5 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q5 x := by
  apply ladder_step (f := q5) (g := q6) (a := 0) (rho := ((1 : ℝ) / 1))
  · intro x
    convert ((((((hasDerivAt_id x).pow 0).const_mul ((-2500 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 0).const_mul ((2592 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((2 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q5, q6] <;> norm_num <;> ring
  · norm_num [q5]
  · exact h6
  · exact hx

private theorem h4 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q4 x := by
  apply ladder_step (f := q4) (g := q5) (a := 0) (rho := ((0 : ℝ) / 1))
  · intro x
    convert (((((((hasDerivAt_id x).pow 0).const_mul ((1280 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 0).const_mul ((-2500 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 0).const_mul ((1296 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((2 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q4, q5] <;> norm_num <;> ring
  · norm_num [q4]
  · exact h5
  · exact hx

private theorem h3 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q3 x := by
  apply ladder_step (f := q3) (g := q4) (a := 0) (rho := ((-4 : ℝ) / 1))
  · intro x
    convert (((((((hasDerivAt_id x).pow 0).const_mul ((320 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 0).const_mul ((-500 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 0).const_mul ((216 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((2 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q3, q4] <;> norm_num <;> ring
  · norm_num [q3]
  · exact h4
  · exact hx

private theorem h2 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q2 x := by
  apply ladder_step (f := q2) (g := q3) (a := 0) (rho := ((-4 : ℝ) / 1))
  · intro x
    convert (((((((hasDerivAt_id x).pow 0).const_mul ((80 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 0).const_mul ((-100 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 0).const_mul ((36 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((2 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q2, q3] <;> norm_num <;> ring
  · norm_num [q2]
  · exact h3
  · exact hx

private theorem h1 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q1 x := by
  apply ladder_step (f := q1) (g := q2) (a := 0) (rho := ((-4 : ℝ) / 1))
  · intro x
    convert (((((((hasDerivAt_id x).pow 0).const_mul ((20 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 0).const_mul ((-20 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 0).const_mul ((6 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((2 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q1, q2] <;> norm_num <;> ring
  · norm_num [q1]
  · exact h2
  · exact hx

private theorem h0 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q0 x := by
  apply ladder_step (f := q0) (g := q1) (a := 0) (rho := ((-4 : ℝ) / 1))
  · intro x
    convert (((((((hasDerivAt_id x).pow 0).const_mul ((5 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((0 : ℝ) / 1)).exp)))).add ((((((hasDerivAt_id x).pow 0).const_mul ((-4 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((1 : ℝ) / 1)).exp))))).add ((((((hasDerivAt_id x).pow 0).const_mul ((1 : ℝ) / 1)).mul (((hasDerivAt_id x).const_mul ((2 : ℝ) / 1)).exp)))) using 1 <;>
      dsimp [q0, q1] <;> norm_num <;> ring
  · norm_num [q0]
  · exact h1
  · exact hx

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (((5 : ℝ) / 1) * x ^ 0 * Real.exp (((0 : ℝ) / 1) * x)) + (((-4 : ℝ) / 1) * x ^ 0 * Real.exp (((1 : ℝ) / 1) * x)) + (((1 : ℝ) / 1) * x ^ 0 * Real.exp (((2 : ℝ) / 1) * x)) := h0 x hx

#print axioms nonnegative
end ForgeAnalytic.Generated.ghost_eps_1
