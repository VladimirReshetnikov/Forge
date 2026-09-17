import Forge.Real.Cone
import Forge.Checker.Corpus
/-
  The prototype's three cone certificates, restated over the REALS.

  Nothing is re-certified. Each theorem reuses the corpus's existing
  `_checks` theorem -- the same Boolean check, proved once by `decide` -- and
  applies `Cert.sound_real` instead of `Cert.sound`. The integer versions in
  `Forge/Checker/Corpus.lean` say "at every integer point"; these say "at every
  real point", which is the statement the prototype's search was actually about.

  `equality_constrained_real` is the one where the difference is visible: over
  the integers, `x + y = 1` leaves only points where the bound is slack, while
  over the reals the minimum `1` is attained at `x = y = 1/2`.
-/
namespace Forge.Checker.Real.Examples

open Forge.Checker Forge.Checker.Real

theorem hidden_quadratic_real (x0 x1 : ℝ) :
    0 ≤ 147 + (-168) * x1 + 99 * x1 ^ 2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0 ^ 2 := by
  have h := Cert.sound_real hidden_quadratic_cert hidden_quadratic_target
    hidden_quadratic_ineqs hidden_quadratic_eqs hidden_quadratic_checks
    (fun i => if i = 0 then x0 else x1) (by simp [hidden_quadratic_ineqs])
    (by simp [hidden_quadratic_eqs])
  simp [evalR, monoEvalR, monoEvalFromR, hidden_quadratic_target] at h
  linarith

theorem guard_product_real (x0 x1 : ℝ) (h0 : 0 ≤ x0) (h1 : 0 ≤ x1) : 0 ≤ x0 * x1 := by
  have h := Cert.sound_real guard_product_cert guard_product_target
    guard_product_ineqs guard_product_eqs guard_product_checks
    (fun i => if i = 0 then x0 else x1)
    (by
      intro g hg
      simp [guard_product_ineqs] at hg
      rcases hg with rfl | rfl <;> simp [evalR, monoEvalR, monoEvalFromR] <;> assumption)
    (by simp [guard_product_eqs])
  simp [evalR, monoEvalR, monoEvalFromR, guard_product_target] at h
  linarith

/-- Over the reals the bound is tight: `x = y = 1/2` gives exactly `1`. -/
theorem equality_constrained_real (x0 x1 : ℝ) (hf : x0 + x1 = 1) :
    1 ≤ 2 * x0 ^ 2 + 2 * x1 ^ 2 := by
  have h := Cert.sound_real equality_constrained_cert equality_constrained_target
    equality_constrained_ineqs equality_constrained_eqs equality_constrained_checks
    (fun i => if i = 0 then x0 else x1) (by simp [equality_constrained_ineqs])
    (by
      intro f hf'
      simp [equality_constrained_eqs] at hf'
      subst hf'
      simp [evalR, monoEvalR, monoEvalFromR]
      linarith)
  simp [evalR, monoEvalR, monoEvalFromR, equality_constrained_target] at h
  linarith

/-- The tight point really is attained, so the real statement is not slack. -/
example : 2 * (1 / 2 : ℝ) ^ 2 + 2 * (1 / 2 : ℝ) ^ 2 = 1 := by norm_num

#print axioms Cert.sound_real
#print axioms hidden_quadratic_real
#print axioms guard_product_real
#print axioms equality_constrained_real

end Forge.Checker.Real.Examples
