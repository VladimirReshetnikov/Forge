/-
HAND-WRITTEN CANDIDATE SCRIPTS: NOT COMPILED IN THE AUTHORING ENVIRONMENT.
These illustrate structural induction and cross-theory replay, not an
implementation of the complete `forge` tactic proposed in the article.
-/
import Mathlib

namespace ForgeReplay

def oddAccum : Nat → Int → Int
  | 0, a => a
  | n + 1, a => oddAccum n (a + (2 * (n : Int) + 1))

theorem oddAccum_eq (n : Nat) (a : Int) :
    oddAccum n a = a + (n : Int)^2 := by
  induction n generalizing a with
  | zero => simp [oddAccum]
  | succ n ih =>
    rw [oddAccum, ih] <;> push_cast <;> ring

/-- A nonlinear fact becomes an equality and is then used by congruence. -/
theorem cross_theory (x y : ℝ) (f : ℝ → ℝ)
    (hupper : x^2 - 2*x*y + y^2 ≤ 0) :
    f (x^2 - 2*x*y + y^2) = f 0 := by
  have hnonneg : 0 ≤ x^2 - 2*x*y + y^2 := by
    calc
      0 ≤ (x-y)^2 := sq_nonneg (x-y)
      _ = x^2 - 2*x*y + y^2 := by ring
  have heq : x^2 - 2*x*y + y^2 = 0 := le_antisymm hupper hnonneg
  exact congrArg f heq

/-- Even-multiplicity zeros are kept as explicit squares. -/
theorem univariate_factored (x : ℝ) (hl : -2 ≤ x) (hu : x ≤ 2) :
    0 ≤ (x^2-2)^2 * (x^2+1) * (x+2) * (2-x) := by
  have hleft : 0 ≤ x+2 := by linarith
  have hright : 0 ≤ 2-x := by linarith
  positivity

end ForgeReplay

#print axioms ForgeReplay.oddAccum_eq
#print axioms ForgeReplay.cross_theory
