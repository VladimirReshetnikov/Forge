/-
  Merged from proposal p8-obligation-broker, file lean/ReplayExamples.lean.

  Mixed obstruction, certificate identity, product bound, and a list-fold
  accumulator over the integers using List.sum and List.length.

  NOT COMPILED as part of this file's original proposal, and not compiled
  here either unless it appears in results/lean-core-elaboration.json.
  See docs/LEAN-STATUS.md for what has and has not been checked.
-/

/-
UNCOMPILED ILLUSTRATIVE LEAN REPLAY RECIPES.

This file is not the Forge tactic. No Lean compiler was available in the
execution environment. The associated identities and Python algorithms were
executed and tested, but these scripts were not. They use conventional Mathlib
tactics to show the intended final proof shape; they are not grind benchmarks.
No `sorry`, new axiom, or native_decide is used here.
-/
import Mathlib

namespace ForgeExamples

theorem mixed_obstruction (x y u : ℝ)
    (hxy : x + y = 1) (hu : u = x * y) (hbound : (1 : ℝ) / 3 ≤ u) :
    False := by
  nlinarith [sq_nonneg (x - y)]

theorem certificate_identity (x y u : ℝ) :
    3 * (x - y)^2 + 12 * (u - (1 : ℝ) / 3)
      - 3 * (x + y + 1) * (x + y - 1) - 12 * (u - x * y) = -1 := by
  ring

theorem product_bound (a b x y : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : a ≤ x) (hy : b ≤ y) :
    a * b ≤ x * y := by
  have hp : 0 ≤ (x - a) * (y - b) :=
    mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  have h1 : 0 ≤ b * (x - a) := mul_nonneg hb (sub_nonneg.mpr hx)
  have h2 : 0 ≤ a * (y - b) := mul_nonneg ha (sub_nonneg.mpr hy)
  nlinarith

def run (w c : ℤ) : List ℤ → ℤ → ℤ
  | [], a => a
  | h :: t, a => run w c t (a + w * h + c)

theorem run_invariant (w c : ℤ) (xs : List ℤ) (a : ℤ) :
    run w c xs a = a + w * xs.sum + c * (xs.length : ℤ) := by
  induction xs generalizing a with
  | nil => simp [run]
  | cons h t ih =>
      simp only [run, List.sum_cons, List.length_cons]
      rw [ih]
      push_cast
      ring

#print axioms mixed_obstruction
#print axioms certificate_identity
#print axioms product_bound
#print axioms run_invariant

end ForgeExamples
