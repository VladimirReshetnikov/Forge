/-
GENERATED CANDIDATE PROOF SCRIPTS: not compiled in the authoring environment.
No theorem here is claimed to have passed Lean until `lake build` succeeds.
Generated from exact Python certificates; no `sorry` or oracle axioms inserted.
-/
import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ForgeReplay
theorem hidden_quadratic (x y : ℝ)
    : 0 ≤ ((21 : ℝ) + (-24 : ℝ) * (y) + ((99 : ℝ) / 7) * (y) ^ 2 + (-18 : ℝ) * (x) + ((-26 : ℝ) / 7) * (x) * (y) + ((78 : ℝ) / 7) * (x) ^ 2) := by
  have ht0 : 0 ≤ ((21 : ℝ) * (((1 : ℝ) + ((-4 : ℝ) / 7) * (y) + ((-3 : ℝ) / 7) * (x))) ^ 2) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ (21 : ℝ)) (sq_nonneg ((1 : ℝ) + ((-4 : ℝ) / 7) * (y) + ((-3 : ℝ) / 7) * (x))))
  have ht1 : 0 ≤ (((51 : ℝ) / 7) * ((((-49 : ℝ) / 51) * (y) + (1 : ℝ) * (x))) ^ 2) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ ((51 : ℝ) / 7)) (sq_nonneg (((-49 : ℝ) / 51) * (y) + (1 : ℝ) * (x))))
  have ht2 : 0 ≤ (((200 : ℝ) / 357) * (((1 : ℝ) * (y))) ^ 2) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ ((200 : ℝ) / 357)) (sq_nonneg ((1 : ℝ) * (y))))
  have hs : 0 ≤ ((((0 : ℝ) + ((21 : ℝ) * (((1 : ℝ) + ((-4 : ℝ) / 7) * (y) + ((-3 : ℝ) / 7) * (x))) ^ 2)) + (((51 : ℝ) / 7) * ((((-49 : ℝ) / 51) * (y) + (1 : ℝ) * (x))) ^ 2)) + (((200 : ℝ) / 357) * (((1 : ℝ) * (y))) ^ 2)) :=
    (add_nonneg (add_nonneg (add_nonneg (le_refl (0 : ℝ)) ht0) ht1) ht2)
  calc
    0 ≤ ((((0 : ℝ) + ((21 : ℝ) * (((1 : ℝ) + ((-4 : ℝ) / 7) * (y) + ((-3 : ℝ) / 7) * (x))) ^ 2)) + (((51 : ℝ) / 7) * ((((-49 : ℝ) / 51) * (y) + (1 : ℝ) * (x))) ^ 2)) + (((200 : ℝ) / 357) * (((1 : ℝ) * (y))) ^ 2)) := hs
    _ = ((21 : ℝ) + (-24 : ℝ) * (y) + ((99 : ℝ) / 7) * (y) ^ 2 + (-18 : ℝ) * (x) + ((-26 : ℝ) / 7) * (x) * (y) + ((78 : ℝ) / 7) * (x) ^ 2) := by ring

theorem equality_constrained (x y : ℝ)
    (he0 : ((-1 : ℝ) + (1 : ℝ) * (y) + (1 : ℝ) * (x)) = 0)
    : 0 ≤ (((-1 : ℝ) / 2) + (1 : ℝ) * (y) ^ 2 + (1 : ℝ) * (x) ^ 2) := by
  have ht0 : 0 ≤ (((1 : ℝ) / 2) * (((1 : ℝ) * (y) + (-1 : ℝ) * (x))) ^ 2) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ ((1 : ℝ) / 2)) (sq_nonneg ((1 : ℝ) * (y) + (-1 : ℝ) * (x))))
  have hs : 0 ≤ ((0 : ℝ) + (((1 : ℝ) / 2) * (((1 : ℝ) * (y) + (-1 : ℝ) * (x))) ^ 2)) :=
    (add_nonneg (le_refl (0 : ℝ)) ht0)
  have hi : (((((1 : ℝ) / 2) + ((1 : ℝ) / 2) * (y) + ((1 : ℝ) / 2) * (x)) * ((-1 : ℝ) + (1 : ℝ) * (y) + (1 : ℝ) * (x)))) = 0 := by
    simp only [he0, mul_zero, zero_mul, add_zero]
  have hid : (((-1 : ℝ) / 2) + (1 : ℝ) * (y) ^ 2 + (1 : ℝ) * (x) ^ 2) = ((0 : ℝ) + (((1 : ℝ) / 2) * (((1 : ℝ) * (y) + (-1 : ℝ) * (x))) ^ 2)) + (((((1 : ℝ) / 2) + ((1 : ℝ) / 2) * (y) + ((1 : ℝ) / 2) * (x)) * ((-1 : ℝ) + (1 : ℝ) * (y) + (1 : ℝ) * (x)))) := by ring
  rw [hid, hi, add_zero]
  exact hs


end ForgeReplay
