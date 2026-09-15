/-
  Merged from proposal p6-proof-logging-cdcl, file lean/Examples.lean.

  Widest variety of arithmetic specimens, and the only ones composing a
  certificate result through division (divided_box_bilinear) and deliberately
  avoiding a leading-coefficient side condition (discriminant_nonnegative).

  NOT COMPILED as part of this file's original proposal, and not compiled
  here either unless it appears in results/lean-core-elaboration.json.
  See docs/LEAN-STATUS.md for what has and has not been checked.
-/

/-
Integration specimens for the Forge design, NOT an implementation of `forge`.
These proofs have NOT been compiled in the creation environment.
Select a compatible Lean/Mathlib manifest, then run `lake env lean lean/Examples.lean`.
No `sorry`, new axiom, external solver, or native_decide is intentionally used.
-/
import Mathlib

namespace ForgeSpecimens

/-- The recursive call changes the accumulator, so its invariant must generalize it. -/
def triAcc : Nat → ℚ → ℚ
  | 0, a => a
  | n + 1, a => triAcc n (a + (n : ℚ) + 1)

/-- Specimen for the p=1 synthesized invariant. -/
theorem triAcc_spec (n : Nat) (a : ℚ) :
    triAcc n a = a + (n : ℚ) * ((n : ℚ) + 1) / 2 := by
  induction n generalizing a with
  | zero => simp [triAcc]
  | succ n ih =>
    rw [triAcc, ih]
    push_cast
    ring

/-- A concrete witness plus exact integer obligations. -/
theorem witness_between (n : Nat) : ∃ m : Nat, n < m ∧ m ≤ n + 2 := by
  refine ⟨n + 1, ?_, ?_⟩ <;> omega

/-- The cone certificate for the automatically discovered box-bilinear case. -/
theorem box_bilinear (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    0 ≤ x + y - 2 * x * y := by
  have hxy : 0 ≤ x * (1 - y) := mul_nonneg hx (sub_nonneg.mpr hy1)
  have hyx : 0 ≤ y * (1 - x) := mul_nonneg hy (sub_nonneg.mpr hx1)
  nlinarith

/-- A manually supplied identity: no nonzero assumption on the leading coefficient. -/
theorem discriminant_nonnegative (a b c t : ℝ)
    (h : a * t ^ 2 + b * t + c = 0) : 0 ≤ b ^ 2 - 4 * a * c := by
  have hid : b ^ 2 - 4 * a * c =
      (2 * a * t + b) ^ 2 - 4 * a * (a * t ^ 2 + b * t + c) := by ring
  rw [hid, h]
  nlinarith [sq_nonneg (2 * a * t + b)]

/-- The complete mathematical cooperation example, assembled by hand. -/
theorem divided_box_bilinear (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    0 ≤ (x + y - 2 * x * y) / (1 + (x - y) ^ 2) := by
  have hn := box_bilinear x y hx hy hx1 hy1
  have hd : 0 < 1 + (x - y) ^ 2 := by positivity
  exact div_nonneg hn (le_of_lt hd)

/-- The signed negative-cycle example used by the integer-difference prototype. -/
theorem negative_cycle (x y z : Int)
    (h1 : x - y ≤ 0) (h2 : y - z ≤ 0) (h3 : z - x ≤ -1) : False := by
  omega

end ForgeSpecimens
