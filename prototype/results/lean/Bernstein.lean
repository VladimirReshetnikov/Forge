/-
GENERATED CANDIDATE PROOF SCRIPTS: not compiled in the authoring environment.
No theorem here is claimed to have passed Lean until `lake build` succeeds.
Generated from exact Python certificates; no `sorry` or oracle axioms inserted.
-/
import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ForgeReplay
theorem shifted_square_box (x : ℝ) (hxl : 0 ≤ x) (hxu : x ≤ 1) :
    0 ≤ (1) * (x) ^ 2 + ((-1 / 2)) * (x) + ((33 / 400)) := by
  rcases le_total x ((1 / 2)) with hs_r | hs_r
  ·
    rcases le_total x ((1 / 4)) with hs_rl | hs_rl
    ·
      have lo_rll_0 : 0 ≤ x - (0) := by linarith
      have hi_rll_0 : 0 ≤ ((1 / 4)) - x := by linarith
      calc
        0 ≤ ((33 / 25)) * (((1 / 4)) - x) ^ 2 +
            ((16 / 25)) * (x - (0)) ^ 1 * (((1 / 4)) - x) ^ 1 +
            ((8 / 25)) * (x - (0)) ^ 2 := by positivity
        _ = (1) * (x) ^ 2 + ((-1 / 2)) * (x) + ((33 / 400)) := by ring
    ·
      have lo_rlr_0 : 0 ≤ x - ((1 / 4)) := by linarith
      have hi_rlr_0 : 0 ≤ ((1 / 2)) - x := by linarith
      calc
        0 ≤ ((8 / 25)) * (((1 / 2)) - x) ^ 2 +
            ((16 / 25)) * (x - ((1 / 4))) ^ 1 * (((1 / 2)) - x) ^ 1 +
            ((33 / 25)) * (x - ((1 / 4))) ^ 2 := by positivity
        _ = (1) * (x) ^ 2 + ((-1 / 2)) * (x) + ((33 / 400)) := by ring
  ·
    have lo_rr_0 : 0 ≤ x - ((1 / 2)) := by linarith
    have hi_rr_0 : 0 ≤ (1) - x := by linarith
    calc
      0 ≤ ((33 / 100)) * ((1) - x) ^ 2 +
          ((83 / 50)) * (x - ((1 / 2))) ^ 1 * ((1) - x) ^ 1 +
          ((233 / 100)) * (x - ((1 / 2))) ^ 2 := by positivity
      _ = (1) * (x) ^ 2 + ((-1 / 2)) * (x) + ((33 / 400)) := by ring


end ForgeReplay
