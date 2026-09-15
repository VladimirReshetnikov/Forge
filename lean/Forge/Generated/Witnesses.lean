/-
  Merged from proposal p1-structural-search, file lean/GeneratedReplay.lean.

  Hidden-quadratic certificate, power-sum recurrences, and the integral affine
  witness.

  NOT COMPILED as part of this file's original proposal, and not compiled
  here either unless it appears in results/lean-core-elaboration.json.
  See docs/LEAN-STATUS.md for what has and has not been checked.
-/

/-
GENERATED CANDIDATE PROOF SCRIPTS: not compiled in the authoring environment.
No theorem here is claimed to have passed Lean until `lake build` succeeds.
Generated from exact Python certificates; no `sorry` or oracle axioms inserted.
-/
import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ForgeReplay

/-- Exact Schur-complement certificate; expanded target. -/
theorem hidden_quadratic (x y : ℝ) : 0 ≤ ((78 / 7)) * (x) ^ 2 + ((-26 / 7)) * (x) * (y) + (-18) * (x) + ((99 / 7)) * (y) ^ 2 + (-24) * (y) + (21) := by
  calc
    0 ≤ (21) * (((-3 / 7)) * (x) + ((-4 / 7)) * (y) + (1)) ^ 2 + ((51 / 7)) * ((1) * (x) + ((-49 / 51)) * (y)) ^ 2 + ((200 / 357)) * ((1) * (y)) ^ 2 := by positivity
    _ = ((78 / 7)) * (x) ^ 2 + ((-26 / 7)) * (x) * (y) + (-18) * (x) + ((99 / 7)) * (y) ^ 2 + (-24) * (y) + (21) := by ring

def powerSum0 : ℕ → ℚ
  | 0 => 0
  | n + 1 => powerSum0 n + ((1))

theorem powerSum0_formula (n : ℕ) :
    powerSum0 n = (1) * ((n : ℚ)) := by
  induction n with
  | zero => norm_num [powerSum0]
  | succ n ih =>
    rw [powerSum0, ih] <;> push_cast <;> ring

def powerSum1 : ℕ → ℚ
  | 0 => 0
  | n + 1 => powerSum1 n + ((1) * ((n : ℚ)))

theorem powerSum1_formula (n : ℕ) :
    powerSum1 n = ((1 / 2)) * ((n : ℚ)) ^ 2 + ((-1 / 2)) * ((n : ℚ)) := by
  induction n with
  | zero => norm_num [powerSum1]
  | succ n ih =>
    rw [powerSum1, ih] <;> push_cast <;> ring

def powerSum2 : ℕ → ℚ
  | 0 => 0
  | n + 1 => powerSum2 n + ((1) * ((n : ℚ)) ^ 2)

theorem powerSum2_formula (n : ℕ) :
    powerSum2 n = ((1 / 3)) * ((n : ℚ)) ^ 3 + ((-1 / 2)) * ((n : ℚ)) ^ 2 + ((1 / 6)) * ((n : ℚ)) := by
  induction n with
  | zero => norm_num [powerSum2]
  | succ n ih =>
    rw [powerSum2, ih] <;> push_cast <;> ring

def powerSum3 : ℕ → ℚ
  | 0 => 0
  | n + 1 => powerSum3 n + ((1) * ((n : ℚ)) ^ 3)

theorem powerSum3_formula (n : ℕ) :
    powerSum3 n = ((1 / 4)) * ((n : ℚ)) ^ 4 + ((-1 / 2)) * ((n : ℚ)) ^ 3 + ((1 / 4)) * ((n : ℚ)) ^ 2 := by
  induction n with
  | zero => norm_num [powerSum3]
  | succ n ih =>
    rw [powerSum3, ih] <;> push_cast <;> ring

def powerSum4 : ℕ → ℚ
  | 0 => 0
  | n + 1 => powerSum4 n + ((1) * ((n : ℚ)) ^ 4)

theorem powerSum4_formula (n : ℕ) :
    powerSum4 n = ((1 / 5)) * ((n : ℚ)) ^ 5 + ((-1 / 2)) * ((n : ℚ)) ^ 4 + ((1 / 3)) * ((n : ℚ)) ^ 3 + ((-1 / 30)) * ((n : ℚ)) := by
  induction n with
  | zero => norm_num [powerSum4]
  | succ n ih =>
    rw [powerSum4, ih] <;> push_cast <;> ring

def powerSum5 : ℕ → ℚ
  | 0 => 0
  | n + 1 => powerSum5 n + ((1) * ((n : ℚ)) ^ 5)

theorem powerSum5_formula (n : ℕ) :
    powerSum5 n = ((1 / 6)) * ((n : ℚ)) ^ 6 + ((-1 / 2)) * ((n : ℚ)) ^ 5 + ((5 / 12)) * ((n : ℚ)) ^ 4 + ((-1 / 12)) * ((n : ℚ)) ^ 2 := by
  induction n with
  | zero => norm_num [powerSum5]
  | succ n ih =>
    rw [powerSum5, ih] <;> push_cast <;> ring

def powerSum6 : ℕ → ℚ
  | 0 => 0
  | n + 1 => powerSum6 n + ((1) * ((n : ℚ)) ^ 6)

theorem powerSum6_formula (n : ℕ) :
    powerSum6 n = ((1 / 7)) * ((n : ℚ)) ^ 7 + ((-1 / 2)) * ((n : ℚ)) ^ 6 + ((1 / 2)) * ((n : ℚ)) ^ 5 + ((-1 / 6)) * ((n : ℚ)) ^ 3 + ((1 / 42)) * ((n : ℚ)) := by
  induction n with
  | zero => norm_num [powerSum6]
  | succ n ih =>
    rw [powerSum6, ih] <;> push_cast <;> ring

theorem affine_witness (x y : ℤ) :
    ∃ u v : ℤ, u + 2*v = 3*x-y+5 ∧ v = 2*x+4*y-3 := by
  refine ⟨(-1) * (x) + (-9) * (y) + (11), (2) * (x) + (4) * (y) + (-3), ?_⟩
  constructor <;> ring

end ForgeReplay

#print axioms ForgeReplay.hidden_quadratic
#print axioms ForgeReplay.powerSum6_formula
