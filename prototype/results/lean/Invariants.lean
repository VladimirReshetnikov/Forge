/-
GENERATED CANDIDATE PROOF SCRIPTS: not compiled in the authoring environment.
No theorem here is claimed to have passed Lean until `lake build` succeeds.
Generated from exact Python certificates; no `sorry` or oracle axioms inserted.
-/
import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ForgeReplay

def orbit {α : Type} (T : α → α) (s₀ : α) : Nat → α
  | 0 => s₀
  | n + 1 => T (orbit T s₀ n)

theorem orbit_invariant {α : Type} (T : α → α) (s₀ : α)
    (I : α → ℝ) (hbase : I s₀ = 0) (hstep : ∀ s, I (T s) = I s) :
    ∀ n, I (orbit T s₀ n) = 0 := by
  intro n
  induction n with
  | zero => simpa only [orbit] using hbase
  | succ n ih => simpa only [orbit, hstep] using ih
def state_cubic : ℝ × ℝ := ((0 : ℝ), (0 : ℝ))
def step_cubic (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (3 : ℝ) * (s.1) + (3 : ℝ) * (s.1) ^ 2 + (1 : ℝ) * (s.1) ^ 3))
def invariant_cubic (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((-1 : ℝ) / 4) * (s.1) ^ 2 + ((-1 : ℝ) / 2) * (s.1) ^ 3 + ((-1 : ℝ) / 4) * (s.1) ^ 4)
theorem preserved_cubic (n : Nat) :
    invariant_cubic (orbit step_cubic state_cubic n) = 0 := by
  apply orbit_invariant step_cubic state_cubic invariant_cubic
  · norm_num [invariant_cubic, state_cubic]
  · intro s
    dsimp [invariant_cubic, step_cubic]
    ring

def acc_square : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_square n (a + ((1 : ℚ) * ((n : ℚ)) ^ 2))

theorem invariant_square (n : ℕ) (a : ℚ) :
    acc_square n a = ((1 : ℚ) * (a) + ((1 : ℚ) / 6) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ)) ^ 2 + ((1 : ℚ) / 3) * ((n : ℚ)) ^ 3) := by
  induction n generalizing a with
  | zero => norm_num [acc_square]
  | succ n ih =>
    rw [acc_square, ih]
    push_cast <;> ring


end ForgeReplay
