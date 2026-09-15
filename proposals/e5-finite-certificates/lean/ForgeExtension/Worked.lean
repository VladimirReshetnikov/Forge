/-
Status: SOURCE SPECIMEN, NOT COMPILED in the preparation environment.
No sorry, axiom, or native_decide is used. This is a hand-written replay target,
not evidence of an implemented source-to-certificate tactic.
-/
import ForgeExtension.Core
import Mathlib

namespace ForgeExtension.Worked

structure State where
  x : ℚ
  y : ℚ
  z : ℚ
  w : ℚ

def step (s : State) (_ : Unit) : State :=
  ⟨s.y ^ 2, s.x, s.w ^ 2, s.z⟩

def invariant (s : State) : Prop :=
  s.x = s.z ∧ s.y ^ 2 = s.w ^ 2

theorem initial (a b : ℚ) : invariant ⟨a, b, a, -b⟩ := by
  constructor
  · rfl
  · dsimp
    ring

theorem preserved (s : State) (a : Unit) (h : invariant s) :
    invariant (step s a) := by
  rcases h with ⟨hx, hy⟩
  constructor
  · exact hy
  · change s.x ^ 2 = s.z ^ 2
    rw [hx]

theorem all_words (a b : ℚ) (word : List Unit) :
    (ForgeExtension.run step ⟨a, b, a, -b⟩ word).x =
    (ForgeExtension.run step ⟨a, b, a, -b⟩ word).z := by
  exact (ForgeExtension.run_preserves step invariant preserved
    ⟨a, b, a, -b⟩ word (initial a b)).1

-- The nonconstant multiplier appearing in the synthesized ideal certificate.
theorem factor_certificate (x z : ℚ) :
    x ^ 2 - z ^ 2 = (x + z) * (x - z) := by ring

-- Pole-free local identity for the squared-binomial sum. The bridge to
-- Nat.choose, endpoint lemmas, and finite summation remain to be implemented.
theorem binomial_square_local (A B n k : ℚ)
    (h : (n + 1 - k) * A - k * B = 0) :
    (n + 1) * (A + B)^2 - 2 * (2*n + 1) * B^2 =
      (2*(k + 1) - 3*n - 3) * B^2 - (2*k - 3*n - 3) * A^2 := by
  have ident :
      ((n + 1) * (A + B)^2 - 2 * (2*n + 1) * B^2) -
      ((2*(k + 1) - 3*n - 3) * B^2 - (2*k - 3*n - 3) * A^2) =
      2 * (B - A) * ((n + 1 - k) * A - k * B) := by ring
  rw [h, mul_zero] at ident
  exact sub_eq_zero.mp ident

end ForgeExtension.Worked
