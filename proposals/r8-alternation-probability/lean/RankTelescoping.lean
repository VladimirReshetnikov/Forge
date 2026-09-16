/-
NOT_RUN: This source was not compiled in the authoring environment.
This is an arithmetic lowering specimen, not a parity-game checker.
Target context: Lean v4.34.0. No Mathlib import is required.
-/
import Lean

namespace ForgeAP

/-- The first n nonnegative, natural-number increments. -/
def prefix (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefix w n + w n

/-- A local rank inequality bounds the accumulated strict progress.
For a parity threshold, w is the indicator of the unfavorable priority,
after the play has entered a tail with no larger priority. -/
theorem rank_telescoping (r w : Nat → Nat)
    (step : ∀ n, r (n + 1) + w n ≤ r n) :
    ∀ n, r n + prefix w n ≤ r 0 := by
  intro n
  induction n with
  | zero => simp [prefix]
  | succ n ih =>
      have hs := step n
      simp only [prefix]
      omega

theorem prefix_bounded (r w : Nat → Nat)
    (step : ∀ n, r (n + 1) + w n ≤ r n) (n : Nat) :
    prefix w n ≤ r 0 := by
  have h := rank_telescoping r w step n
  omega

#print axioms rank_telescoping
#print axioms prefix_bounded
end ForgeAP
