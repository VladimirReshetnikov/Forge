/-
  Merged from proposal p7-successor-architecture, file lean/WitnessExamples.lean.

  Integer-lattice witness family and the 6x + 10y parity obstruction. The only
  Bezout/impossibility material.

  NOT COMPILED as part of this file's original proposal, and not compiled
  here either unless it appears in results/lean-core-elaboration.json.
  See docs/LEAN-STATUS.md for what has and has not been checked.
-/

/-
STATUS: NOT COMPILED IN THE AUTHORING ENVIRONMENT.
Illustrative ordinary proofs; no implementation of the Forge tactic is claimed.
-/
import Mathlib

namespace ForgeArtifacts

theorem parametricWitness (m : ℤ) : ∃ x y : ℤ, 6*x + 10*y = 2*m := by
  refine ⟨2*m, -m, ?_⟩
  ring

theorem witnessFamily (t : ℤ) : 6*(2-5*t) + 10*(-1+3*t) = 2 := by
  ring

-- A deliberate reminder: the negative linear example already suits omega.
-- Its presence is not evidence of an existing grind limitation.
theorem parityObstruction : ¬ ∃ x y : ℤ, 6*x + 10*y = 1 := by
  omega

end ForgeArtifacts
