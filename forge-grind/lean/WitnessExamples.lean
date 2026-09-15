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
