/-
Candidate analytic bridge. GENERATED / NOT COMPILED in the authoring environment.
No `sorry`, `admit`, or new axioms are used. See STATUS.md for the exact status.
The intended baseline is the Forge-pinned Lean / Mathlib project, not latest.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace ForgeAnalytic
open Set

/-- One integrating-factor step, with an explicit source derivative equation. -/
theorem ladder_step {f g : ℝ → ℝ} {a rho : ℝ}
    (hf : ∀ t, HasDerivAt f (rho * f t + g t) t)
    (ha : 0 ≤ f a)
    (hg : ∀ t, a ≤ t → 0 ≤ g t) :
    ∀ t, a ≤ t → 0 ≤ f t := by
  let w : ℝ → ℝ := fun t => Real.exp (-rho * t) * f t
  have hw : ∀ t, HasDerivAt w (Real.exp (-rho * t) * g t) t := by
    intro t
    have he : HasDerivAt (fun s : ℝ => Real.exp (-rho * s))
        (Real.exp (-rho * t) * (-rho)) t := by
      simpa using (((hasDerivAt_id t).const_mul (-rho)).exp)
    convert he.mul (hf t) using 1 <;> dsimp [w] <;> ring
  have hc : ContinuousOn w (Ici a) := by
    intro t ht
    exact (hw t).continuousAt.continuousWithinAt
  have hm : MonotoneOn w (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a) hc
      (fun t _ => (hw t).hasDerivWithinAt)
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (hg t (interior_subset ht))
  intro t ht
  have hwa : 0 ≤ w a := mul_nonneg (Real.exp_pos _).le ha
  have hwt : 0 ≤ w t := hwa.trans (hm (le_refl a) ht ht)
  by_contra h
  have hft : f t < 0 := lt_of_not_ge h
  have hwneg : w t < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hft
  exact (not_lt_of_ge hwt) hwneg

#print axioms ladder_step
end ForgeAnalytic
