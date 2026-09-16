/-
UNCOMPILED CANDIDATES. No Lean executable was available in the authoring environment.
These small lemmas fix intended semantics; they do not check a certificate,
reify a source goal, or implement the Forge tactic. No kernel acceptance is claimed.
-/
import Mathlib

namespace Forge.AnalyticCandidates

/-- An already-proved source factorization, not a raw candidate data format. -/
structure AnchoredWitness (f : ℝ → ℝ) (m : ℕ) (b : ℝ) where
  quotient : ℝ → ℝ
  represents : ∀ x ∈ Set.Icc (0 : ℝ) b, f x = x ^ m * quotient x
  quotient_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) b, 0 ≤ quotient x

/-- Algebraic end of the anchored bridge. Model soundness remains separate. -/
theorem AnchoredWitness.nonneg
    {f : ℝ → ℝ} {m : ℕ} {b : ℝ}
    (w : AnchoredWitness f m b) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) b) :
    0 ≤ f x := by
  rw [w.represents x hx]
  exact mul_nonneg (pow_nonneg hx.1 m) (w.quotient_nonneg x hx)

/-- Finite telescoping only. To use a tail from N, instantiate a i with source (N+i).
    No infinite sum is used before summability has been established. -/
theorem prefix_le_barrier
    (a B : ℕ → ℝ)
    (step : ∀ n : ℕ, a n + B (n + 1) ≤ B n) :
    ∀ m : ℕ, (∑ i ∈ Finset.range m, a i) ≤ B 0 - B m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hs := step m
      linarith

#print axioms AnchoredWitness.nonneg
#print axioms prefix_le_barrier

end Forge.AnalyticCandidates
