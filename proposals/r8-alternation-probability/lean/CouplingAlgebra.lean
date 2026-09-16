/-
NOT_RUN: This source was not compiled in the authoring environment.
These are finite rational marginal lemmas, not a Boolean certificate checker,
not Hall-duality formalization, and not a source-to-PMF interpretation.
Target: Lean v4.34.0 with the Mathlib revision recorded in docs/sources.json.
-/
import Mathlib

namespace ForgeAP

structure RationalCoupling {m n : Nat}
    (mu : Fin m → ℚ) (nu : Fin n → ℚ) where
  mass : Fin m → Fin n → ℚ
  nonnegative : ∀ i j, 0 ≤ mass i j
  row_mass : ∀ i, (∑ j, mass i j) = mu i
  column_mass : ∀ j, (∑ i, mass i j) = nu j

variable {m n : Nat} {mu : Fin m → ℚ} {nu : Fin n → ℚ}

theorem total_mass (c : RationalCoupling mu nu)
    (normalized : (∑ i, mu i) = 1) :
    (∑ i, ∑ j, c.mass i j) = 1 := by
  calc
    (∑ i, ∑ j, c.mass i j) = ∑ i, mu i := by
      apply Finset.sum_congr rfl
      intro i _
      exact c.row_mass i
    _ = 1 := normalized

theorem left_expectation (c : RationalCoupling mu nu) (f : Fin m → ℚ) :
    (∑ i, ∑ j, c.mass i j * f i) = ∑ i, mu i * f i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, c.row_mass i]

theorem right_expectation (c : RationalCoupling mu nu) (f : Fin n → ℚ) :
    (∑ j, ∑ i, c.mass i j * f j) = ∑ j, nu j * f j := by
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, c.column_mass j]

#print axioms total_mass
#print axioms left_expectation
#print axioms right_expectation
end ForgeAP
