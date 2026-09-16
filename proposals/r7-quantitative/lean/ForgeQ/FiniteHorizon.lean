import Mathlib

/-!
Candidate source, NOT compiler-validated in the authoring environment.
Only finite-horizon rational expectations are treated here. The target-
normalization, PMF interpretation, all-scheduler, and infinite-horizon
bridges required by the article are NOT implemented in this file.
-/
set_option autoImplicit false
namespace ForgeQ
open scoped BigOperators

abbrev QVector (n : Nat) := Fin n → ℚ

def wp {n : Nat} (P : Fin n → Fin n → ℚ) (v : QVector n) : QVector n :=
  fun s => ∑ t, P s t * v t

theorem wp_mono {n : Nat} (P : Fin n → Fin n → ℚ)
    (hP : ∀ s t, 0 ≤ P s t) {v w : QVector n} (h : ∀ s, v s ≤ w s) :
    ∀ s, wp P v s ≤ wp P w s := by
  intro s
  unfold wp
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_left (h t) (hP s t)

def costPrefix {n : Nat} (P : Fin n → Fin n → ℚ) (cost : QVector n) :
    Nat → QVector n
  | 0 => fun _ => 0
  | k + 1 => fun s => cost s + wp P (costPrefix P cost k) s

theorem costPrefix_le {n : Nat} (P : Fin n → Fin n → ℚ)
    (hP : ∀ s t, 0 ≤ P s t) (cost V : QVector n)
    (hV : ∀ s, 0 ≤ V s) (step : ∀ s, cost s + wp P V s ≤ V s) :
    ∀ k s, costPrefix P cost k s ≤ V s := by
  intro k
  induction k with
  | zero => exact hV
  | succ k ih =>
      intro s
      change cost s + wp P (costPrefix P cost k) s ≤ V s
      exact le_trans (add_le_add_left (wp_mono P hP ih s) (cost s)) (step s)

/-- A coupling's left marginal transports every rational observation. -/
theorem coupling_left_expectation {n m : Nat}
    (joint : Fin n → Fin m → ℚ) (mu : Fin n → ℚ)
    (marginal : ∀ i, (∑ j, joint i j) = mu i) (f : Fin n → ℚ) :
    (∑ i, ∑ j, joint i j * f i) = ∑ i, mu i * f i := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul, marginal i]

#print axioms wp_mono
#print axioms costPrefix_le
#print axioms coupling_left_expectation
end ForgeQ
