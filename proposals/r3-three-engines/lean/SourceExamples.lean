/-
UNCOMPILED SPECIMENS. These are source-level mathematical examples, not the
implementation or validation of any new reflected checker. Mathlib signatures
must be checked in the selected pinned project. No `sorry` is used as evidence.
-/
import Mathlib

universe u
namespace ForgeDelta

example (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃ z : ℝ, 0 ≤ z ∧ x + y - 1 ≤ z ∧ z ≤ x ∧ z ≤ y := by
  refine ⟨max 0 (x + y - 1), le_max_left _ _, le_max_right _ _, ?_, ?_⟩
  · exact max_le hx0 (by linarith)
  · exact max_le hy0 (by linarith)

-- The critical-pair consequence itself needs only associativity.
-- The prototype discovers its original-relation polynomial certificate.
example {A : Type u} [Semigroup A] (a b : A)
    (hab : a * b = a) (hba : b * a = b) : a * a = a := by
  calc
    a * a = (a * b) * a := by rw [hab]
    _ = a * (b * a) := mul_assoc _ _ _
    _ = a * b := by rw [hba]
    _ = a := hab

end ForgeDelta
