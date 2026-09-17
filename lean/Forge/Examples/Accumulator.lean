/-
  Merged from proposal p3-planner-certificate-layer, file lean/InductionExamples.lean.

  Accumulator specifications built on Mathlib's List.reverse, including
  energyAcc_ge -- the only accumulator INEQUALITY invariant.

  NOT COMPILED as part of this file's original proposal. Since compiled here,
  on the pinned toolchain against the pinned Mathlib, with no errors and no
  `sorry`, by tools/build_mathlib_forge.py (results/lean-mathlib-forge.json);
  its theorems pass lean/MathlibAudit.lean. The status line below is the
  original author's, kept as written.
-/

/- Standalone integration targets. NOT COMPILED in the supplied experiment.
   These are ordinary proofs, not an implementation of the proposed Forge planner. -/
import Mathlib

namespace ForgeExamples

universe u
variable {α : Type u}

def reverseAcc : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => reverseAcc xs (x :: acc)

theorem reverseAcc_spec (xs acc : List α) :
    reverseAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [reverseAcc]
  | cons x xs ih =>
      simp [reverseAcc, List.reverse_cons, ih, List.append_assoc]

def lengthAcc : List α → Nat → Nat
  | [], n => n
  | _ :: xs, n => lengthAcc xs (n + 1)

theorem lengthAcc_spec (xs : List α) (n : Nat) :
    lengthAcc xs n = xs.length + n := by
  induction xs generalizing n with
  | nil => simp [lengthAcc]
  | cons x xs ih =>
      simp only [lengthAcc, ih, List.length_cons]
      omega

-- This illustrates the *proposed* cooperation of induction and an ordered solver.
def energyAcc : List ℝ → ℝ → ℝ
  | [], a => a
  | x :: xs, a => energyAcc xs (a + (x - 1)^2)

theorem energyAcc_ge (xs : List ℝ) (a : ℝ) : a ≤ energyAcc xs a := by
  induction xs generalizing a with
  | nil => simp [energyAcc]
  | cons x xs ih =>
      have h₁ : a ≤ a + (x - 1)^2 := le_add_of_nonneg_right (sq_nonneg (x - 1))
      have h₂ : a + (x - 1)^2 ≤ energyAcc xs (a + (x - 1)^2) := ih _
      exact le_trans h₁ h₂

#print axioms reverseAcc_spec
#print axioms lengthAcc_spec
#print axioms energyAcc_ge

end ForgeExamples
