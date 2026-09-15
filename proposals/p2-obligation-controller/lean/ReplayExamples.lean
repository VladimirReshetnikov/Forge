/-
Proof-shaped examples corresponding to the Python experiments.
STATUS: NOT COMPILED IN THIS ENVIRONMENT. This is not the Forge tactic.
Uses Mathlib; choose a Mathlib revision compatible with your Lean toolchain.
There are no `sorry` placeholders; nevertheless compilation is unverified.
-/
import Mathlib

namespace ForgeReplayExamples

variable {α : Type*}

def cat : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: cat xs ys

def rev : List α → List α
  | [] => []
  | x :: xs => cat (rev xs) [x]

def revAux : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAux xs (x :: acc)

theorem cat_assoc (xs ys zs : List α) :
    cat (cat xs ys) zs = cat xs (cat ys zs) := by
  induction xs generalizing ys zs with
  | nil => simp [cat]
  | cons x xs ih => simp [cat, ih]

theorem cat_nil (xs : List α) : cat xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cat, ih]

theorem rev_cat (xs ys : List α) :
    rev (cat xs ys) = cat (rev ys) (rev xs) := by
  induction xs generalizing ys with
  | nil => simp [cat, rev, cat_nil]
  | cons x xs ih => simp [cat, rev, ih, cat_assoc]

theorem rev_rev (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, rev_cat, cat, ih]

-- This is the generalized statement discovered by the Python prototype.
theorem revAux_spec (xs acc : List α) :
    revAux xs acc = cat (rev xs) acc := by
  induction xs generalizing acc with
  | nil => simp [revAux, rev, cat]
  | cons x xs ih => simp [revAux, rev, ih, cat_assoc, cat]

theorem revAux_nil (xs : List α) : revAux xs [] = rev xs := by
  rw [revAux_spec, cat_nil]

def triangular : ℕ → ℚ
  | 0 => 0
  | n + 1 => triangular n + ((n : ℚ) + 1)

theorem triangular_closed (n : ℕ) :
    triangular n = (n : ℚ) * ((n : ℚ) + 1) / 2 := by
  induction n with
  | zero => norm_num [triangular]
  | succ n ih =>
    simp only [triangular, ih, Nat.cast_add, Nat.cast_one]
    ring

example (x : ℚ) : ∃ y : ℚ, x + 1 ≤ y ∧ y ≤ x + 2 := by
  refine ⟨x + 1, le_rfl, ?_⟩
  linarith

example (x : ℝ) : 0 < x ^ 2 - x + (13 : ℝ) / 50 := by
  have h : 0 ≤ (x - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
  nlinarith

-- Proposed theory-constrained instantiation should discover n / 2.
-- This particular example was not run against grind in this environment.
example (P : ℤ → Prop) (h : ∀ k : ℤ, P (2 * k + 1))
    (n : ℤ) (hodd : n % 2 = 1) : P n := by
  have he : 2 * (n / 2) + 1 = n := by omega
  simpa only [he] using h (n / 2)

end ForgeReplayExamples
