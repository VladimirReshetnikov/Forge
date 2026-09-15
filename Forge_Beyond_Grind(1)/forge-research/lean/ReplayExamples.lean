/-
Forge research: prospective Lean replay examples, NOT compiled in the authoring
session. These are handwritten proof scripts illustrating reconstruction, not a
completed Forge tactic and not exports from a Lean-certified Python checker.
Requires an existing, compatible mathlib project. No sorry or added axioms.
-/
import Mathlib

namespace ForgeReplay

variable {α : Type*}

def app : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys

def rev : List α → List α
  | [] => []
  | x :: xs => app (rev xs) [x]

def qrev : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => qrev xs (x :: acc)

@[simp] theorem app_right_id (xs : List α) : app xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]

theorem app_assoc (xs ys zs : List α) :
    app (app xs ys) zs = app xs (app ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]

theorem rev_app (xs ys : List α) :
    rev (app xs ys) = app (rev ys) (rev xs) := by
  induction xs with
  | nil => simp [app, rev]
  | cons x xs ih => simp [app, rev, ih, app_assoc]

theorem qrev_correct (xs acc : List α) :
    qrev xs acc = app (rev xs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [qrev, rev, app, ih, app_assoc]

theorem rev_involution (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, rev_app, app, ih]

theorem cyclic_quadratic (x y z : ℝ) :
    0 ≤ x^2 + y^2 + z^2 - x*y - y*z - z*x := by
  have hxy := sq_nonneg (x-y)
  have hyz := sq_nonneg (y-z)
  have hzx := sq_nonneg (z-x)
  nlinarith

theorem simplex_quadratic (x y : ℝ) (h : x+y=1) :
    (1:ℝ)/2 ≤ x^2+y^2 := by
  have hid : x^2+y^2-(1:ℝ)/2 =
      (1:ℝ)/2*(x-y)^2 + (1:ℝ)/2*(x+y-1)*(x+y+1) := by ring
  have hn := sq_nonneg (x-y)
  nlinarith

theorem box_product (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x^2 ≤ x := by
  have hc := mul_nonneg h0 (sub_nonneg.mpr h1)
  nlinarith

theorem residue_witness (n : ℤ) :
    ∃ k : ℤ, n ≤ k ∧ k < n+5 ∧ k % 5 = 2 := by
  refine ⟨n + (2-n) % 5, ?_, ?_, ?_⟩ <;> omega

#print axioms qrev_correct
#print axioms rev_involution
#print axioms cyclic_quadratic
#print axioms simplex_quadratic
#print axioms box_product
#print axioms residue_witness
end ForgeReplay
