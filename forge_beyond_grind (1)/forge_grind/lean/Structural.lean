/-
Reference replay targets, not a `forge` implementation.
This file was NOT compiled in the artifact-producing environment.
It is intended to need only Lean's core library. No admitted proof is present.
-/
import Lean

namespace ForgeExamples

variable {α : Type}

def app : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys

def rev : List α → List α
  | [] => []
  | x :: xs => app (rev xs) [x]

def revAcc : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

theorem app_right_nil (xs : List α) : app xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [app, ih]

theorem app_assoc (xs ys zs : List α) :
    app (app xs ys) zs = app xs (app ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [app, ih]

theorem revAcc_spec (xs acc : List α) :
    revAcc xs acc = app (rev xs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [revAcc, rev, ih, app_assoc, app]

theorem revAcc_correct (xs : List α) : revAcc xs [] = rev xs := by
  rw [revAcc_spec, app_right_nil]

theorem rev_append (xs ys : List α) :
    rev (app xs ys) = app (rev ys) (rev xs) := by
  induction xs with
  | nil => simp only [app, rev, app_right_nil]
  | cons x xs ih => simp only [app, rev, ih, app_assoc]

theorem rev_involutive (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [rev, rev_append, ih, app]

#print axioms revAcc_correct
#print axioms rev_involutive

end ForgeExamples
