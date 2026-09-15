/- Hand-written integration target, NOT COMPILED in this environment.
   The Python search found a two-dimensional closure for this example.
   This file illustrates how its relational meaning can be reconstructed. -/
import Mathlib
set_option autoImplicit false
namespace ForgeDeltaWorked

def leftStep (s : ℚ × ℚ) (u : ℚ) : ℚ × ℚ := (s.1 + s.2, s.2 + u)
def rightStep (s : ℚ × ℚ) (u : ℚ) : ℚ × ℚ := (s.1 + s.2, s.2 + u)

def leftRun (s : ℚ × ℚ) : List ℚ → ℚ × ℚ
  | [] => s
  | u :: us => leftRun (leftStep s u) us

def rightRun (s : ℚ × ℚ) : List ℚ → ℚ × ℚ
  | [] => s
  | u :: us => rightRun (rightStep s u) us

theorem relational (us : List ℚ) (s t : ℚ × ℚ)
    (h0 : s.1 - t.1 = 0) (h1 : s.2 - t.2 = 0) :
    (leftRun s us).1 = (rightRun t us).1 := by
  induction us generalizing s t with
  | nil =>
      simp only [leftRun, rightRun]
      exact sub_eq_zero.mp h0
  | cons u us ih =>
      apply ih (leftStep s u) (rightStep t u)
      · change (s.1 + s.2) - (t.1 + t.2) = 0
        linear_combination h0 + h1
      · change (s.2 + u) - (t.2 + u) = 0
        linear_combination h1

#print axioms relational
end ForgeDeltaWorked
