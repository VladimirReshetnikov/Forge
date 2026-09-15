/-
Status: SOURCE SPECIMEN, NOT COMPILED in the preparation environment.
This file supplies only the semantic induction glue. It is not a reflected
checker, source reifier, or implementation of the forge tactic.
-/
import Lean

namespace ForgeExtension
universe u v

def run {State : Type u} {Action : Type v}
    (step : State → Action → State) : State → List Action → State
  | s, [] => s
  | s, a :: rest => run step (step s a) rest

theorem run_preserves {State : Type u} {Action : Type v}
    (step : State → Action → State) (Inv : State → Prop)
    (hstep : ∀ s a, Inv s → Inv (step s a))
    (s : State) (word : List Action) (hs : Inv s) :
    Inv (run step s word) := by
  induction word generalizing s with
  | nil => exact hs
  | cons a rest ih =>
      exact ih (step s a) (hstep s a hs)

end ForgeExtension
