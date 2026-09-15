/-
  NOT_RUN: no Lean executable was available in the authoring environment.
  Proposed proof-principle specimens, not an implementation of the forge tactic.
  No axioms or unfinished proof placeholders are introduced here.
-/
import Lean

namespace ForgeExtensions
universe u v w

inductive Reachable {S : Type u} (initial : S → Prop) (step : S → S → Prop) : S → Prop where
  | base {s : S} : initial s → Reachable initial step s
  | next {s t : S} : Reachable initial step s → step s t → Reachable initial step t

theorem reachableInvariant {S : Type u}
    {initial : S → Prop} {step : S → S → Prop} {P : S → Prop}
    (hinit : ∀ s, initial s → P s)
    (hstep : ∀ s t, P s → step s t → P t)
    {s : S} (h : Reachable initial step s) : P s := by
  induction h with
  | base hi => exact hinit _ hi
  | next _ hs ih => exact hstep _ _ ih hs

def runWord {S : Type u} {A : Type v} (step : S → A → S) : S → List A → S
  | s, [] => s
  | s, a :: w => runWord step (step s a) w

theorem runWordInvariant {S : Type u} {A : Type v}
    (step : S → A → S) (P : S → Prop)
    (hstep : ∀ s a, P s → P (step s a))
    (s : S) (hs : P s) (word : List A) : P (runWord step s word) := by
  induction word generalizing s with
  | nil => exact hs
  | cons a word ih => exact ih (step s a) (hstep s a hs)

/-- A finite-coordinate simulation. For weighted replay, `embed c` is `c * B`. -/
theorem simulateWord {S : Type u} {C : Type w} {A : Type v}
    (stepS : S → A → S) (stepC : C → A → C) (embed : C → S)
    (commutes : ∀ c a, embed (stepC c a) = stepS (embed c) a)
    (c : C) (word : List A) :
    embed (runWord stepC c word) = runWord stepS (embed c) word := by
  induction word generalizing c with
  | nil => rfl
  | cons a word ih =>
    change embed (runWord stepC (stepC c a) word) =
      runWord stepS (stepS (embed c) a) word
    rw [ih, commutes]

#print axioms reachableInvariant
#print axioms runWordInvariant
#print axioms simulateWord
end ForgeExtensions
