/-
Forge Delta: generic induction bridge, authored but NOT COMPILED here.
This is not a reflected polynomial checker or an installed tactic.
-/
import Lean
set_option autoImplicit false

namespace ForgeDelta
universe u v

inductive Reachable {S : Type u} (step : S → S → Prop) (initial : S) : S → Prop where
  | base : Reachable step initial initial
  | next {s t : S} : Reachable step initial s → step s t → Reachable step initial t

theorem reachableInvariant {S : Type u} (step : S → S → Prop) (initial : S)
    (I : S → Prop) (h0 : I initial)
    (hstep : ∀ s t, I s → step s t → I t)
    (s : S) (hs : Reachable step initial s) : I s := by
  induction hs with
  | base => exact h0
  | next hs hst ih => exact hstep _ _ ih hst

def run {S : Type u} {A : Type v} (step : S → A → S) (s : S) : List A → S
  | [] => s
  | a :: as => run step (step s a) as

theorem runInvariant {S : Type u} {A : Type v}
    (step : S → A → S) (I : S → Prop)
    (preserve : ∀ s a, I s → I (step s a))
    (as : List A) (s : S) (hs : I s) : I (run step s as) := by
  induction as generalizing s with
  | nil => exact hs
  | cons a as ih => exact ih (step s a) (preserve s a hs)

theorem runRelation {S : Type u} {T : Type u} {A : Type v}
    (left : S → A → S) (right : T → A → T) (R : S → T → Prop)
    (preserve : ∀ s t a, R s t → R (left s a) (right t a))
    (as : List A) (s : S) (t : T) (h : R s t) :
    R (run left s as) (run right t as) := by
  induction as generalizing s t with
  | nil => exact h
  | cons a as ih => exact ih (left s a) (right t a) (preserve s t a h)

#print axioms reachableInvariant
#print axioms runInvariant
#print axioms runRelation
end ForgeDelta
