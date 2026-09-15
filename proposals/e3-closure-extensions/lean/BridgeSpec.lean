/-
  UNCOMPILED SPECIMEN: NOT_RUN.
  Intended baseline: leanprover/lean4:v4.34.0.
  No Lean executable was available when this package was produced.
  This is not an implementation of forge or of a polynomial certificate checker.
-/
import Lean

set_option autoImplicit false

namespace ForgeClosureSpec

universe u v w z

/-- Finite-word execution, with the first input symbol executed first. -/
def run {S : Type u} {A : Type v} (step : S → A → S)
    (s : S) : List A → S
  | [] => s
  | a :: xs => run step (step s a) xs

/-- Generic invariant preservation. The caller must prove step preservation. -/
theorem invariant_run {S : Type u} {A : Type v}
    (step : S → A → S) (I : S → Prop)
    (hstep : ∀ s a, I s → I (step s a))
    (s : S) (hs : I s) (xs : List A) : I (run step s xs) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih =>
    exact ih (s := step s a) (hstep s a hs)

/-- Relational preservation for two executions reading the same input. -/
theorem relation_run {S : Type u} {T : Type v} {A : Type w}
    (left : S → A → S) (right : T → A → T)
    (R : S → T → Prop)
    (hstep : ∀ s t a, R s t → R (left s a) (right t a))
    (s : S) (t : T) (h : R s t) (xs : List A) :
    R (run left s xs) (run right t xs) := by
  induction xs generalizing s t with
  | nil => exact h
  | cons a xs ih =>
    exact ih (s := left s a) (t := right t a) (hstep s t a h)

/-- Observation equality follows from a relation preserving both steps. -/
theorem observations_run {S : Type u} {T : Type v} {A : Type w}
    {O : Type z}
    (left : S → A → S) (right : T → A → T)
    (ol : S → O) (or_ : T → O) (R : S → T → Prop)
    (hstep : ∀ s t a, R s t → R (left s a) (right t a))
    (hout : ∀ s t, R s t → ol s = or_ t)
    (s : S) (t : T) (h : R s t) (xs : List A) :
    ol (run left s xs) = or_ (run right t xs) := by
  exact hout _ _ (relation_run left right R hstep s t h xs)

/-- A commuting source-to-machine step map transports every finite fold. -/
theorem run_map {S : Type u} {T : Type v} {A : Type w}
    (source : S → A → S) (target : T → A → T) (encode : S → T)
    (commute : ∀ s a, encode (source s a) = target (encode s) a)
    (s : S) (xs : List A) :
    encode (run source s xs) = run target (encode s) xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
    change encode (run source (source s a) xs) =
      run target (target (encode s) a) xs
    rw [ih, commute]

end ForgeClosureSpec
