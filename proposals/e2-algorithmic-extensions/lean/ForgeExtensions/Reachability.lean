/-
Status: WRITTEN, NOT COMPILED in the accompanying run (no Lean executable).
A small proof-composition target, not an implemented forge tactic.
-/
import Lean
set_option autoImplicit false

namespace ForgeExtensions
universe u

inductive Reachable {S : Type u} (Initial : S → Prop)
    (Step : S → S → Prop) : S → Prop where
  | initial {s : S} : Initial s → Reachable Initial Step s
  | next {s t : S} : Reachable Initial Step s → Step s t →
      Reachable Initial Step t

theorem invariant_of_closed {S : Type u} (Initial : S → Prop)
    (Step : S → S → Prop) (P : S → Prop)
    (hinit : ∀ s, Initial s → P s)
    (hstep : ∀ s t, P s → Step s t → P t)
    {s : S} (h : Reachable Initial Step s) : P s := by
  induction h with
  | initial hi => exact hinit _ hi
  | next _ ht ih => exact hstep _ _ ih ht

end ForgeExtensions
#print axioms ForgeExtensions.invariant_of_closed
