/-
Forge relational closure: semantic proof skeleton.
STATUS: authored, NOT COMPILED in this environment. No `forge` tactic is defined.
This file needs only Lean core; it does not formalize the Python checker.
-/
namespace ForgeRelationalClosure
universe u v

inductive Reachable {S : Type u} (Initial : S → Prop)
    (Step : S → S → Prop) : S → Prop where
  | initial {s : S} : Initial s → Reachable Initial Step s
  | advance {s t : S} : Reachable Initial Step s → Step s t →
      Reachable Initial Step t

theorem reachable_invariant {S : Type u}
    {Initial : S → Prop} {Step : S → S → Prop} {Inv : S → Prop}
    (base : ∀ s, Initial s → Inv s)
    (preserve : ∀ s t, Inv s → Step s t → Inv t)
    {s : S} (h : Reachable Initial Step s) : Inv s := by
  induction h with
  | initial hi => exact base _ hi
  | advance _ hstep ih => exact preserve _ _ ih hstep

theorem fold_preserves {S : Type u} {A : Type v}
    (step : S → A → S) (Inv : S → Prop)
    (preserve : ∀ s a, Inv s → Inv (step s a)) :
    ∀ (xs : List A) (s : S), Inv s → Inv (xs.foldl step s) := by
  intro xs
  induction xs with
  | nil =>
      intro s hs
      exact hs
  | cons a xs ih =>
      intro s hs
      exact ih (step s a) (preserve s a hs)

end ForgeRelationalClosure
