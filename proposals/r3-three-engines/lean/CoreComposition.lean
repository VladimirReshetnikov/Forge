/-
UNCOMPILED SPECIMEN. No Lean compiler was available during this study.
These logical composition lemmas are not reflected checker soundness theorems
and do not define a forge tactic. No kernel-acceptance claim is made.
-/
universe u v
namespace ForgeDelta

theorem liftWitness {α : Type u} {β : Type v}
    (D Q : α → Prop) (R : α → β → Prop) (w : α → β)
    (hDomain : ∀ x, D x → Q x)
    (hLift : ∀ x, Q x → R x (w x)) :
    ∀ x, D x → ∃ y, R x y := by
  intro x hx
  exact ⟨w x, hLift x (hDomain x hx)⟩

theorem combineContracts {α : Type u} {β : Type v}
    (D : α → Prop) (L A : α → β → Prop) (w : α → β)
    (hWitness : ∀ x, D x → L x (w x))
    (hExtra : ∀ x y, D x → L x y → A x y) :
    ∀ x, D x → ∃ y, L x y ∧ A x y := by
  intro x hx
  exact ⟨w x, hWitness x hx, hExtra x (w x) hx (hWitness x hx)⟩

end ForgeDelta
