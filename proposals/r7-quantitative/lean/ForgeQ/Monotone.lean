import Lean

/-!
Candidate source, NOT compiler-validated in the authoring environment.
This module proves only an abstract finite-iteration principle. It is NOT
an implementation of a probability checker or a `forge` tactic.
-/
set_option autoImplicit false
namespace ForgeQ
universe u

def iterate {α : Type u} (step : α → α) (initial : α) : Nat → α
  | 0 => initial
  | n + 1 => step (iterate step initial n)

theorem iterate_preserves_bound {α : Type u} (R : α → α → Prop)
    (trans : ∀ {a b c : α}, R a b → R b c → R a c)
    (step : α → α) (mono : ∀ {a b : α}, R a b → R (step a) (step b))
    (initial bound : α) (base : R initial bound) (closed : R (step bound) bound) :
    ∀ n : Nat, R (iterate step initial n) bound := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact trans (mono ih) closed

#print axioms iterate_preserves_bound
end ForgeQ
