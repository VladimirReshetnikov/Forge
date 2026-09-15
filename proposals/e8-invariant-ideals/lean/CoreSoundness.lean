/-
Hand-written integration specimens. NOT COMPILED in the producing environment.
These generic induction theorems are not a certificate decoder or a forge tactic.
Target toolchain: leanprover/lean4:v4.34.0. No Mathlib import is intended here.
-/
import Lean
set_option autoImplicit false
set_option debug.skipKernelTC false

namespace ForgeExtensions

universe u v

inductive Reach {S : Type u} (initial : S → Prop) (step : S → S → Prop) : S → Prop
  | base {s : S} : initial s → Reach initial step s
  | advance {s t : S} : Reach initial step s → step s t → Reach initial step t

theorem reach_invariant {S : Type u} {initial : S → Prop} {step : S → S → Prop}
    {P : S → Prop}
    (base : ∀ s, initial s → P s)
    (closed : ∀ s t, P s → step s t → P t)
    {s : S} (h : Reach initial step s) : P s := by
  induction h with
  | base hi => exact base _ hi
  | advance _ hs ih => exact closed _ _ ih hs

inductive Tree (A : Type u) where
  | leaf : A → Tree A
  | node : Tree A → Tree A → Tree A

def treeFold {A : Type u} {Q : Type v} (leaf : A → Q) (node : Q → Q → Q) : Tree A → Q
  | .leaf a => leaf a
  | .node l r => node (treeFold leaf node l) (treeFold leaf node r)

theorem tree_cover {A : Type u} {Q : Type v}
    (leaf : A → Q) (node : Q → Q → Q) (R : Q → Prop)
    (base : ∀ a, R (leaf a))
    (closed : ∀ q r, R q → R r → R (node q r))
    (t : Tree A) : R (treeFold leaf node t) := by
  induction t with
  | leaf a => exact base a
  | node l r ihl ihr => exact closed _ _ ihl ihr

theorem tree_property {A : Type u} {Q : Type v}
    (leaf : A → Q) (node : Q → Q → Q) (R good : Q → Prop)
    (base : ∀ a, R (leaf a))
    (closed : ∀ q r, R q → R r → R (node q r))
    (safe : ∀ q, R q → good q)
    (t : Tree A) : good (treeFold leaf node t) := by
  exact safe _ (tree_cover leaf node R base closed t)

#print axioms ForgeExtensions.reach_invariant
#print axioms ForgeExtensions.tree_cover
#print axioms ForgeExtensions.tree_property

end ForgeExtensions
