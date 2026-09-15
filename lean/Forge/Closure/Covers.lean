/-
  Forge: finite-algebra covers for inductive data.

  PROVENANCE: e8-invariant-ideals/lean/CoreSoundness.lean, its tree half.
  The `Reach` inductive that file also carried is merged into
  Forge/Closure/Principles.lean, where five other proposals wrote the same
  theorem.

  STATUS: elaborates against leanprover/lean4:v4.34.0 with no axiom
  dependencies. It is not a certificate decoder and not a `forge` tactic.

  What `tree_property` does and does not give you. It discharges the goal for
  the SUPPLIED algebra: `leaf`, `node`, `R` and `good` are whatever the caller
  provides. Connecting it to a source datatype needs a proved compatibility
  theorem per constructor, and the certificate establishes the property it
  encodes -- a congruence, say -- not the integer equality that may have
  motivated the choice of states.
-/
import Lean
set_option autoImplicit false

namespace ForgeClosure

universe u v

inductive Tree (A : Type u) where
  | leaf : A → Tree A
  | node : Tree A → Tree A → Tree A

def treeFold {A : Type u} {Q : Type v} (leaf : A → Q) (node : Q → Q → Q) : Tree A → Q
  | .leaf a => leaf a
  | .node l r => node (treeFold leaf node l) (treeFold leaf node r)

/--
  An inductive cover: `R` holds of every nullary summary and is closed under
  every constructor. The positive certificate is just the list of states in
  `R`; this theorem is what that list buys.
-/
theorem tree_cover {A : Type u} {Q : Type v}
    (leaf : A → Q) (node : Q → Q → Q) (R : Q → Prop)
    (base : ∀ a, R (leaf a))
    (closed : ∀ q r, R q → R r → R (node q r))
    (t : Tree A) : R (treeFold leaf node t) := by
  induction t with
  | leaf a => exact base a
  | node l r ihl ihr => exact closed _ _ ihl ihr

/-- A cover inside the good set settles the goal for every finite tree. -/
theorem tree_property {A : Type u} {Q : Type v}
    (leaf : A → Q) (node : Q → Q → Q) (R good : Q → Prop)
    (base : ∀ a, R (leaf a))
    (closed : ∀ q r, R q → R r → R (node q r))
    (safe : ∀ q, R q → good q)
    (t : Tree A) : good (treeFold leaf node t) :=
  safe _ (tree_cover leaf node R base closed t)

#print axioms ForgeClosure.tree_cover
#print axioms ForgeClosure.tree_property

end ForgeClosure
