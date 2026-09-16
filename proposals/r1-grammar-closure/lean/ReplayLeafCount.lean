/-
  STATUS: NOT_RUN. No Lean/lake executable was available for this package.
  This is a hand-written integration specimen, not generated/compiled evidence.

  Install in a Mathlib project whose import path also includes Forge's existing
  lean/Forge/Closure/Covers.lean, pinned in docs/SOURCES.md.
  It REUSES tree_property rather than re-proving the existing induction rule.

  The coefficients below are the bilinear extension of the five identities in
  results/fixtures/tree_identity.certificate.json. There are no sorry commands,
  axioms, native_decide calls, or unchecked certificate assertions in this file.
  Their textual absence is not an axiom audit or a compilation result.
-/
import Mathlib
import Forge.Closure.Covers

set_option autoImplicit false

namespace ForgeGrammarReplay

abbrev V := ℚ × ℚ × ℚ

def rep (a b : ℚ) : V := (a + b, a + 2 * b, b)

def node (x y : V) : V :=
  (x.1 * y.1,
   x.2.1 * y.1 + x.1 * y.2.1,
   x.2.2 * y.1 + x.1 * y.2.2 + x.1 * y.1)

def cover (v : V) : Prop := ∃ a b : ℚ, v = rep a b

def observe (v : V) : ℚ := v.2.1 - v.2.2 - v.1

-- These are the collected tensor coefficients, not a guessed invariant step.
theorem node_rep (a b c d : ℚ) :
    node (rep a b) (rep c d) =
      rep (-a * d - b * c - 2 * b * d)
          (a * c + 2 * a * d + 2 * b * c + 3 * b * d) := by
  apply Prod.ext
  · dsimp [node, rep]
    ring
  · apply Prod.ext
    · dsimp [node, rep]
      ring
    · dsimp [node, rep]
      ring

theorem leaf_base : cover ((1, 1, 0) : V) := by
  refine ⟨1, 0, ?_⟩
  norm_num [rep]

theorem node_closed (x y : V) (hx : cover x) (hy : cover y) : cover (node x y) := by
  rcases hx with ⟨a, b, rfl⟩
  rcases hy with ⟨c, d, rfl⟩
  exact ⟨-a * d - b * c - 2 * b * d,
    a * c + 2 * a * d + 2 * b * c + 3 * b * d, node_rep a b c d⟩

theorem cover_zero (v : V) (h : cover v) : observe v = 0 := by
  rcases h with ⟨a, b, rfl⟩
  dsimp [observe, rep]
  ring

theorem all_tree_counts (t : ForgeClosure.Tree Unit) :
    observe (ForgeClosure.treeFold (fun (_ : Unit) => ((1, 1, 0) : V)) node t) = 0 :=
  ForgeClosure.tree_property
    (fun (_ : Unit) => ((1, 1, 0) : V)) node cover
    (fun v => observe v = 0)
    (fun _ => leaf_base) node_closed cover_zero t

#print axioms ForgeGrammarReplay.node_rep
#print axioms ForgeGrammarReplay.all_tree_counts

end ForgeGrammarReplay
