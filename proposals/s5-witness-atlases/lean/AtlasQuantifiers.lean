/-
UNCOMPILED SPECIMEN. No Lean executable was available for this delivery.
These are semantic composition lemmas, NOT a real-algebraic checker.
The cover and local witness/counterexample hypotheses contain the hard work.
-/
import Lean
set_option autoImplicit false
namespace ForgeAtlasSpec
universe u v w

theorem forall_exists_of_cell_witnesses
    {X : Type u} {Y : Type v} {Cell : Type w}
    (member : Cell → X → Prop) (F : X → Y → Prop)
    (cover : ∀ x, ∃ c, member c x)
    (witness : Cell → X → Y)
    (correct : ∀ c x, member c x → F x (witness c x)) :
    ∀ x, ∃ y, F x y :=
  fun x => Exists.elim (cover x)
    (fun c hc => Exists.intro (witness c x) (correct c x hc))

theorem not_exists_forall_of_cell_counterexamples
    {X : Type u} {Y : Type v} {Cell : Type w}
    (member : Cell → X → Prop) (F : X → Y → Prop)
    (cover : ∀ x, ∃ c, member c x)
    (counterexample : Cell → X → Y)
    (incorrect : ∀ c x, member c x → ¬ F x (counterexample c x)) :
    ¬ (∃ x, ∀ y, F x y) :=
  fun h => Exists.elim h (fun x hx =>
    Exists.elim (cover x) (fun c hc =>
      incorrect c x hc (hx (counterexample c x))))

#print axioms ForgeAtlasSpec.forall_exists_of_cell_witnesses
#print axioms ForgeAtlasSpec.not_exists_forall_of_cell_counterexamples
end ForgeAtlasSpec
