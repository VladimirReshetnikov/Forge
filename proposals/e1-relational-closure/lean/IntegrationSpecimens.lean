import Mathlib
/-
STATUS: NOT COMPILED. These are explicit integration targets, not an installed
Forge tactic or a claim of kernel acceptance. All mathematics is independently
covered by the JSON examples and the article's induction argument.
-/
set_option autoImplicit false
namespace ForgeRelationalClosure.Specimens

def slowStep (z u : ℚ) : ℚ := z * z + u

def fastStep (p : ℚ × ℚ) (u : ℚ) : ℚ × ℚ :=
  (p.2 + u, (p.2 + u) ^ 2)

/-- Relational induction, with the strengthened relation made explicit. -/
theorem nonlinear_fold_equivalence (xs : List ℚ) (t : ℚ) :
    xs.foldl slowStep t = (xs.foldl fastStep (t, t ^ 2)).1 := by
  have general : ∀ (ys : List ℚ) (z x y : ℚ), z = x → y = x ^ 2 →
      ys.foldl slowStep z = (ys.foldl fastStep (x, y)).1 := by
    intro ys
    induction ys with
    | nil =>
        intro z x y hz _
        exact hz
    | cons u us ih =>
        intro z x y hz hy
        change us.foldl slowStep (z * z + u) =
          (us.foldl fastStep (y + u, (y + u) ^ 2)).1
        apply ih
        · rw [hz, hy]
          ring
        · rfl
  exact general xs t t (t ^ 2) rfl rfl

/-- The discovered relation is stable, although its first component is not conserved. -/
theorem relational_transition_identity (z x y u : ℚ) :
    (z * z + u) - (y + u) =
      (z + x) * (z - x) + (x ^ 2 - y) := by
  ring

/-- Coupled invariant certificate in the explanatory two-generator basis. -/
theorem coupled_step_one (x y z u : ℚ) :
    ((x + u) ^ 2 + z - x ^ 3) - (x + u) ^ 2 = z - x ^ 3 := by
  ring

theorem coupled_step_two (x y z u : ℚ) :
    ((x + u) ^ 3 + (x + u + 1) * (y - x ^ 2)) - (x + u) ^ 3 =
      (x + u + 1) * (y - x ^ 2) := by
  ring

def badStep (p : ℚ × ℚ) (u : ℚ) : ℚ × ℚ :=
  (p.2 + u, (p.2 + u) ^ 2 + 1)

example : ([0, 0] : List ℚ).foldl slowStep 0 ≠
    (([0, 0] : List ℚ).foldl badStep (0, 0)).1 := by
  norm_num [slowStep, badStep, List.foldl]

end ForgeRelationalClosure.Specimens
