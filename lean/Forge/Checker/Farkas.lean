import Forge.Checker.Affine
/-
  Forge.Checker.Farkas -- Farkas certificates of linear infeasibility, in core Lean.

  A system of constraints  a_i · x ≤ b_i  (i = 1..r) is refuted by multipliers
  λ_i ≥ 0 with  Σ λ_i a_i = 0  and  Σ λ_i b_i < 0: summing the constraints with
  those weights would give  0 ≤ Σ λ_i b_i < 0.

  PROVENANCE. This file was written against the textbook statement, before the
  prototype had a family of this shape. It now has one:
  prototype/forge/witness/farkas.py, whose `check_farkas` mirrors
  `FarkasCert.check`, and whose three bundle records are exported to
  `FarkasCorpus.lean` by tools/export_lean_farkas.py. (The prototype's older
  `check_witness` in witness/affine.py certifies an IMPLICATION, not
  infeasibility, and is still not exported.)

  PROVED. `FarkasCert.sound`: if the check passes, no integer vector x satisfies
  every constraint. (The certificate in fact refutes rational and real solutions
  too; that stronger statement needs an ordered field and is not stated here.)
  Farkas certificates are complete only for RATIONAL infeasibility: an integer-
  only obstruction such as 2x = 1 has no certificate of this kind.
-/

namespace Forge.Checker.Farkas
open Forge.Checker.Lin

/-- One constraint `coeffs · x ≤ bound`. -/
structure Constraint where
  coeffs : List Int
  bound : Int
  deriving Repr, DecidableEq

def Constraint.Holds (x : List Int) (r : Constraint) : Prop := dot r.coeffs x ≤ r.bound

/-- Nonnegative multipliers, one per constraint. -/
structure FarkasCert where
  mult : List Int
  deriving Repr, DecidableEq

/-- The checker, for `n` variables. -/
def FarkasCert.check (n : Nat) (rows : List Constraint) (cert : FarkasCert) : Bool :=
  rows.length == cert.mult.length
    && rows.all (·.coeffs.length == n)
    && cert.mult.all (fun l => decide (0 ≤ l))
    && comb n cert.mult (rows.map (·.coeffs)) == List.replicate n 0
    && decide (dot cert.mult (rows.map (·.bound)) < 0)

/-- Weighted sum of satisfied constraints. -/
theorem weighted_le (x : List Int) :
    ∀ (lam : List Int) (rows : List Constraint),
      (∀ l ∈ lam, 0 ≤ l) → (∀ r ∈ rows, r.Holds x) →
      dot lam (mulVec (rows.map (·.coeffs)) x) ≤ dot lam (rows.map (·.bound)) := by
  intro lam
  induction lam with
  | nil => intro rows _ _; simp
  | cons l lam ih =>
    intro rows hl hr
    cases rows with
    | nil => simp [mulVec]
    | cons r rows =>
      simp only [List.map_cons, mulVec_cons, dot_cons_cons]
      have h1 : l * dot r.coeffs x ≤ l * r.bound :=
        Int.mul_le_mul_of_nonneg_left (hr r (by simp)) (hl l (by simp))
      have h2 := ih rows (fun l' h => hl l' (by simp [h])) (fun r' h => hr r' (by simp [h]))
      exact Int.add_le_add h1 h2

/-- SOUNDNESS. A passing certificate means no integer point satisfies all rows. -/
theorem FarkasCert.sound (n : Nat) (rows : List Constraint) (cert : FarkasCert)
    (h : cert.check n rows = true) (x : List Int) : ¬ ∀ r ∈ rows, r.Holds x := by
  intro hx
  simp only [FarkasCert.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨_, hn⟩, hnn⟩, hcomb⟩, hneg⟩ := h
  have hW : ∀ w ∈ rows.map (·.coeffs), w.length = n := by
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    simpa using hn r hr
  have hle := weighted_le x cert.mult rows hnn hx
  rw [dot_mulVec n _ _ x hW, hcomb, dot_replicate_zero] at hle
  omega

/-! ## Tests: positive examples -/
section Tests

/-- `x ≤ -1` and `-x ≤ 0`. -/
def ex1 : List Constraint := [⟨[1], -1⟩, ⟨[-1], 0⟩]
def ex1_cert : FarkasCert := ⟨[1, 1]⟩
theorem ex1_checks : ex1_cert.check 1 ex1 = true := by decide
theorem ex1_concrete (x : Int) : ¬ (x ≤ -1 ∧ -x ≤ 0) := by
  intro ⟨h1, h2⟩
  apply FarkasCert.sound 1 ex1 ex1_cert ex1_checks [x]
  intro r hr
  simp [ex1] at hr
  rcases hr with rfl | rfl <;> simp [Constraint.Holds] <;> omega

/-- `x + y ≤ 1`, `-x ≤ -1`, `-y ≤ -1`. -/
def ex2 : List Constraint := [⟨[1, 1], 1⟩, ⟨[-1, 0], -1⟩, ⟨[0, -1], -1⟩]
def ex2_cert : FarkasCert := ⟨[1, 1, 1]⟩
theorem ex2_checks : ex2_cert.check 2 ex2 = true := by decide
theorem ex2_concrete (x y : Int) : ¬ (x + y ≤ 1 ∧ -x ≤ -1 ∧ -y ≤ -1) := by
  intro ⟨h1, h2, h3⟩
  apply FarkasCert.sound 2 ex2 ex2_cert ex2_checks [x, y]
  intro r hr
  simp [ex2] at hr
  rcases hr with rfl | rfl | rfl <;> simp [Constraint.Holds] <;> omega

/-- `2x - y ≤ 0`, `-x ≤ -3`, `y ≤ 5`, plus a redundant `x ≤ 100` with weight 0. -/
def ex3 : List Constraint := [⟨[2, -1], 0⟩, ⟨[-1, 0], -3⟩, ⟨[0, 1], 5⟩, ⟨[1, 0], 100⟩]
def ex3_cert : FarkasCert := ⟨[1, 2, 1, 0]⟩
theorem ex3_checks : ex3_cert.check 2 ex3 = true := by decide
theorem ex3_concrete (x y : Int) : ¬ (2 * x - y ≤ 0 ∧ -x ≤ -3 ∧ y ≤ 5 ∧ x ≤ 100) := by
  intro ⟨h1, h2, h3, h4⟩
  apply FarkasCert.sound 2 ex3 ex3_cert ex3_checks [x, y]
  intro r hr
  simp [ex3] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [Constraint.Holds] <;> omega

/-- Three variables, larger multipliers:
`x + 2y + 3z ≤ 4`, `-x ≤ 0`, `-y ≤ -1`, `-z ≤ -1`  (x + 2y + 3z ≥ 5 > 4). -/
def ex4 : List Constraint := [⟨[1, 2, 3], 4⟩, ⟨[-1, 0, 0], 0⟩, ⟨[0, -1, 0], -1⟩, ⟨[0, 0, -1], -1⟩]
def ex4_cert : FarkasCert := ⟨[1, 1, 2, 3]⟩
theorem ex4_checks : ex4_cert.check 3 ex4 = true := by decide
theorem ex4_concrete (x y z : Int) :
    ¬ (x + 2 * y + 3 * z ≤ 4 ∧ -x ≤ 0 ∧ -y ≤ -1 ∧ -z ≤ -1) := by
  intro ⟨h1, h2, h3, h4⟩
  apply FarkasCert.sound 3 ex4 ex4_cert ex4_checks [x, y, z]
  intro r hr
  simp [ex4] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [Constraint.Holds] <;> omega

/-! ## Tests: negative controls, one per conjunct -/

/-- NONNEGATIVITY. `x ≤ -1`, `x ≤ 0` with multipliers `[1, -1]`: the combination
is zero and the bound sum is `-1 < 0`, so ONLY the sign test fails -- and the
system is feasible, so dropping that test would be unsound. -/
def neg_sign : List Constraint := [⟨[1], -1⟩, ⟨[1], 0⟩]
theorem neg_sign_rejected : (FarkasCert.mk [1, -1]).check 1 neg_sign = false := by decide
theorem neg_sign_feasible : ∀ r ∈ neg_sign, r.Holds [-5] := by
  intro r hr; simp [neg_sign] at hr
  rcases hr with rfl | rfl <;> simp [Constraint.Holds]

/-- STRICTNESS. `x ≤ 0`, `-x ≤ 0` with `[1, 1]`: combination zero, bound sum `0`,
not `< 0`. Feasible at `x = 0`. -/
def neg_strict : List Constraint := [⟨[1], 0⟩, ⟨[-1], 0⟩]
theorem neg_strict_rejected : (FarkasCert.mk [1, 1]).check 1 neg_strict = false := by decide
theorem neg_strict_feasible : ∀ r ∈ neg_strict, r.Holds [0] := by
  intro r hr; simp [neg_strict] at hr
  rcases hr with rfl | rfl <;> simp [Constraint.Holds]

/-- ZERO COMBINATION. `ex1` with `[1, 2]`: nonnegative, bound sum `-1 < 0`, but
`1·1 + 2·(-1) ≠ 0`. -/
theorem neg_comb_rejected : (FarkasCert.mk [1, 2]).check 1 ex1 = false := by decide

/-- ARITY. `ex1`'s valid certificate with an extra multiplier. -/
theorem neg_arity_rejected : (FarkasCert.mk [1, 1, 0]).check 1 ex1 = false := by decide

/-- ROW WIDTH. Two variables, but the second row has a third coefficient. The
truncating combination is still `[0, 0]` and the bound sum is `-1`, so ONLY the
width test fails. -/
def neg_width : List Constraint := [⟨[1, 0], -1⟩, ⟨[-1, 0, 5], 0⟩]
theorem neg_width_rejected : ex1_cert.check 2 neg_width = false := by decide
/-- The width test is the conjunct that fires: the others all pass. -/
theorem neg_width_only_width :
    comb 2 ex1_cert.mult (neg_width.map (·.coeffs)) = [0, 0]
      ∧ dot ex1_cert.mult (neg_width.map (·.bound)) = -1 := by decide

/-- ALL-ZERO MULTIPLIERS. On a system that IS infeasible (`0 <= -1` and `x <= 0`),
`[0, 0]` combines to `0 <= 0`: no contradiction, so no certificate. The genuine
certificate `[1, 0]` is accepted. Both were observed in review; pinned here. -/
def neg_zero : List Constraint := [⟨[0], -1⟩, ⟨[1], 0⟩]
theorem neg_zero_rejected : (FarkasCert.mk [0, 0]).check 1 neg_zero = false := by decide
theorem neg_zero_genuine_accepted : (FarkasCert.mk [1, 0]).check 1 neg_zero = true := by decide

/-- EMPTY SYSTEM. With no constraints every point is feasible, so nothing can
certify infeasibility -- at any arity. -/
theorem neg_empty_rejected_0 : (FarkasCert.mk []).check 0 [] = false := by decide
theorem neg_empty_rejected_2 : (FarkasCert.mk []).check 2 [] = false := by decide

end Tests

#print axioms FarkasCert.sound
#print axioms weighted_le
#print axioms ex1_concrete
#print axioms ex2_concrete
#print axioms ex3_concrete
#print axioms ex4_concrete
#print axioms neg_sign_rejected
#print axioms neg_sign_feasible
#print axioms neg_strict_rejected
#print axioms neg_width_rejected

end Forge.Checker.Farkas
