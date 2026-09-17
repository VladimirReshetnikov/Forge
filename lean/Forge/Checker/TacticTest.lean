import Forge.Checker.Tactic
import Forge.Checker.Corpus
/-
  Tests for `forge_cone` and `forge_reify`.

  Positive tests close goals and have their axioms printed. Negative tests use
  `fail_if_success`: the tactic must fail. Where the negative goal is FALSE it is
  stated with the goal itself as a hypothesis `hfalse`, used only to discharge the
  `example` after `forge_cone` has been shown to fail (it is never passed to
  `forge_cone`).
-/
/- Negative tests take hypotheses that exist only to be passed to a tactic that
must fail, and `forge_reify` does not use the hypotheses it prints; the unused
variable linter would flag every one of them. -/
set_option linter.unusedVariables false

namespace Forge.Checker.TacticTest

open Forge.Checker

/-! ## 0. The bridge theorems themselves -/

#print axioms Forge.Checker.eval_toPoly
#print axioms Forge.Checker.cone_denote
#print axioms Forge.Checker.cone_denote_le

/-! ## 1. The three Corpus statements, verbatim, via the proved bridge

The Corpus certificates are over variables `x0, x1` in that order. In
`hidden_quadratic_concrete` the first atom scanned is `x1` (the term
`(-168) * x1` precedes `(-126) * x0`), so the atom order is fixed explicitly with
`(atoms := [x0, x1])`. The other two statements already scan `x0` before `x1`;
the `atoms` clause is given for the equality example anyway (its goal mentions
`x1` first), and omitted for `guard_product`. A reordered restatement of
`hidden_quadratic` without the clause is also proved. -/

theorem hidden_quadratic_concrete' (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

theorem hidden_quadratic_reordered (x0 x1 : Int)
    : 0 ≤ 147 + (-126) * x0 + (-168) * x1 + 99 * x1^2 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone using hidden_quadratic_cert

theorem equality_constrained_concrete' (x0 x1 : Int)
    (hf0 : (-1) + 1 * x1 + 1 * x0 = 0)
    : 0 ≤ (-1) + 2 * x1^2 + 2 * x0^2 := by
  forge_cone (atoms := [x0, x1]) [hf0] using equality_constrained_cert

theorem guard_product_concrete' (x0 x1 : Int)
    (hg0 : 0 ≤ 1 * x0)
    (hg1 : 0 ≤ 1 * x1)
    : 0 ≤ 1 * (x0 * x1) := by
  forge_cone [hg0, hg1] using guard_product_cert

#print axioms hidden_quadratic_concrete'
#print axioms hidden_quadratic_reordered
#print axioms equality_constrained_concrete'
#print axioms guard_product_concrete'

/-! ## 2. Monomials in three distinct variables

The class that broke the old generated bridge. Atom order `x, y, z`.
`q₁ = x*y*z + x` (monomials `[1,1,1]` and the short `[1]`) and
`q₂ = y*z - x` (`[0,1,1]`, `[1]`); target `q₁² + 3 q₂²`, stated expanded for `q₁`. -/

def three_var_cert : Cert where
  scale := 1
  squares := [
    { weight := 1, powers := [], poly := [([1, 1, 1], 1), ([1], 1)] },
    { weight := 3, powers := [], poly := [([0, 1, 1], 1), ([1], -1)] } ]
  multipliers := []

theorem three_var (x y z : Int) :
    0 ≤ x^2 * y^2 * z^2 + 2 * x^2 * y * z + x^2 + 3 * (y * z - x)^2 := by
  forge_cone using three_var_cert

/-- The same polynomial, fully expanded and in a different term order, with
`x` still scanned first, then `y`, then `z`. -/
theorem three_var_expanded (x y z : Int) :
    x^2 * y^2 * z^2 + x^2 + 2 * (x * (x * (y * z))) + 3 * (y*y*z*z) - 6 * (x*y*z) + 3 * x^2 ≥ 0 := by
  forge_cone using three_var_cert

#print axioms three_var
#print axioms three_var_expanded

/-! ## 3. Atoms that are terms, not variables -/

opaque f : Int → Int
opaque g : Int → Int → Int

/-- Atoms: `f a` (0), `g b c` (1). `(f a - g b c)^2`, expanded. -/
def opaque_cert : Cert where
  scale := 1
  squares := [ { weight := 1, powers := [], poly := [([1], 1), ([0, 1], -1)] } ]
  multipliers := []

theorem opaque_atoms (a b c : Int) :
    0 ≤ f a ^ 2 - 2 * (f a * g b c) + g b c * g b c := by
  forge_cone using opaque_cert

/-- A product inside a non-polynomial context is part of an atom: `f (a * b)`
is atom 0 and `a * b` is not reified inside it. Outside `f` the same `a * b` IS
reified, as the monomial over atoms `a` (1) and `b` (2).
Hypothesis `f (a * b) ≥ 0`. -/
def guarded_atom_cert : Cert where
  scale := 1
  squares := [ { weight := 2, powers := [1], poly := [([], 1)] },
               { weight := 1, powers := [0], poly := [([0, 1, 1], 1)] } ]
  multipliers := []

theorem opaque_guarded (a b : Int) (h : f (a * b) ≥ 0) :
    2 * f (a * b) + (a * b) ^ 2 ≥ 0 := by
  forge_cone [h] using guarded_atom_cert

/-- A non-literal exponent makes the power an atom; the atom `x ^ n` is
deduplicated across both occurrences. -/
def square_atom_cert : Cert where
  scale := 1
  squares := [ { weight := 1, powers := [], poly := [([1], 1)] } ]
  multipliers := []

theorem pow_atom (x : Int) (n : Nat) : 0 ≤ x ^ n * x ^ n := by
  forge_cone using square_atom_cert

#print axioms opaque_atoms
#print axioms opaque_guarded
#print axioms pow_atom

/-! ## 4. Hypotheses and goals in the supported forms -/

/-- Goal `a ≥ b` (certifies `x*y - x`), hypotheses `x ≥ 0` and `1 ≤ y`
(contributing `x` and `y - 1`). `x*y - x = x * (y - 1)`. -/
def ge_le_cert : Cert where
  scale := 1
  squares := [ { weight := 1, powers := [1, 1], poly := [([], 1)] } ]
  multipliers := []

theorem hyp_forms_ge_le (x y : Int) (hx : x ≥ 0) (hy : 1 ≤ y) : x * y ≥ x := by
  forge_cone [hx, hy] using ge_le_cert

/-- Goal `a ≤ b`: `2*x ≤ x^2 + 1`, certificate `(x - 1)^2`. -/
def amgm_cert : Cert where
  scale := 1
  squares := [ { weight := 1, powers := [], poly := [([1], 1), ([], -1)] } ]
  multipliers := []

theorem goal_le (x : Int) : 2 * x ≤ x^2 + 1 := by
  forge_cone using amgm_cert

/-- Equality `a = b` (contributes `x - y`): `x*y = x^2 + (-x)*(x - y)`. -/
def eq_ab_cert : Cert where
  scale := 1
  squares := [ { weight := 1, powers := [], poly := [([1], 1)] } ]
  multipliers := [ [([1], -1)] ]

theorem hyp_eq_ab (x y : Int) (h : x = y) : 0 ≤ x * y := by
  forge_cone [h] using eq_ab_cert

/-- Interleaved list: inequality `0 ≤ x`, equality `x - y = 0` (form `f = 0`),
inequality `x ≥ y` (form `a ≥ b`, contributing `x - y`), and scale 2.
Inequalities `[x, x - y]`, equalities `[x - y]`.
`2 * (x*y + x) = 2*x*x + 2*x + (-2*x)*(x - y)`, and `x*x = square`, `x = ineq 0`. -/
def mixed_cert : Cert where
  scale := 2
  squares := [ { weight := 2, powers := [0, 0], poly := [([1], 1)] },
               { weight := 2, powers := [1, 0], poly := [([], 1)] } ]
  multipliers := [ [([1], -2)] ]

theorem hyp_mixed (x y : Int) (h0 : 0 ≤ x) (he : x - y = 0) (h1 : x ≥ y) :
    x * y + x ≥ 0 := by
  forge_cone [h0, he, h1] using mixed_cert

/-- Order matters: `x` is the first constraint, `y` the second. -/
def first_guard_cert : Cert where
  scale := 1
  squares := [ { weight := 1, powers := [1, 0], poly := [([], 1)] } ]
  multipliers := []

theorem hyp_order_ok (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x := by
  forge_cone [hx, hy] using first_guard_cert

#print axioms hyp_forms_ge_le
#print axioms goal_le
#print axioms hyp_eq_ab
#print axioms hyp_mixed
#print axioms hyp_order_ok

/-! ## 5. `forge_reify` output

Keys are printed sorted. The goal `x ≤ x ^ 2 + 1` contributes `x^2 + 1 - x`;
atoms are `x` (goal) then `y` (first seen in `h`). -/

/-- `4 (x^2 - x + 1) = (2x - 1)^2 + 3`. -/
def reify_demo_cert : Cert where
  scale := 4
  squares := [ { weight := 1, powers := [], poly := [([1], 2), ([], -1)] },
               { weight := 3, powers := [], poly := [([], 1)] } ]
  multipliers := []

/-- info: {"atoms":["x","y"],"equalities":[{"n":2,"terms":[[[0,1],"-1"],[[1,0],"1"]]}],"inequalities":[{"n":2,"terms":[[[0,1],"1"]]}],"p":{"n":2,"terms":[[[1,0],"-1"],[[0,0],"1"],[[2,0],"1"]]}} -/
#guard_msgs in
theorem reify_demo (x y : Int) (h : 0 ≤ y) (e : x = y) : x ≤ x ^ 2 + 1 := by
  forge_reify [h, e]
  forge_cone using reify_demo_cert

#print axioms reify_demo

/-! ## 6. Negative tests: the tactic must FAIL

Each false goal is stated with itself as hypothesis `hfalse`, which is never
passed to `forge_cone`; it only discharges the `example` afterwards. -/

/-- (N1) A valid certificate for a different goal (`77` in place of `78`). -/
example (x0 x1 : Int)
    (hfalse : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 77 * x0^2) :
    0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 77 * x0^2 := by
  fail_if_success forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert
  exact hfalse

/-- (N1') The right certificate and polynomial, atoms in the wrong order (no
`atoms` clause, so `x1` is scanned first). -/
example (x0 x1 : Int) :
    0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone using hidden_quadratic_cert
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/-- (N2a) Mutated: one weight negated. -/
def neg_weight_cert : Cert :=
  { hidden_quadratic_cert with
    squares := hidden_quadratic_cert.squares.set 2
      { weight := -200, powers := [], poly := [([0, 1], 1)] } }

/-- (N2b) Mutated: one coefficient changed (`7` to `8` in the first square). -/
def bad_coeff_cert : Cert :=
  { hidden_quadratic_cert with
    squares := hidden_quadratic_cert.squares.set 0
      { weight := 153, powers := [], poly := [([0, 0], 8), ([0, 1], (-4)), ([1, 0], (-3))] } }

/-- (N2c) Mutated: scale changed. -/
def bad_scale_cert : Cert := { hidden_quadratic_cert with scale := 52 }

example (x0 x1 : Int) :
    0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone (atoms := [x0, x1]) using neg_weight_cert
  fail_if_success forge_cone (atoms := [x0, x1]) using bad_coeff_cert
  fail_if_success forge_cone (atoms := [x0, x1]) using bad_scale_cert
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/-- (N3) A FALSE goal, `0 ≤ -x^2 - 1`, with "almost right" certificates.
`-1 * (-x^2 - 1) = x^2 + 1` is an exact sum of squares, so the identity holds;
only the sign of the scale is wrong. -/
def almost_cert : Cert where
  scale := -1
  squares := [ { weight := 1, powers := [], poly := [([1], 1)] },
               { weight := 1, powers := [], poly := [([], 1)] } ]
  multipliers := []

/-- The same identity with scale `1` and NEGATIVE weights. -/
def almost_cert2 : Cert where
  scale := 1
  squares := [ { weight := -1, powers := [], poly := [([1], 1)] },
               { weight := -1, powers := [], poly := [([], 1)] } ]
  multipliers := []

/-- Scale `0` and no squares: `0 * p = 0` holds identically. -/
def zero_scale_cert : Cert where
  scale := 0
  squares := []
  multipliers := []

/-- A spurious equality multiplier with no equality constraint to pair it with
(`dot` would silently drop it if the length were not checked). -/
def extra_mult_cert : Cert where
  scale := 1
  squares := []
  multipliers := [ [([2], -1), ([], -1)] ]

example (x : Int) (hfalse : 0 ≤ -x^2 - 1) : 0 ≤ -x^2 - 1 := by
  fail_if_success forge_cone using almost_cert
  fail_if_success forge_cone using almost_cert2
  fail_if_success forge_cone using zero_scale_cert
  fail_if_success forge_cone using extra_mult_cert
  fail_if_success forge_cone using square_atom_cert
  exact hfalse

/-- (N3') A false goal whose negation is a hypothesis-shaped term: passing the
false statement's own "evidence" in the wrong list. `0 ≤ x - 1` does not follow
from `x ≥ 0`. -/
example (x : Int) (hx : x ≥ 0) (hfalse : 0 ≤ x - 1) : 0 ≤ x - 1 := by
  fail_if_success forge_cone [hx] using first_guard_cert
  fail_if_success forge_cone [hx] using eq_ab_cert
  exact hfalse

/-- (N4) A non-literal exponent: `x ^ (2 * n)` is an atom, so the certificate
for a square does not apply (the goal is true; the tactic cannot see why). -/
example (x : Int) (n : Nat) (htrue : 0 ≤ x ^ (2 * n)) : 0 ≤ x ^ (2 * n) := by
  fail_if_success forge_cone using square_atom_cert
  exact htrue

/-- (N4') A FALSE goal with a non-literal exponent: `0 ≤ x ^ n` fails at
`x = -1, n = 1`. -/
example (x : Int) (n : Nat) (hfalse : 0 ≤ x ^ n) : 0 ≤ x ^ n := by
  fail_if_success forge_cone using square_atom_cert
  exact hfalse

/-- (N5) Hypothesis list in the wrong order. With `[hy, hx]` the first constraint
is `y`, so `first_guard_cert` certifies `0 ≤ y`, not `0 ≤ x`. -/
example (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x := by
  fail_if_success forge_cone [hy, hx] using first_guard_cert
  fail_if_success forge_cone [hx] using first_guard_cert   -- wrong length
  forge_cone [hx, hy] using first_guard_cert

/-- (N5') An inequality where the certificate expects an equality, and a
reversed two-sided hypothesis (`x ≤ y` contributes `y - x`, not `x - y`). -/
example (x y : Int) (h0 : 0 ≤ x) (he : x - y = 0) (h1 : x ≥ y) (hle : x ≤ y) :
    x * y + x ≥ 0 := by
  fail_if_success forge_cone [h0, h1, h1] using mixed_cert
  fail_if_success forge_cone [hle, he, h1] using mixed_cert
  forge_cone [h0, he, h1] using mixed_cert

/-- NOT a failure: `[h0, h1, he]` is ACCEPTED, and correctly so. Inequalities and
equalities go to separate lists, each in its own relative order, so this is the
same problem as `[h0, he, h1]`. -/
example (x y : Int) (h0 : 0 ≤ x) (he : x - y = 0) (h1 : x ≥ y) : x * y + x ≥ 0 := by
  forge_cone [h0, h1, he] using mixed_cert

/- (N6) A NONSTANDARD multiplication. Under this instance `x * x` means `x + x`,
so `0 ≤ x * x` is FALSE at `x = -1`, while the polynomial `x^2` has a valid
certificate. The reifier sees a nonstandard instance and makes the product an
atom, so the certificate is rejected. -/
section FakeMul
local instance (priority := high) fakeMul : Mul Int := ⟨fun a b => a + b⟩

def fake_sq_cert : Cert where
  scale := 1
  squares := [ { weight := 1, powers := [], poly := [([1], 1)] } ]
  multipliers := []

example (x : Int) (hfalse : 0 ≤ x * x) : 0 ≤ x * x := by
  fail_if_success forge_cone using fake_sq_cert
  exact hfalse

/- (N6') The backstop, independent of the reifier: the proof term a reifier that
ignored instances WOULD build. The certificate check itself succeeds (`x^2` is a
square), but the term does not type-check against the goal, because
`denote (mul (atom 0) (atom 0))` is `Int.mul x x`, not the fake `x * x`. -/
example (x : Int) (hfalse : 0 ≤ x * x) : 0 ≤ x * x := by
  have hc : fake_sq_cert.check (IExpr.toPoly (.mul (.atom 0) (.atom 0)))
      (List.map IExpr.toPoly []) (List.map IExpr.toPoly []) = true := by decide
  fail_if_success exact (cone_denote fake_sq_cert (Env.ofList [x]) (.mul (.atom 0) (.atom 0)) [] [] hc trivial trivial)
  exact hfalse
end FakeMul

/-- (N7) Unsupported shapes fail instead of doing anything: a strict goal, an
equation goal, a strict hypothesis, a `Nat` goal. -/
example (x y : Int) (h : x < y) (hn : ∀ n : Nat, 0 ≤ n) : True := by
  have h1 : 0 < x * x + 1 := by
    fail_if_success forge_cone using square_atom_cert
    have : 0 ≤ x * x := by forge_cone using square_atom_cert
    omega
  have h2 : x * x = x ^ 2 := by
    fail_if_success forge_cone using square_atom_cert
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  have h3 : 0 ≤ x * x := by
    fail_if_success forge_cone [h] using square_atom_cert
    forge_cone using square_atom_cert
  have h4 : 0 ≤ (3 : Nat) := by
    fail_if_success forge_cone using square_atom_cert
    exact hn 3
  trivial

/-- (N8) Atom seeding cannot duplicate an atom, and a seed that is not in the
goal still takes its index. -/
example (x y : Int) (hfalse : 0 ≤ x * y) : 0 ≤ x * y := by
  fail_if_success forge_cone (atoms := [x, x]) using square_atom_cert
  fail_if_success forge_cone (atoms := [y, x]) using square_atom_cert
  exact hfalse

end Forge.Checker.TacticTest
