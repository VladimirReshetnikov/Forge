import Forge.Checker.Oracle
import Forge.Checker.Corpus
/-
  Tests for `forge_cone?`, the oracle protocol.

  REQUIREMENTS. `python` on PATH with NumPy and SciPy (the prototype's cone
  search imports them), and the working directory `lean/` or the repository
  root, so that `tools/forge_oracle.py` and `tools/test_oracles/fake_oracle.py`
  resolve. The oracle is called at ELABORATION time; the resulting declarations
  do not depend on it (see `#print axioms`, and section 2, where the suggested
  oracle-free proofs are replayed with `forge_cone` alone).

  SECTIONS.
  1. End to end: `forge_cone?` with the real oracle on the three Corpus goals and
     new goals. `forge.oracle.reportTime` is on, so the build log records the
     wall-clock time of each oracle call and of the kernel-checked closing step.
  2. The "Try this" output pinned once, and the suggested proofs replayed without
     the oracle.
  3. Mutation rejection AT THE DATA BOUNDARY: `forge.oracle.cmd` points at
     `tools/test_oracles/fake_oracle.py MODE`, which runs the real search and
     corrupts its answer. Every goal in this section is TRUE, and each example
     closes it afterwards with the honest certificate -- so the only thing that
     makes `forge_cone?` fail is the data. Each case is checked twice: with
     `fail_if_success` (it fails), and with `fails_with "…"` (it fails for the
     stated reason, so a rejection for an unrelated cause would not pass).
-/
set_option linter.unusedVariables false

namespace Forge.Checker.OracleTest

open Lean Elab Tactic
open Forge.Checker

/-- `fails_with "s" tac`: `tac` must FAIL, and its error message must contain
`s`. The goal is left unchanged. -/
elab "fails_with " s:str " => " t:tactic : tactic => do
  let st ← saveState
  let outcome ← try
      evalTactic t
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  st.restore
  match outcome with
  | none => throwError "fails_with: the tactic SUCCEEDED; it was expected to fail with \"{s.getString}\""
  | some msg =>
    unless (msg.splitOn s.getString).length > 1 do
      throwError "fails_with: the tactic failed, but its message does not contain \
        \"{s.getString}\":\n{msg}"

/-! ## 1. End to end with the real oracle -/

section EndToEnd
set_option forge.oracle.reportTime true

/-- Corpus `hidden_quadratic`, verbatim. The Corpus certificate is in atom order
`x0, x1`; the oracle needs no such pin, but the clause is kept so the suggested
`forge_cone` matches the one in TacticTest. -/
theorem e2e_hidden_quadratic (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone? (atoms := [x0, x1])

/-- The same goal WITHOUT the atom clause: the oracle solves the problem in
whatever order the reifier produced, so the Corpus pin is unnecessary here. -/
theorem e2e_hidden_quadratic_unpinned (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone?

/-- Corpus `equality_constrained`, verbatim. -/
theorem e2e_equality_constrained (x0 x1 : Int)
    (hf0 : (-1) + 1 * x1 + 1 * x0 = 0)
    : 0 ≤ (-1) + 2 * x1^2 + 2 * x0^2 := by
  forge_cone? [hf0]

/-- Corpus `guard_product`, verbatim. -/
theorem e2e_guard_product (x0 x1 : Int)
    (hg0 : 0 ≤ 1 * x0)
    (hg1 : 0 ≤ 1 * x1)
    : 0 ≤ 1 * (x0 * x1) := by
  forge_cone? [hg0, hg1]

/-- New: a goal of the form `a ≤ b`. -/
theorem e2e_amgm (x y : Int) : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  forge_cone?

/-- New: three variables, three guards, a sum of guard products. -/
theorem e2e_three_guards (x y z : Int) (hx : 0 ≤ x) (hy : y ≥ 0) (hz : 0 ≤ z) :
    0 ≤ x * y + y * z + z * x := by
  forge_cone? [hx, hy, hz]

/-- New: atoms that are terms, and a goal of the form `a ≥ b`. -/
opaque f : Int → Int
opaque g : Int → Int → Int

theorem e2e_opaque (a b c : Int) : f a ^ 2 + g b c * g b c ≥ 2 * (f a * g b c) := by
  forge_cone?

/-- New: an equality `a = b` and an inequality `a ≤ b` mixed. -/
theorem e2e_mixed (x y : Int) (h : x = y) (hx : 1 ≤ x) : 0 ≤ x * y - 1 := by
  forge_cone? [h, hx]

/-- New: degree four, found by the dictionary search, not by `quadratic_sos`. -/
theorem e2e_quartic (x y : Int) : 0 ≤ x ^ 4 + y ^ 4 - 2 * (x ^ 2 * y ^ 2) := by
  forge_cone?

/-- New: no atoms at all. -/
theorem e2e_constant : (0 : Int) ≤ 5 := by
  forge_cone?

end EndToEnd

#print axioms e2e_hidden_quadratic
#print axioms e2e_hidden_quadratic_unpinned
#print axioms e2e_equality_constrained
#print axioms e2e_guard_product
#print axioms e2e_amgm
#print axioms e2e_three_guards
#print axioms e2e_opaque
#print axioms e2e_mixed
#print axioms e2e_quartic
#print axioms e2e_constant

/-! ### A goal the oracle cannot certify: the tactic fails, it does not admit -/

example (x : Int) (hfalse : 0 ≤ -x ^ 2 - 1) : 0 ≤ -x ^ 2 - 1 := by
  fail_if_success forge_cone?
  fails_with "returned status `unknown`" => forge_cone?
  exact hfalse

/-- A TRUE goal outside the search's reach (odd degree, needs a real argument):
still `unknown`, still a failure. -/
example (x : Int) (hx : 0 ≤ x) (hfalse : 0 ≤ x ^ 3) : 0 ≤ x ^ 3 := by
  fails_with "forge_cone?" => forge_cone?
  exact hfalse

/-- An input the oracle refuses by its own bounds (more than 6 variables). -/
example (a b c d e f' g' : Int) (h : 0 ≤ a*a + b*b + c*c + d*d + e*e + f'*f' + g'*g') :
    0 ≤ a*a + b*b + c*c + d*d + e*e + f'*f' + g'*g' := by
  fails_with "returned status `error`" => forge_cone?
  exact h

/-! ## 2. The suggestion, pinned, and the suggested proofs replayed -/

/--
info: Try this:
  [apply] forge_cone (atoms := [x0, x1]) using
    { scale := 51,
      squares :=
        [{ weight := 153, powers := [], poly := [([0, 0], 7), ([0, 1], (-4)), ([1, 0], (-3))] },
          { weight := 1, powers := [], poly := [([0, 1], (-49)), ([1, 0], 51)] },
          { weight := 200, powers := [], poly := [([0, 1], 1)] }],
      multipliers := [] }
-/
#guard_msgs in
theorem pinned_hidden_quadratic (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone? (atoms := [x0, x1])

/-! The ten suggestions the oracle produced in section 1, replayed verbatim with
`forge_cone` alone. No Python, no IO: if any suggestion were not a valid proof,
this section would fail to compile. -/

section Replay

theorem replay_hidden_quadratic (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone (atoms := [x0, x1]) using
    { scale := 51,
      squares :=
        [{ weight := 153, powers := [], poly := [([0, 0], 7), ([0, 1], (-4)), ([1, 0], (-3))] },
          { weight := 1, powers := [], poly := [([0, 1], (-49)), ([1, 0], 51)] },
          { weight := 200, powers := [], poly := [([0, 1], 1)] }],
      multipliers := [] }

theorem replay_hidden_quadratic_unpinned (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone using
    { scale := 51,
      squares :=
        [{ weight := 153, powers := [], poly := [([0, 0], 7), ([0, 1], (-3)), ([1, 0], (-4))] },
          { weight := 1, powers := [], poly := [([0, 1], (-49)), ([1, 0], 51)] },
          { weight := 200, powers := [], poly := [([0, 1], 1)] }],
      multipliers := [] }

theorem replay_equality_constrained (x0 x1 : Int)
    (hf0 : (-1) + 1 * x1 + 1 * x0 = 0)
    : 0 ≤ (-1) + 2 * x1^2 + 2 * x0^2 := by
  forge_cone [hf0] using
    { scale := 1, squares := [{ weight := 1, powers := [], poly := [([0, 1], 1), ([1, 0], (-1))] }],
      multipliers := [[([0, 0], 1), ([0, 1], 1), ([1, 0], 1)]] }

theorem replay_guard_product (x0 x1 : Int)
    (hg0 : 0 ≤ 1 * x0)
    (hg1 : 0 ≤ 1 * x1)
    : 0 ≤ 1 * (x0 * x1) := by
  forge_cone [hg0, hg1] using
    { scale := 1, squares := [{ weight := 1, powers := [1, 1], poly := [([0, 0], 1)] }], multipliers := [] }

theorem replay_amgm (x y : Int) : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  forge_cone using
    { scale := 1, squares := [{ weight := 1, powers := [], poly := [([0, 1], (-1)), ([1, 0], 1)] }], multipliers := [] }

theorem replay_three_guards (x y z : Int) (hx : 0 ≤ x) (hy : y ≥ 0) (hz : 0 ≤ z) :
    0 ≤ x * y + y * z + z * x := by
  forge_cone [hx, hy, hz] using
    { scale := 1,
      squares :=
        [{ weight := 1, powers := [1, 1, 0], poly := [([0, 0, 0], 1)] },
          { weight := 1, powers := [1, 0, 1], poly := [([0, 0, 0], 1)] },
          { weight := 1, powers := [0, 1, 1], poly := [([0, 0, 0], 1)] }],
      multipliers := [] }

theorem replay_opaque (a b c : Int) : f a ^ 2 + g b c * g b c ≥ 2 * (f a * g b c) := by
  forge_cone using
    { scale := 1, squares := [{ weight := 1, powers := [], poly := [([0, 1], (-1)), ([1, 0], 1)] }], multipliers := [] }

theorem replay_mixed (x y : Int) (h : x = y) (hx : 1 ≤ x) : 0 ≤ x * y - 1 := by
  forge_cone [h, hx] using
    { scale := 1,
      squares :=
        [{ weight := 2, powers := [1], poly := [([0, 0], 1)] }, { weight := 1, powers := [2], poly := [([0, 0], 1)] }],
      multipliers := [[([1, 0], (-1))]] }

theorem replay_quartic (x y : Int) : 0 ≤ x ^ 4 + y ^ 4 - 2 * (x ^ 2 * y ^ 2) := by
  forge_cone using
    { scale := 1, squares := [{ weight := 1, powers := [], poly := [([0, 2], 1), ([2, 0], (-1))] }], multipliers := [] }

theorem replay_constant : (0 : Int) ≤ 5 := by
  forge_cone using
    { scale := 1, squares := [{ weight := 5, powers := [], poly := [([], 1)] }], multipliers := [] }

end Replay

#print axioms replay_hidden_quadratic
#print axioms replay_hidden_quadratic_unpinned
#print axioms replay_equality_constrained
#print axioms replay_guard_product
#print axioms replay_amgm
#print axioms replay_three_guards
#print axioms replay_opaque
#print axioms replay_mixed
#print axioms replay_quartic
#print axioms replay_constant

/-! ## 3. Mutation rejection at the data boundary

Fixtures: three TRUE goals, each with its honest closing proof. -/

section Mutations

/- (a) A negated weight. It decodes (a negative integer is well-typed data);
`Cert.check` rejects it under `decide`. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py negweight" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "DECODED but was REJECTED" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- Positive control for the harness: the fake oracle in `identity` mode passes
the real answer through, and the tactic succeeds. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py identity" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone? (atoms := [x0, x1])

/- (b) A wrong multiplier: one coefficient off by one. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py wrongmult" in
example (x0 x1 : Int) (hf0 : (-1) + 1 * x1 + 1 * x0 = 0) : 0 ≤ (-1) + 2 * x1^2 + 2 * x0^2 := by
  fail_if_success forge_cone? [hf0]
  fails_with "DECODED but was REJECTED" => forge_cone? [hf0]
  forge_cone (atoms := [x0, x1]) [hf0] using equality_constrained_cert

/- (b') One multiplier too many. Rejected by the decoder's arity check. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py extramult" in
example (x0 x1 : Int) (hf0 : (-1) + 1 * x1 + 1 * x0 = 0) : 0 ≤ (-1) + 2 * x1^2 + 2 * x0^2 := by
  fail_if_success forge_cone? [hf0]
  fails_with "reply.multipliers: more than 1 elements" => forge_cone? [hf0]
  forge_cone (atoms := [x0, x1]) [hf0] using equality_constrained_cert

/- (b'') A dropped square: well-formed, wrong identity. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py dropsquare" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "DECODED but was REJECTED" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (c) Truncated JSON. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py truncated" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "not a single well-formed JSON value" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (c') Not JSON at all; (c'') no output; (c''') two JSON values. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py garbage" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "MALFORMED oracle reply" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py empty" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "not a single well-formed JSON value" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py two" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "not a single well-formed JSON value" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

/- (d) A non-integer coefficient `1.5`. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py float" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "character '.'" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (d') An integral value in float syntax, `51.0`: still not an integer token. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py float_integral" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "character '.'" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (d'') A coefficient as a string `"7"`. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py string_coeff" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "coefficient: expected an integer" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (d''') A boolean weight `true`. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py bool" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "character 't'" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (e) A valid certificate for a DIFFERENT problem (the target plus one). It
decodes and is internally consistent; it is not a certificate for this goal. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py otherproblem" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "DECODED but was REJECTED" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py otherproblem" in
example (x0 x1 : Int) (hg0 : 0 ≤ 1 * x0) (hg1 : 0 ≤ 1 * x1) : 0 ≤ 1 * (x0 * x1) := by
  fail_if_success forge_cone? [hg0, hg1]
  fails_with "DECODED but was REJECTED" => forge_cone? [hg0, hg1]
  forge_cone [hg0, hg1] using guard_product_cert

/- (f) An extra top-level field. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py extrafield" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "reply: expected exactly the fields" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (f') An extra field inside a square. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py extrasquarefield" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "reply.squares[0]: expected exactly the fields" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (f'') A missing top-level field. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py missingfield" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "reply: expected exactly the fields" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (f''') A missing field inside a polynomial. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py missingpolyn" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "reply.squares[0].poly: expected exactly the fields" =>
    forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (f'''') A duplicated key whose LAST value is the valid one (the core JSON
parser keeps the last value; the colon count catches it). -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py dupkey" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "duplicate object key" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (f''''') The right field with the wrong type (`null`). -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py nullfield" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "character 'n'" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (g) An enormous integer, 10^200: beyond the digit bound. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py bigint" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "more than 100 digits" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (g') `1e999999999`: an exponent the core parser would expand before any
bound applied. The prescan rejects it first. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py exponent" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "character 'e'" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (g'') 10^99: inside the bound, so it decodes, and the check rejects it. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py bigint_inbounds" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "DECODED but was REJECTED" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (g''') Valid JSON padded past 1 MB: rejected for size alone. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py oversized" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "wrote more than 1000000 bytes" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- (g'''') Output that never ends: killed at the byte cap, not waited on. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py flood" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "wrote more than 1000000 bytes" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

/-! ### Other boundary violations -/

/- A monomial arity that disagrees with the number of atoms. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py wrongn" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "expected 2 (the number of atoms), got 3" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- A `powers` list longer than the inequality list. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py powerslen" in
example (x0 x1 : Int) (hg0 : 0 ≤ 1 * x0) (hg1 : 0 ≤ 1 * x1) : 0 ≤ 1 * (x0 * x1) := by
  fail_if_success forge_cone? [hg0, hg1]
  fails_with "powers: more than 2 elements" => forge_cone? [hg0, hg1]
  forge_cone [hg0, hg1] using guard_product_cert

/- A negative exponent. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py negpower" in
example (x0 x1 : Int) (hg0 : 0 ≤ 1 * x0) (hg1 : 0 ≤ 1 * x1) : 0 ≤ 1 * (x0 * x1) := by
  fail_if_success forge_cone? [hg0, hg1]
  fails_with "expected a nonnegative integer, got -1" => forge_cone? [hg0, hg1]
  forge_cone [hg0, hg1] using guard_product_cert

/- Scale zero: decodes, fails `0 < scale` in the check. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py scale0" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "DECODED but was REJECTED" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- A correct certificate, but a nonzero exit code. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py exit1" in
example (x0 x1 : Int)
    : 0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  fail_if_success forge_cone? (atoms := [x0, x1])
  fails_with "exited with code 1" => forge_cone? (atoms := [x0, x1])
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert

/- A declining oracle, and a status outside the protocol. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py unknown" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "fake oracle declines" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py badstatus" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "reply.status: expected" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

/- A hung oracle: killed at the time limit. -/
set_option forge.oracle.timeoutMs 3000 in
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py sleep" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "did not finish within 3000 ms" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

/- A command that does not exist. -/
set_option forge.oracle.cmd "forge_no_such_oracle_program_xyz" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "could not run the oracle command" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

/- (R1, size, at the data boundary) A VALID certificate padded with a zero-weight
45-term square. The identity still holds, so a checker with no size limit would
accept it; the decoder must refuse it BEFORE checking, and say it is a resource
limit and not a verdict. -/
set_option forge.oracle.cmd "python tools/test_oracles/fake_oracle.py oversize_valid" in
example (x : Int) : 0 ≤ x ^ 2 := by
  fail_if_success forge_cone?
  fails_with "MEASURED to check" => forge_cone?
  forge_cone using ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1)] }], multipliers := [] } : Cert)

end Mutations

end Forge.Checker.OracleTest
