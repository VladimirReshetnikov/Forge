import Forge.Checker.Cone
/-
  Checked certificate checkers for the recurrence family: additive polynomial
  recurrences and conserved polynomial invariants of polynomial transition maps.

  CORE LEAN ONLY, like `Poly.lean` and `Cone.lean`. Coefficients are integers;
  the exporter clears denominators and every statement below carries the
  positive scale it used explicitly.

  WHAT THE PYTHON CHECKERS ESTABLISH (prototype/forge/recurrence.py and
  prototype/forge/certificates.py), and what is proved here.

  1. `check_recurrence(step, initial, formula)`. Variables are `(n, a1..ak)`;
     `initial` must not mention `n`. The checker verifies the two polynomial
     identities
         formula(0, a)                    = initial(a)
         formula(n+1, a) - formula(n, a)  = step(n, a).
     Mathematically: the sequence F defined by F(0,a) = initial(a) and
     F(n+1,a) = F(n,a) + step(n,a) satisfies F(n,a) = formula(n,a) for every
     natural n. So F(n,a) = initial(a) + sum_{i<n} step(i,a); the step at index
     i is added when passing from i to i+1 (the sum is over i < n, NOT i <= n).

     Here: `RecCert.check` verifies, for an integer `scale > 0` and an integer
     polynomial `formula`,
         formula(0, a)                    = scale * initial(a)
         formula(n+1, a) - formula(n, a)  = scale * step(n, a)
     and `RecCert.sound` proves  scale * recSeq step initial a n = formula(n, a)
     for every `n : Nat` and every integer assignment `a` of the parameters.

  2. `check_invariant(InvariantCertificate(I, s0, T))`. Verifies I(s0) = 0 (a
     rational point) and the polynomial identity I(T(s)) = I(s). Mathematically:
     I vanishes at T^k(s0) for every k, i.e. on the whole forward orbit of s0.

     Here: `InvCert.check` verifies I(s0) = 0 and I o T = I as a polynomial
     identity, for an integer I (= scale * the rational invariant, scale > 0),
     and `InvCert.sound` proves I vanishes at every state `Reachable` from s0,
     where `Reachable` is the inductive closure of {s0} under T.
-/
namespace Forge.Checker

/-! ### Frame lemmas -/

/-- `monoEvalFrom x i m` only reads variables `j >= i`. -/
theorem monoEvalFrom_congr (x y : Env) :
    ∀ (i : Nat) (m : Mono), (∀ j, i ≤ j → x j = y j) →
      monoEvalFrom x i m = monoEvalFrom y i m
  | _, [], _ => rfl
  | i, e :: es, h => by
    simp only [monoEvalFrom]
    rw [h i (Nat.le_refl i),
      monoEvalFrom_congr x y (i + 1) es (fun j hj => h j (by omega))]

/-- Overwrite variable `0`. -/
def setVar0 (x : Env) (v : Int) : Env := fun i => if i = 0 then v else x i

theorem setVar0_setVar0 (x : Env) (u v : Int) : setVar0 (setVar0 x u) v = setVar0 x v := by
  funext i
  simp only [setVar0]
  split <;> rfl

/-! ### General substitution (composition)

`subst p qs` replaces variable `i` by `qs[i]`; a variable beyond the end of
`qs` is replaced by the zero polynomial. -/

def monoSubstFrom (qs : List Poly) : Nat → Mono → Poly
  | _, [] => one
  | i, e :: es => mul (polyPow (qs.getD i []) e) (monoSubstFrom qs (i + 1) es)

def subst : Poly → List Poly → Poly
  | [], _ => []
  | (m, c) :: p, qs => add (smul c (monoSubstFrom qs 0 m)) (subst p qs)

/-- The assignment obtained by evaluating each `qs[i]` at `x`. -/
def substEnv (x : Env) (qs : List Poly) : Env := fun i => eval x (qs.getD i [])

theorem eval_monoSubstFrom (x : Env) (qs : List Poly) :
    ∀ (i : Nat) (m : Mono),
      eval x (monoSubstFrom qs i m) = monoEvalFrom (substEnv x qs) i m
  | _, [] => by simp [monoSubstFrom, monoEvalFrom]
  | i, e :: es => by
    simp only [monoSubstFrom, monoEvalFrom, eval_mul, eval_polyPow,
      eval_monoSubstFrom x qs (i + 1) es, substEnv]

/-- **Evaluation commutes with substitution.** -/
theorem eval_subst (x : Env) :
    ∀ (p : Poly) (qs : List Poly), eval x (subst p qs) = eval (substEnv x qs) p
  | [], _ => by simp [subst, eval]
  | (m, c) :: p, qs => by
    simp only [subst, eval_add, eval_smul, eval_monoSubstFrom, eval_subst x p qs, eval,
      monoEval]

/-! ### Substitution for variable `0` only

Arity-free: the other variables are left as they are, so no variable count is
needed. `substVar0 [([1],1),([],1)] p` is `p(x0 + 1, x1, ...)`, and
`substVar0 [] p` is `p(0, x1, ...)`. -/

def substVar0 (q : Poly) : Poly → Poly
  | [] => []
  | ([], c) :: p => ([], c) :: substVar0 q p
  | (e :: es, c) :: p => mulTerm (0 :: es) c (polyPow q e) ++ substVar0 q p

theorem eval_substVar0 (x : Env) (q : Poly) :
    ∀ p : Poly, eval x (substVar0 q p) = eval (setVar0 x (eval x q)) p
  | [] => by simp [substVar0, eval]
  | ([], c) :: p => by
    simp only [substVar0, eval, eval_substVar0 x q p, monoEval, monoEvalFrom]
  | (e :: es, c) :: p => by
    simp only [substVar0, eval_append, eval_mulTerm, eval_polyPow, eval_substVar0 x q p,
      eval, monoEval, monoEvalFrom]
    have hc : monoEvalFrom x 1 es = monoEvalFrom (setVar0 x (eval x q)) 1 es :=
      monoEvalFrom_congr _ _ 1 es (fun j hj => by
        simp only [setVar0]
        split
        · omega
        · rfl)
    have h0 : setVar0 x (eval x q) 0 = eval x q := by simp [setVar0]
    rw [hc, h0, Int.pow_zero]
    simp only [Nat.zero_add, Int.one_mul]
    int_ring

/-- A polynomial none of whose monomials mentions variable `0` does not read it. -/
theorem eval_setVar0_of_free (x : Env) (v : Int) :
    ∀ p : Poly, p.all (fun t => t.1.headD 0 == 0) = true →
      eval (setVar0 x v) p = eval x p
  | [], _ => rfl
  | (m, c) :: p, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hm, hp⟩ := h
    simp only [eval, eval_setVar0_of_free x v p hp]
    congr 2
    cases m with
    | nil => rfl
    | cons e es =>
      simp only [List.headD, beq_iff_eq] at hm
      subst hm
      simp only [monoEval, monoEvalFrom, Int.pow_zero]
      exact congrArg _ (monoEvalFrom_congr _ _ 1 es (fun j hj => by
        simp only [setVar0]
        split
        · omega
        · rfl))

/-! ### Polynomial recurrences -/

/-- `x0 + 1`. -/
def x0PlusOne : Poly := [([1], 1), ([], 1)]

/-- The sequence the Python checker is about: `F(0,a) = initial(a)` and
`F(n+1,a) = F(n,a) + step(n,a)`. Variable `0` of `step` is the index; the
other variables are the parameters, read from `a`. -/
def recSeq (step initial : Poly) (a : Env) : Nat → Int
  | 0 => eval a initial
  | n + 1 => recSeq step initial a n + eval (setVar0 a n) step

/-- A recurrence certificate: the closed form, multiplied by `scale`. -/
structure RecCert where
  /-- The positive integer the producer multiplied the closed form by. -/
  scale : Int
  /-- `scale` times the closed form, as an integer polynomial. -/
  formula : Poly
  deriving Repr

/-- The checker. Total, search-free, decidable by kernel reduction. -/
def RecCert.check (c : RecCert) (step initial : Poly) : Bool :=
  (0 < c.scale) &&
  initial.all (fun t => t.1.headD 0 == 0) &&
  isZero (sub (substVar0 [] c.formula) (smul c.scale initial)) &&
  isZero (sub (sub (substVar0 x0PlusOne c.formula) c.formula) (smul c.scale step))

/-- **Soundness.** If the checker accepts, `scale` times the recursively
defined sequence equals the certified closed form, for every natural index
and every integer assignment of the parameters. -/
theorem RecCert.sound (c : RecCert) (step initial : Poly)
    (hcheck : c.check step initial = true) (a : Env) :
    ∀ n : Nat, c.scale * recSeq step initial a n = eval (setVar0 a n) c.formula := by
  simp only [RecCert.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨_, hfree⟩, hbase⟩, hstep⟩ := hcheck
  intro n
  induction n with
  | zero =>
    have h := eval_eq_of_sub_isZero (setVar0 a 0) _ _ hbase
    rw [eval_substVar0, eval_smul, eval_setVar0_of_free a 0 initial hfree] at h
    simp only [eval, setVar0_setVar0] at h
    simp only [recSeq]
    rw [← h]
    rfl
  | succ n ih =>
    have h := eval_eq_of_sub_isZero (setVar0 a n) _ _ hstep
    rw [eval_sub, eval_substVar0, eval_smul, setVar0_setVar0] at h
    have hx : eval (setVar0 a (n : Int)) x0PlusOne = ((n + 1 : Nat) : Int) := by
      simp [x0PlusOne, eval, monoEval, monoEvalFrom, setVar0, Int.pow_one]
    rw [hx] at h
    simp only [recSeq, Int.mul_add]
    rw [ih]
    omega

/-! ### Conserved invariants -/

/-- The state given by a finite list of coordinates, zero beyond its end. -/
def pointEnv (s : List Int) : Env := fun i => s.getD i 0

/-- The states reachable from `s0` by iterating the polynomial map `T`, whose
`i`-th output coordinate is `T[i]`. -/
inductive Reachable (T : List Poly) (s0 : Env) : Env → Prop
  | init : Reachable T s0 s0
  | step {s : Env} : Reachable T s0 s → Reachable T s0 (substEnv s T)

/-- An invariant certificate. The transition system (initial point and map)
is NOT part of it: the checker takes those as the problem. -/
structure InvCert where
  /-- The positive integer the producer multiplied the rational invariant by.

  EXPORTER METADATA, NOT A LEAN GUARANTEE. Nothing in `check` ties `scale` to
  `invariant`: the relation `invariant = scale * I` is established by the
  exporter's re-check in Python, not by Lean. `0 < scale` only records that the
  multiplier the exporter claims to have used is positive, which is what a
  reader needs to pass from `invariant = 0` back to `I = 0`. Unlike `RecCert`,
  where a zero scale would make the certificate vacuous, here a zero scale would
  not; the non-vacuity guard for this family is the separate `invariant` conjunct
  below. (Adversarial review found the earlier docstrings implied otherwise.) -/
  scale : Int
  /-- `scale` times the rational invariant. -/
  invariant : Poly
  deriving Repr

/-- The checker. Conjuncts, in order:

  * `0 < scale` -- exporter metadata, see `InvCert.scale`.
  * the invariant is not identically zero. Without this, the zero polynomial is
    a "certified invariant" of every system; true, and worthless as evidence.
    The prototype's Python checker accepts it, so Lean is stricter here, which
    can only cost completeness. Added after adversarial review.
  * three arity conjuncts mirroring the Python checker, which raises (and so
    rejects) on a dimension mismatch.
  * the invariant vanishes at the initial point, and is preserved by `T`.

Soundness needs only the last two. -/
def InvCert.check (c : InvCert) (initial : List Int) (T : List Poly) : Bool :=
  (0 < c.scale) &&
  !(isZero c.invariant) &&
  (initial.length == T.length) &&
  c.invariant.all (fun t => t.1.length ≤ T.length) &&
  T.all (fun q => q.all (fun t => t.1.length ≤ T.length)) &&
  (eval (pointEnv initial) c.invariant == 0) &&
  isZero (sub (subst c.invariant T) c.invariant)

/-- **Soundness.** If the checker accepts, the invariant vanishes at every
state reachable from the initial point. -/
theorem InvCert.sound (c : InvCert) (initial : List Int) (T : List Poly)
    (hcheck : c.check initial T = true) :
    ∀ s : Env, Reachable T (pointEnv initial) s → eval s c.invariant = 0 := by
  simp only [InvCert.check, Bool.and_eq_true, beq_iff_eq] at hcheck
  obtain ⟨⟨_, hinit⟩, hid⟩ := hcheck
  intro s hs
  induction hs with
  | init => exact hinit
  | @step s _ ih =>
    rw [← eval_subst]
    have := eval_eq_of_sub_isZero s _ _ hid
    rw [this, ih]

/-- `scale` is positive whenever the check passes. This is a fact about the
metadata only: it lets a reader who ALSO trusts the exporter's claim that
`invariant = scale * I` conclude `I = 0` on the orbit. Lean itself proves nothing
connecting `scale` to `invariant`. -/
theorem InvCert.scale_pos (c : InvCert) (initial : List Int) (T : List Poly)
    (hcheck : c.check initial T = true) : 0 < c.scale := by
  simp only [InvCert.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.1.1.1.1.1.1

theorem RecCert.scale_pos (c : RecCert) (step initial : Poly)
    (hcheck : c.check step initial = true) : 0 < c.scale := by
  simp only [RecCert.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.1.1.1

end Forge.Checker
