import Forge.Checker.Cone
/-
  Typed reification: a syntax of integer polynomial expressions, its meaning,
  and a PROVED translation into the checker's `Poly`.

  WHY THIS FILE EXISTS. The certificates in `Corpus.lean` are connected to a
  human-readable goal by a generated bridge (`have` + `simp` + `omega`). That
  bridge has no theorem behind it. Here the connection is a theorem,
  `eval_toPoly`: for every expression `t` and every assignment `x`,
  `eval x (toPoly t) = denote x t`. The tactic in `Tactic.lean` only has to
  produce a `t` whose `denote` is DEFINITIONALLY the user's expression, which the
  kernel checks; nothing about the translation is left to a script that might
  not fit.

  `denote` uses exactly the operations an ordinary `Int` goal elaborates to:
  `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `Neg.neg` and `HPow.hPow Int Nat Int`.

  CORE LEAN ONLY. No metaprogramming here either; that is in `Tactic.lean`.
-/
namespace Forge.Checker

/-- Integer polynomial expressions over atoms `0, 1, 2, ...`. -/
inductive IExpr where
  | atom (index : Nat)
  | const (value : Int)
  | add (a b : IExpr)
  | sub (a b : IExpr)
  | neg (a : IExpr)
  | mul (a b : IExpr)
  | pow (base : IExpr) (exponent : Nat)
  deriving Repr, Inhabited

namespace IExpr

/-- The meaning of an expression, using the same operations as a user's goal. -/
def denote (x : Env) : IExpr → Int
  | atom i => x i
  | const c => c
  | add a b => denote x a + denote x b
  | sub a b => denote x a - denote x b
  | neg a => -denote x a
  | mul a b => denote x a * denote x b
  | pow a n => denote x a ^ n

/-- The monomial `x_i`: exponent `1` at position `i`, zeros before it. -/
def atomMono (i : Nat) : Mono := List.replicate i 0 ++ [1]

/-- Translation into the checker's polynomial representation. -/
def toPoly : IExpr → Poly
  | atom i => [(atomMono i, 1)]
  | const c => [([], c)]
  | add a b => Forge.Checker.add (toPoly a) (toPoly b)
  | sub a b => Forge.Checker.sub (toPoly a) (toPoly b)
  | neg a => Forge.Checker.neg (toPoly a)
  | mul a b => Forge.Checker.mul (toPoly a) (toPoly b)
  | pow a n => polyPow (toPoly a) n

end IExpr

open IExpr

theorem monoEvalFrom_atomMono (x : Env) :
    ∀ (i j : Nat), monoEvalFrom x j (atomMono i) = x (j + i)
  | 0, j => by
    simp [atomMono, monoEvalFrom, Int.pow_one]
  | i + 1, j => by
    have ih := monoEvalFrom_atomMono x i (j + 1)
    simp only [atomMono, List.replicate_succ, List.cons_append] at ih ⊢
    simp only [monoEvalFrom, Int.pow_zero, Int.one_mul]
    rw [ih, Nat.add_assoc, Nat.add_comm 1 i]

/-- **The bridge theorem.** Translation preserves meaning at every assignment. -/
theorem eval_toPoly (x : Env) : ∀ t : IExpr, eval x (toPoly t) = denote x t
  | .atom i => by
    simp only [toPoly, denote, eval, monoEval, monoEvalFrom_atomMono, Nat.zero_add,
      Int.one_mul, Int.add_zero]
  | .const c => by
    simp [toPoly, denote, eval, monoEval, monoEvalFrom]
  | .add a b => by
    simp only [toPoly, denote, eval_add, eval_toPoly x a, eval_toPoly x b]
  | .sub a b => by
    simp only [toPoly, denote, eval_sub, eval_toPoly x a, eval_toPoly x b]
  | .neg a => by
    simp only [toPoly, denote, eval_neg, eval_toPoly x a]
  | .mul a b => by
    simp only [toPoly, denote, eval_mul, eval_toPoly x a, eval_toPoly x b]
  | .pow a n => by
    simp only [toPoly, denote, eval_polyPow, eval_toPoly x a]

/-! ### Environments and hypothesis lists

These are what the tactic instantiates. Everything the tactic supplies is
checked against them by the kernel. -/

/-- The environment assigning the `i`-th list element to atom `i` (and `0`
beyond the end). Structural recursion, so it reduces by `whnf`. -/
def Env.ofList : List Int → Env
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, n + 1 => Env.ofList as n

/-- Every expression in the list is nonnegative. -/
def AllNonneg (x : Env) : List IExpr → Prop
  | [] => True
  | t :: ts => 0 ≤ denote x t ∧ AllNonneg x ts

/-- Every expression in the list vanishes. -/
def AllZero (x : Env) : List IExpr → Prop
  | [] => True
  | t :: ts => denote x t = 0 ∧ AllZero x ts

theorem allNonneg_eval (x : Env) :
    ∀ ts : List IExpr, AllNonneg x ts → ∀ g ∈ ts.map toPoly, 0 ≤ eval x g
  | [], _, g, hg => by simp at hg
  | t :: ts, ⟨ht, hts⟩, g, hg => by
    simp only [List.map_cons, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [eval_toPoly]; exact ht
    · exact allNonneg_eval x ts hts g hg

theorem allZero_eval (x : Env) :
    ∀ ts : List IExpr, AllZero x ts → ∀ f ∈ ts.map toPoly, eval x f = 0
  | [], _, f, hf => by simp at hf
  | t :: ts, ⟨ht, hts⟩, f, hf => by
    simp only [List.map_cons, List.mem_cons] at hf
    rcases hf with rfl | hf
    · rw [eval_toPoly]; exact ht
    · exact allZero_eval x ts hts f hf

/-- **What the tactic applies.** A certificate accepted for the reified target
and constraints proves nonnegativity of the target's meaning, given that the
constraints' meanings hold. -/
theorem cone_denote (c : Cert) (x : Env) (tp : IExpr) (gs fs : List IExpr)
    (hcheck : c.check (toPoly tp) (gs.map toPoly) (fs.map toPoly) = true)
    (hg : AllNonneg x gs) (hf : AllZero x fs) : 0 ≤ denote x tp := by
  have h := Cert.sound c (toPoly tp) (gs.map toPoly) (fs.map toPoly) hcheck x
    (allNonneg_eval x gs hg) (allZero_eval x fs hf)
  rwa [eval_toPoly] at h

/-- The `a ≤ b` form: certify `b - a`. -/
theorem cone_denote_le (c : Cert) (x : Env) (ta tb : IExpr) (gs fs : List IExpr)
    (hcheck : c.check (toPoly (IExpr.sub tb ta)) (gs.map toPoly) (fs.map toPoly) = true)
    (hg : AllNonneg x gs) (hf : AllZero x fs) : denote x ta ≤ denote x tb :=
  Int.le_of_sub_nonneg (cone_denote c x (IExpr.sub tb ta) gs fs hcheck hg hf)

end Forge.Checker
