import Mathlib
import Forge.Checker.Cone
/-
  SOUNDNESS OVER THE REALS for the cone certificates of `Forge.Checker.Cone`.

  WHY. `Cert.sound` concludes nonnegativity at INTEGER points, because the core
  development evaluates polynomials in `Int` -- Lean core has no reals. But the
  certificate itself asserts a polynomial IDENTITY with integer coefficients,
  and an identity holds in every commutative ring. This file proves that the
  SAME Boolean check, `Cert.check`, establishes nonnegativity at every REAL
  point satisfying the constraints. No new checker, no new certificates: the
  `_checks` theorems already in the corpus transfer as they are.

  MATHLIB. This file imports Mathlib. When written it was the first
  Mathlib-dependent file in this repository to be checked, compiled with Lean
  v4.32.0 by `tools/build_real.py`, because that was the only built Mathlib on
  the machine. It has since compiled unchanged on the pinned v4.34.0 toolchain
  against the pinned Mathlib too (`tools/build_mathlib_forge.py`).

  AXIOMS. Mathlib's reals are built with `Classical.choice`, so the theorems here
  depend on propext, Classical.choice and Quot.sound -- unlike the core files,
  which avoid choice. That is recorded, not hidden.
-/
namespace Forge.Checker.Real

open Forge.Checker

noncomputable section

/-- A real-valued monomial evaluation, variable `i` first. -/
def monoEvalFromR (x : ℕ → ℝ) : ℕ → Mono → ℝ
  | _, [] => 1
  | i, e :: es => x i ^ e * monoEvalFromR x (i + 1) es

def monoEvalR (x : ℕ → ℝ) (m : Mono) : ℝ := monoEvalFromR x 0 m

/-- A real-valued polynomial evaluation. Coefficients are the same integers. -/
def evalR (x : ℕ → ℝ) : Poly → ℝ
  | [] => 0
  | (m, c) :: p => (c : ℝ) * monoEvalR x m + evalR x p

theorem monoEvalFromR_addMono (x : ℕ → ℝ) :
    ∀ (i : ℕ) (m m' : Mono),
      monoEvalFromR x i (addMono m m') = monoEvalFromR x i m * monoEvalFromR x i m'
  | _, [], m' => by simp [addMono, monoEvalFromR]
  | _, a :: as, [] => by simp [addMono, monoEvalFromR]
  | i, a :: as, b :: bs => by
    simp only [addMono, monoEvalFromR, monoEvalFromR_addMono x (i + 1) as bs, pow_add]
    ring

theorem evalR_append (x : ℕ → ℝ) : ∀ p q : Poly, evalR x (p ++ q) = evalR x p + evalR x q
  | [], q => by simp [evalR]
  | (m, c) :: p, q => by
    simp only [List.cons_append, evalR, evalR_append x p q]
    ring

theorem evalR_neg (x : ℕ → ℝ) : ∀ p : Poly, evalR x (neg p) = -evalR x p
  | [] => by simp [neg, evalR]
  | (m, c) :: p => by
    have ih := evalR_neg x p
    simp only [neg, List.map_cons] at ih ⊢
    simp only [evalR, ih, Int.cast_neg]
    ring

theorem evalR_smul (x : ℕ → ℝ) (k : Int) : ∀ p : Poly, evalR x (smul k p) = k * evalR x p
  | [] => by simp [smul, evalR]
  | (m, c) :: p => by
    have ih := evalR_smul x k p
    simp only [smul, List.map_cons] at ih ⊢
    simp only [evalR, ih, Int.cast_mul]
    ring

theorem evalR_mulTerm (x : ℕ → ℝ) (m : Mono) (c : Int) :
    ∀ q : Poly, evalR x (mulTerm m c q) = c * monoEvalR x m * evalR x q
  | [] => by simp [mulTerm, evalR]
  | (m', c') :: q => by
    have ih := evalR_mulTerm x m c q
    simp only [mulTerm, List.map_cons] at ih ⊢
    simp only [evalR, ih, Int.cast_mul, monoEvalR, monoEvalFromR_addMono]
    ring

theorem evalR_mul (x : ℕ → ℝ) : ∀ p q : Poly, evalR x (mul p q) = evalR x p * evalR x q
  | [], q => by simp [mul, evalR]
  | (m, c) :: p, q => by
    simp only [mul, evalR_append, evalR_mulTerm, evalR_mul x p q, evalR]
    ring

theorem monoEvalFromR_trimMono (x : ℕ → ℝ) :
    ∀ (i : ℕ) (m : Mono), monoEvalFromR x i (trimMono m) = monoEvalFromR x i m
  | _, [] => rfl
  | i, e :: es => by
    have ih := monoEvalFromR_trimMono x (i + 1) es
    simp only [trimMono]
    split
    · next h =>
        rw [h] at ih
        simp only [monoEvalFromR] at ih
        split
        · next he => simp [monoEvalFromR, he, ← ih]
        · simp [monoEvalFromR, ← ih]
    · next t ht =>
        simp only [monoEvalFromR]
        rw [← ih]

theorem evalR_insertTerm (x : ℕ → ℝ) (m : Mono) (c : Int) :
    ∀ p : Poly, evalR x (insertTerm m c p) = c * monoEvalR x m + evalR x p
  | [] => by simp [insertTerm, evalR]
  | (m', c') :: p => by
    simp only [insertTerm]
    split
    · next h =>
        subst h
        simp only [evalR, Int.cast_add]
        ring
    · next h =>
        simp only [evalR, evalR_insertTerm x m c p]
        ring

theorem evalR_collect (x : ℕ → ℝ) : ∀ p : Poly, evalR x (collect p) = evalR x p
  | [] => by simp [collect]
  | (m, c) :: p => by
    simp only [collect, evalR_insertTerm, evalR_collect x p, evalR, monoEvalR,
      monoEvalFromR_trimMono]

theorem evalR_eq_zero_of_coeffs (x : ℕ → ℝ) :
    ∀ p : Poly, (∀ t ∈ p, t.2 = 0) → evalR x p = 0
  | [], _ => by simp [evalR]
  | (m, c) :: p, h => by
    have hc : c = 0 := h (m, c) (by simp)
    have hp : evalR x p = 0 := evalR_eq_zero_of_coeffs x p (fun t ht => h t (by simp [ht]))
    simp [evalR, hc, hp]

/-- The zero test the checker runs is sound over the reals too. -/
theorem evalR_eq_zero_of_isZero (x : ℕ → ℝ) (p : Poly) (h : isZero p = true) :
    evalR x p = 0 := by
  have hall : ∀ t ∈ collect p, t.2 = 0 := by
    intro t ht
    have := List.all_eq_true.mp h t ht
    simpa using this
  have := evalR_eq_zero_of_coeffs x (collect p) hall
  rwa [evalR_collect] at this

theorem evalR_eq_of_sub_isZero (x : ℕ → ℝ) (p q : Poly) (h : isZero (sub p q) = true) :
    evalR x p = evalR x q := by
  have := evalR_eq_zero_of_isZero x (sub p q) h
  simp only [sub, evalR_append, evalR_neg] at this
  linarith

theorem evalR_add (x : ℕ → ℝ) (p q : Poly) : evalR x (add p q) = evalR x p + evalR x q :=
  evalR_append x p q

theorem evalR_one (x : ℕ → ℝ) : evalR x one = 1 := by
  simp [one, evalR, monoEvalR, monoEvalFromR]

theorem evalR_polyPow (x : ℕ → ℝ) (q : Poly) : ∀ n, evalR x (polyPow q n) = evalR x q ^ n
  | 0 => by simp [polyPow, evalR_one]
  | n + 1 => by
    simp only [polyPow, evalR_mul, evalR_polyPow x q n, pow_succ]
    ring

theorem evalR_powerProduct_nonneg (x : ℕ → ℝ) :
    ∀ (es : List ℕ) (gs : List Poly), (∀ g ∈ gs, 0 ≤ evalR x g) →
      0 ≤ evalR x (powerProduct es gs)
  | [], _, _ => by simp [powerProduct, evalR_one]
  | _ :: _, [], _ => by simp [powerProduct, evalR_one]
  | e :: es, g :: gs, h => by
    have hg : 0 ≤ evalR x g := h g (by simp)
    have hrest := evalR_powerProduct_nonneg x es gs (fun g' hg' => h g' (by simp [hg']))
    simp only [powerProduct, evalR_mul, evalR_polyPow]
    exact mul_nonneg (pow_nonneg hg e) hrest

theorem evalR_sumCone_nonneg (x : ℕ → ℝ) (ineqs : List Poly)
    (hg : ∀ g ∈ ineqs, 0 ≤ evalR x g) :
    ∀ ts : List Square, (∀ s ∈ ts, 0 ≤ s.weight) → 0 ≤ evalR x (sumCone ts ineqs)
  | [], _ => by simp [sumCone, evalR]
  | s :: ts, h => by
    have hw : (0 : ℝ) ≤ s.weight := by exact_mod_cast h s (by simp)
    have hrest := evalR_sumCone_nonneg x ineqs hg ts (fun s' hs' => h s' (by simp [hs']))
    simp only [sumCone, coneTerm, evalR_add, evalR_smul, evalR_mul]
    have hp := evalR_powerProduct_nonneg x s.powers ineqs hg
    have hsq := mul_self_nonneg (evalR x s.poly)
    exact add_nonneg (mul_nonneg hw (mul_nonneg hp hsq)) hrest

theorem evalR_dot_eq_zero (x : ℕ → ℝ) :
    ∀ (hs fs : List Poly), (∀ f ∈ fs, evalR x f = 0) → evalR x (dot hs fs) = 0
  | [], _, _ => by simp [dot, evalR]
  | _ :: _, [], _ => by simp [dot, evalR]
  | h :: hs, f :: fs, hz => by
    have hf : evalR x f = 0 := hz f (by simp)
    have hrest := evalR_dot_eq_zero x hs fs (fun f' hf' => hz f' (by simp [hf']))
    simp only [dot, evalR_add, evalR_mul, hf, hrest]
    ring

/-- **Soundness over the reals.** The same Boolean check as `Cert.sound`, and the
conclusion holds at every REAL point satisfying the constraints. -/
theorem Cert.sound_real (c : Cert) (p : Poly) (ineqs eqs : List Poly)
    (hcheck : c.check p ineqs eqs = true) (x : ℕ → ℝ)
    (hge : ∀ g ∈ ineqs, 0 ≤ evalR x g)
    (hz : ∀ f ∈ eqs, evalR x f = 0) : 0 ≤ evalR x p := by
  simp only [Cert.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
  obtain ⟨⟨⟨⟨hpos, hw⟩, _⟩, _⟩, hid⟩ := hcheck
  have hEq := evalR_eq_of_sub_isZero x _ _ hid
  rw [evalR_smul, evalR_add, evalR_dot_eq_zero x _ _ hz] at hEq
  have hnn : 0 ≤ evalR x (sumCone c.squares ineqs) :=
    evalR_sumCone_nonneg x ineqs hge c.squares (fun s hs => by
      have := List.all_eq_true.mp hw s hs
      simpa using this)
  have hscale : (0 : ℝ) < c.scale := by exact_mod_cast hpos
  have hprod : 0 ≤ (c.scale : ℝ) * evalR x p := by rw [hEq]; linarith
  exact (mul_nonneg_iff_of_pos_left hscale).mp hprod

end

end Forge.Checker.Real
