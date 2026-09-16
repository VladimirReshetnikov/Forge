# `Forge.Checker` — a certificate checker that is actually checked

This is the first part of this repository that closes the loop the project is
named for: a certificate a search produced, checked by Lean, with a *proof*
that checking it establishes the mathematical claim.

Everything here is **core Lean only**. No Mathlib, no `ring`, no `nlinarith`.
That is a deliberate constraint and not a limitation of the method: 59 of this
repository's 86 `.lean` files import Mathlib or a sibling module and **none of
them has ever been checked by anything**. A checker in that bucket would have
been one more uncompiled claim.

## What is here

| File | What it is |
| --- | --- |
| `Poly.lean` | Sparse multivariate polynomials over `Int`. Evaluation is proved to be a ring homomorphism, and `isZero` is proved to decide identical vanishing. |
| `Cone.lean` | The certificate type, the checker `Cert.check`, and `Cert.sound`. |
| `Corpus.lean` | **Generated** from the prototype's own certificate bundle by `tools/export_lean_cone.py`. Do not edit. |

## The theorem

```lean
theorem Cert.sound (c : Cert) (p : Poly) (ineqs eqs : List Poly)
    (hcheck : c.check p ineqs eqs = true) (x : Env)
    (hge : ∀ g ∈ ineqs, 0 ≤ eval x g)
    (hz  : ∀ f ∈ eqs,   eval x f = 0) : 0 ≤ eval x p
```

`Cert.check` is a total `Bool`-valued function that performs no search. The
theorem says nothing about where the certificate came from: found by search,
written by hand, or produced adversarially, it faces the same check and the
conclusion follows from the check alone.

What is certified is the polynomial identity

```
D * p  =  Σᵢ wᵢ · (Πₖ gₖ ^ eᵢₖ) · qᵢ²  +  Σⱼ hⱼ · fⱼ
```

with `D > 0` and every `wᵢ ≥ 0`. On the feasible set every `gₖ ≥ 0`, so each
product of their powers is nonnegative, each square is nonnegative, and the
equality terms vanish — leaving `D * p ≥ 0`, hence `p ≥ 0`.

Every theorem in these three files depends on `propext` and `Quot.sound`, and
nothing else. No `sorry`, no `native_decide`, no `Lean.ofReduceBool`.

## Integers, not rationals

The prototype searches over ℚ. `tools/export_lean_cone.py` clears denominators
before emitting, which is a change of representation rather than a weakening:
every multiplier it introduces is *positive*, so `D·p ≥ 0` iff `p ≥ 0`,
`dg·g ≥ 0` iff `g ≥ 0`, and `df·f = 0` iff `f = 0`. The exporter re-checks the
resulting integer identity in Python before emitting, and the Lean kernel
checks it again by reduction.

`Int` is in Lean core; `Rat`'s arithmetic lemmas largely are not. That is the
whole reason for the choice.

## Two statements per certificate

The encoded form is an implementation detail:

```lean
theorem hidden_quadratic_nonneg (x : Env) : 0 ≤ eval x hidden_quadratic_target
```

The bridge restates it as a goal someone would actually type:

```lean
theorem hidden_quadratic_concrete (x0 x1 : Int) :
    0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2
```

Both are generated. A checker that only proves things about its own encoding
is not usable, and the bridge is what makes the difference.

## Scope, stated plainly

- `Env` assigns **integers** to variables, so what is proved is nonnegativity
  at integer points. The *identity* the checker verifies holds in every
  commutative ring; lifting the conclusion to ℝ needs an ordered field and
  therefore Mathlib.
- This is a checker, **not a tactic**. There is no `forge` tactic. Applying a
  certificate to a goal is a generated `have` and a `simp`/`omega`, not
  automation that finds the certificate for you.
- The checker is proved sound. It is **not** proved complete, and nothing here
  says a certificate exists for any particular problem.
- Soundness is relative to `eval` being the right semantics for `Poly`. That is
  a definition, not a theorem, and a reader should look at it.

## Regenerating

```bash
python tools/export_lean_cone.py
```

```bash
cd lean && LEAN_PATH=.lake/build/lib lean Forge/Checker/Corpus.lean
```
