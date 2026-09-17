# `Forge.Checker` — Gate 2 of the design, in core Lean

This is the part of the repository that closes the loop the project is named
for: a certificate a search produced, checked by the Lean kernel, with a *proof*
that checking it establishes the mathematical claim — and, since Gate 2, a
tactic that applies it to an ordinary goal and an oracle protocol that finds it.

Everything here is **core Lean only**. No Mathlib, no `ring`, no `nlinarith`.
That was a deliberate constraint: 58 of this repository's `.lean` files are
delivered Mathlib-dependent files that **nothing has ever checked**, and a checker
in that bucket would have been one more uncompiled claim. The one exception is
`lean/Forge/Real/`, below, which lifts soundness to the reals with Mathlib and is
itself checked.

## What is here

Gate 2 of the design (article §17) calls for: typed reification and cone replay
in Lean; the quadratic and finite-cone oracles called through a bounded data
protocol; the affine/Farkas and recurrence certificate reconstructions. Exit
criteria: Lean checking of every end-to-end example, mutation rejection at the
data boundary, recorded axiom dependencies.

| File | What it is |
| --- | --- |
| `Poly.lean` | Sparse `Int` polynomials. Evaluation is proved a ring homomorphism; `isZero` is proved to decide identical vanishing, up to trailing zeros. |
| `Cone.lean` | Cone certificates: `Cert.check` and `Cert.sound`. |
| `Corpus.lean` | **Generated** from the prototype's cone certificates. |
| `Bench.lean` | **Generated** benchmark: 36 problems, 6 negative controls. |
| `Reify.lean` | `IExpr`, `denote`, `toPoly`, and **`eval_toPoly`, proved** — the bridge from a certificate to a goal is a theorem, not a generated script. |
| `Tactic.lean` | `forge_cone [hyps] using cert` and `forge_reify`. |
| `Oracle.lean` | `forge_cone?`: runs the prototype's search as a separate process through a bounded JSON protocol, decodes strictly, closes the goal by the same kernel path, and suggests an oracle-free proof. |
| `TacticTest.lean`, `OracleTest.lean` | Positive tests, negative tests, review regressions, mutation rejection at the data boundary. `OracleTest` needs `python`. |
| `Affine.lean`, `AffineCorpus.lean` | Integral affine witnesses: `AffineCert.sound`, and `check_iff` (exact, not only sound). |
| `Farkas.lean` | Farkas linear-infeasibility certificates with soundness. **No prototype family corresponds**: the prototype code labelled Farkas is an implication certificate. |
| `Recurrence.lean`, `RecurrenceCorpus.lean` | Polynomial recurrences (`RecCert.sound`, all `n`) and conserved invariants (`InvCert.sound`, every reachable state), with substitution proved. |
| `../../AxiomAudit.lean` | Fails to compile if any theorem under `Forge.Checker` uses an axiom outside `propext`, `Quot.sound` beyond documented, necessary exemptions. |

Generated corpora are written only through `tools/lean_emit_guard.py`; see
**The data boundary** below.

## Where Gate 2 stands, against its own exit criteria

| Criterion | Status |
| --- | --- |
| Typed reification | **Met.** `eval_toPoly` proved. |
| Cone replay in Lean | **Met.** |
| Oracles through a bounded data protocol | **Met** for the cone family: size, time, output and decoding bounds, all tested. |
| Affine/Farkas reconstruction | **Met.** Three affine records and three Farkas refutations in the bundle, each exported with negative controls (`AffineCorpus.lean`, `FarkasCorpus.lean`); the corpus is still small. |
| Recurrence reconstruction | **Met**: all 5 power sums and the one conserved invariant. |
| Every end-to-end example checked | **Met.** |
| Mutation rejection at the data boundary | **Met — after a hole was found and closed** (see below). |
| Recorded axiom dependencies | **Met**, and enforced by `AxiomAudit.lean`. |
| "Adds useful nonlinear facts to a stock `grind` leaf" | **Met as composition only**: `compose_with_grind` shows a goal neither `grind` nor `omega` proves alone, closed after `forge_cone` supplies one fact via `have`. Nothing calls `forge_cone` automatically. |
| Gate 1 (trustworthy orchestration), its prerequisite | **First milestone.** `Forge/Frontend.lean`: `forge` runs decide, omega, `forge_cone?` (off in restricted mode) and grind in a fixed order with full state rollback, rejects proofs containing `sorry` or axioms outside the policy by inspecting the term, and logs a deterministic replay record. `FrontendTest.lean` pins each exit criterion: a restricted baseline with `#print axioms`, an admitted proof rejected, the choice policy enforced both ways, and a failed worker's metavariable assignment rolled back. Not built: worker contracts beyond the proof audit, source-assumption preservation, planning. Gate 2 was built first. |

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
- `forge_cone` and `forge_cone?` are tactics **for one certificate family**.
  There is still no `forge` planner tactic — nothing decides which family to try,
  decomposes a goal, or orchestrates workers (that is Gate 1 and Gate 3).
  `forge_cone?` finds certificates only by calling the prototype's Python search
  as an untrusted process; the proof it leaves behind does not depend on it.
- The checker is proved sound. It is **not** proved complete, and nothing here
  says a certificate exists for any particular problem.
- Soundness is relative to `eval` being the right semantics for `Poly`. That is
  a definition, not a theorem, and a reader should look at it.

## Over the reals

`Cert.sound` concludes nonnegativity at integer points, because core Lean has no
reals. But a certificate asserts a polynomial *identity*, which holds in every
commutative ring, so the same Boolean check should prove the real statement.
[`lean/Forge/Real/Cone.lean`](../Real/Cone.lean) proves exactly that:

```lean
theorem Cert.sound_real (c : Cert) (p : Poly) (ineqs eqs : List Poly)
    (hcheck : c.check p ineqs eqs = true) (x : ℕ → ℝ)
    (hge : ∀ g ∈ ineqs, 0 ≤ evalR x g)
    (hz  : ∀ f ∈ eqs,   evalR x f = 0) : 0 ≤ evalR x p
```

No new checker and no new certificates: the corpus's existing `_checks` theorems
transfer as they are. [`Examples.lean`](../Real/Examples.lean) restates all three
prototype certificates over ℝ, including `x + y = 1 ⇒ 1 ≤ 2x² + 2y²`, which over
the reals is tight at `x = y = 1/2`.

Both files import Mathlib and are compiled by `tools/build_real.py` with Lean
v4.32 (the only built Mathlib here), under the same memory guard as the
head-to-head: exit 0, no errors, no warnings. Their theorems depend on `propext`,
`Classical.choice` and `Quot.sound` — `Classical.choice` because Mathlib's reals
are built on it, unlike the core files. Recorded in
[`results/lean-real.json`](../../../results/lean-real.json).

## The tactic

```lean
theorem hidden_quadratic_concrete' (x0 x1 : Int) :
    0 ≤ 147 + (-168) * x1 + 99 * x1^2 + (-126) * x0 + (-26) * (x0 * x1) + 78 * x0^2 := by
  forge_cone (atoms := [x0, x1]) using hidden_quadratic_cert
```

`forge_cone` reifies the goal and hypotheses into `IExpr`, proves the check by
`decide +kernel`, and closes the goal with `cone_denote`, which is `Cert.sound`
transported through `eval_toPoly`. The metaprogram is untrusted: the kernel
re-checks the hypotheses' and goal's correspondence with their reified forms by
definitional equality. Atom order is: explicit `atoms`, then the goal left to
right, then the hypotheses in list order; certificates are expressed in it.

`forge_cone?` does the same after asking an oracle. It serialises the reified
problem, runs `tools/forge_oracle.py` (configurable via `forge.oracle.cmd`),
bounds its time and output, decodes the reply strictly, and emits
`Try this: forge_cone … using {…}` so the saved proof never mentions Python.

Measured on an isolated call: about 420 ms for the oracle round trip and 150 ms
for the kernel check. Inside a test file the per-call figure reads ~4.5 s,
because Lean elaborates theorems in parallel and ten oracle processes contend.

## The data boundary

Every exporter used to paste the bundle's record id into a Lean doc comment. An
id containing `-/` closes the comment, and what follows is compiled. Review
produced a generated corpus that compiles cleanly and proves `(1 : Int) = 2` from
an injected `axiom`; the same attack then worked on `tools/export_lean_cone.py`.
The real theorems were never affected, but a generated `axiom … : False` poisons
everything that imports it.

`tools/lean_emit_guard.py` is the single fix: ids must be plain identifiers
(collisions and empty ids refused), and every emitted file is audited, with
comments stripped, for `axiom`, `sorry`, `native_decide`, `unsafe`, `opaque`,
`macro`, `#eval` and the like before it is written. All corpora regenerate
byte-identical through it; the injection is refused by every exporter.

## Adversarial review

Three skeptics reviewed Gate 2, each told to make it accept something false, and
to report only findings they had reproduced.

| Scope | Attacks | False statements accepted | Findings |
| --- | ---: | ---: | --- |
| Tactic and oracle | 45, including a hostile oracle | 0 | 4 minor, all fixed and pinned by regression tests |
| Affine and Farkas | 20 + a 4000-case differential fuzz against Python | 0 | 1 major (the injection), minor exporter gaps |
| Recurrence | 20+ | 0 | 1 major (a false claim in prose), 4 minor |

Fixed as a result: the injection hole; untrue size bounds (the kernel's limit
tracks the *expanded* identity, measured at about 1600 terms, and a valid
certificate past it is now reported as "could NOT BE CHECKED", not "REJECTED");
goal metavariables assigned by atom matching; numerals read without checking
their instance, so the oracle could be sent a different problem; the command
resolver replacing `python` with a stray file; an exporter docstring claiming the
certificate cannot choose the problem, which review showed it can for conserved
invariants; a scale conjunct that guaranteed nothing; two exporter crashes.

One test had to be rewritten because it pinned nothing: it passed with or
without the fix it was meant to guard.

## Known limits

- **Size.** Checks fail beyond roughly 1600 terms of expanded identity with
  Lean's default recursion limit. Measured in `results/lean-kernel-depth.json`:
  raising `maxRecDepth` lifts it, but at 148 s and 4.5 GB for 2025 products, so it
  is not shipped. A tail-recursive `collect` does **not** help -- an earlier
  version of this file called it the obvious fix -- because the kernel evaluates
  lazily and the accumulator stays a deferred thunk of the same depth. The fix
  that scales is Kronecker substitution (check the identity with GMP integers at
  one large point, with a proved coefficient bound); it is not implemented.
- **Integers in the tactic.** `forge_cone` states goals over `Int`. The same
  certificates are sound over ℝ — see **Over the reals** — but no tactic applies
  them to a real-valued goal yet; the real theorems are stated by hand.
- **The prototype's data model** used to let a conserved-invariant record carry
  its problem inside the certificate, so the certificate chose what it
  certified. Fixed: the problem now lives in `input`, and the decoder refuses a
  certificate that names an initial point or transition.
- **Affine and Farkas data are small**: three bundle records each. The Farkas
  family used to have none; it now has a prototype search and checker
  (`prototype/forge/witness/farkas.py`) and a generated corpus.

## Regenerating

```bash
python tools/export_lean_cone.py
```

```bash
cd lean && LEAN_PATH=.lake/build/lib lean Forge/Checker/Corpus.lean
```

The affine and Farkas corpora are generated the same way:

```bash
python tools/export_lean_affine.py
```

```bash
python tools/export_lean_farkas.py
```

## Head-to-head on problems Forge did not choose

`tools/compare_tactics.py` runs `forge_cone?`, `nlinarith`, `positivity`,
`grind` and `omega` on the 20 well-known inequalities in
[`bench/tactics/problems.json`](../../../bench/tactics/problems.json), each
checked true on an integer grid before any Lean ran. Every success below is a
kernel-checked proof: failures and errors match one-for-one, and no `sorry`.

It was run twice, and the difference between the runs is the point.

| Problem | `forge_cone?` first run | `forge_cone?` after search fixes | `nlinarith` | `positivity` |
| --- | --- | --- | --- | --- |
| AM-GM, 2 variables | ok | ok | fails | form |
| 1 + x² ≥ 2x | ok | ok | ok | form |
| x²+y²+z² ≥ xy+yz+zx | ok | ok | fails | form |
| (x+y)² ≤ 2(x²+y²) | ok | ok | fails | form |
| x² − xy + y² ≥ 0 | ok | ok | ok | fails |
| (x−1)²+(y−1)² ≥ 0, expanded | ok | ok | fails | form |
| PSD tridiagonal form, 3 vars | ok | ok | fails | fails |
| Cauchy–Schwarz, 2D | ok | ok | fails | form |
| a⁴+b⁴ ≥ a³b+ab³ | none found | **ok** | fails | form |
| (x−y)⁴ ≥ 0, expanded | none found | **ok** | fails | fails |
| x⁴+y⁴+z⁴ ≥ x²y²+y²z²+z²x² | ok | ok | fails | form |
| a⁴+b⁴+c⁴ ≥ abc(a+b+c) | none found | **ok** | fails | form |
| x³+y³ ≥ x²y+xy² for x,y ≥ 0 | none found | **ok** (8.2 s) | fails | form |
| (x−1)(y−1) ≥ 0 for x,y ≥ 1 | ok | ok | ok | form |
| x+y = 2 ⇒ xy ≤ 1 | none found | **ok** | fails | form |
| x+y+z = 3 ⇒ x²+y²+z² ≥ 3 | ok | ok | fails | form |
| Schur, t = 1 | none found | none found | fails | fails |
| xyz ≥ 0 for x,y,z ≥ 0 | ok | ok | fails | ok |
| Motzkin (not SOS, degree 6) | degree bound | none found — correct | fails | fails |
| (x³−y³)² expanded, degree 6 | degree bound | **ok** | fails | form |
| **Solved** | **12** | **18** | **3** | **1** |

`grind` and `omega` solved none in either run. Mathlib's counts were identical in
both runs. Solved by Forge and no Mathlib tactic: 8, then **14**. Solved by a
Mathlib tactic and not Forge: 0 both times. Data:
[`results/tactic-headtohead-before-search-fixes.json`](../../../results/tactic-headtohead-before-search-fixes.json),
[`results/tactic-headtohead.json`](../../../results/tactic-headtohead.json).

**What the fixes were.** The first run showed Forge's dictionary search missing
textbook sums of squares, for two reasons. It only proposed binomial squares it
could guess from the target's even monomials, so `1 − xy` never led it to
`(x−y)²`; it now offers all of them. And no dictionary proposes a trinomial with
specific coefficients, such as `(x² − 2xy + y²)²` for `(x−y)⁴`; a Gram-matrix
search with exact rational reconstruction (`prototype/forge/gram.py`) now does,
without an SDP solver, and the degree bound rose from 4 to 6. The two problems
still unsolved are the right two: Motzkin's polynomial is not a sum of squares,
and Schur's inequality needs reasoning this certificate family does not express.

**Read before quoting.**
- *`nlinarith` gets no hints, by design.* Given the certificate's squares it
  succeeds (see the earlier comparison), so what this measures is *finding* the
  certificate. Every `nlinarith` failure was a genuine refutation failure in
  under a second, never a timeout.
- *"form" is not a capability result.* `positivity` rejects goals not of the form
  `0 ≤ e`; 14 of its 20 rows are that. On the six it attempted it solved one.
- *Forge is slower when both succeed* — its oracle is a separate Python process —
  and one fixed problem now takes 8.2 s.
- *The problem set was fixed before either run*, but the search was improved in
  response to the first run's failures on that same set. The second run shows
  the fixes work on the problems that motivated them; it is not independent
  evidence of how the search generalises. The held-out run below is.
- *Twenty curated problems, over `Int`, on Lean v4.32 with Mathlib* — the only
  built Mathlib here; Forge's core compiles unchanged on it.

## Held-out run: does it generalise?

Twenty NEW problems, [`bench/tactics/problems_heldout.json`](../../../bench/tactics/problems_heldout.json),
written after the search fixes and **committed and pushed before any tool ran on
them** (commit `0ba7ca4`), with the rule that the search is not changed in
response. They differ from the first set on purpose: Cauchy–Schwarz in three
dimensions (six variables), products of hypotheses, a power of a single
hypothesis (`x ≥ 1 ⇒ x³ ≥ x`), an equality with a nonlinear multiplier
(`xy = 1 ⇒ x² + y² ≥ 2`), degree-6 forms, and Choi–Lam's polynomial as a second
not-a-sum-of-squares probe.

| Tactic | Solved (of 20) |
| --- | ---: |
| `forge_cone?` | **19** |
| `nlinarith`, no hints | 3 |
| `positivity` | 0 |
| `grind`, `omega` | 0 |
| Solved by `forge_cone?` only | 16 |
| Solved by a Mathlib tactic only | 0 |

The one `forge_cone?` failure is Choi–Lam, and for the right reason: "no PSD Gram
matrix reconstructed" — it is not a sum of squares. All 17 `nlinarith` failures
are genuine refutation failures, none a timeout. `positivity` rejected 16 goals
for their form and solved none of the 4 it attempted. The slowest Forge success
took 2.1 s. Every success is a kernel-checked proof (78 failures, 78 errors, no
`sorry`). Data: [`results/tactic-headtohead-heldout.json`](../../../results/tactic-headtohead-heldout.json).

This is the strongest evidence in the repository that the search is useful, and
it is still bounded: twenty problems, curated by the same hand that wrote the
search, over `Int`, degree ≤ 6, six variables at most. It shows the fixes were
not fitted to the first set. It does not show how the search does on problems
drawn from real proofs, which is where Gate 1 has to operate.

## Does Lean already do this?


The first comparison this project has run. Full data in
[`results/lean-tactic-comparison.json`](../../../results/lean-tactic-comparison.json).

| Tactic | `hidden_quadratic` | `equality_constrained` | `guard_product` |
| --- | --- | --- | --- |
| `grind` (core) | fails | fails | fails |
| `omega` (core) | fails | — | — |
| `positivity` | fails | fails | **passes** |
| `nlinarith`, bare | fails | fails | **passes** |
| `nlinarith` + the certificate's squares | **passes** | **passes** | passes |
| `linarith` + the certificate's squares | **passes** | fails | — |

The sharpest row is the last: for `hidden_quadratic`, once the squares are
supplied, plain `linarith` closes it. The certificate is *linear in its
squares*, so no nonlinear search is needed at all.

**Four qualifications, which matter more than the table.**

1. **`grind` is not a baseline for this at all.** It cannot prove `0 ≤ x^2`.
   Nor `0 ≤ x*x`, nor `0 ≤ 3*x^2 + 1`, nor `0 ≤ x*y` from `0 ≤ x` and `0 ≤ y` —
   while it proves a linear control immediately. Its cutsat model treats `x^2`
   as an unconstrained atom and assigns it zero. So a 0/30 score against it on
   the benchmark below measures its *scope*, not the difficulty of the
   problems, and should never be quoted as Forge outperforming it. The tactics
   that do address this territory — `positivity`, `nlinarith`, `polyrith` —
   are in Mathlib, which this development deliberately does not import.
2. **`guard_product` is not evidence.** Bare `nlinarith` and `positivity` get
   it unaided and its certificate is trivial. It is listed so the table is not
   filtered.
3. **The gap is smaller than "with the certificate versus without".** Given
   only *two* of `hidden_quadratic`'s three squares, `nlinarith` still succeeds:
   it manufactures the missing `b²` itself. What was measured is "some of the
   squares" against "none", not "exactly this certificate" against "none".
4. **Two informative goals is a small sample.** This is not a benchmark.

Mathlib measurements are on a v4.32.0 build, the only one available here; the
rest of this repository is v4.34.0.

## Benchmark

36 problems (30 positive, 6 negative controls), generated by
`tools/bench_lean_cone.py` into `Bench.lean`. Full data in
[`results/lean-cone-benchmark.json`](../../../results/lean-cone-benchmark.json).

| | |
| --- | --- |
| Verified by the checker | 30/30 |
| Negative controls correctly rejected | 6/6 |
| Proved unaided by `grind` | 0/30 — but see qualification 1 above |
| Proved unaided by `omega` | 0/30 — it is documented as linear |
| Whole-file elaboration | 11.7 s |
| Axioms across all 96 theorems | `propext`, `Quot.sound` |

The negative controls matter more than the positives: two of them satisfy the
polynomial identity *exactly* while negating the target and a weight, so each
would certify `0 ≤ -p` for a positive-definite `p` if its guard were dropped.

**Kernel cost tracks polynomial size, not coefficient size.** Coefficients
growing by a factor of 2.4 × 10⁸ cost nothing measurable — `Int` bottoms out in
GMP-backed literals. Term count drives it superlinearly: 3 terms ≈ 0.03 s,
26 terms ≈ 0.73 s, about 24× the time for 9× the terms, which is what the
quadratic `insertTerm` in `collect` predicts. A better `collect` is the obvious
first optimisation if one is ever needed.

**What it does not establish.** The certificates were constructed, not found, so
nothing here measures search cost — and search is the expensive half. Random
sums of squares are generically strictly positive, so no instance sits near the
cone boundary. Timings are single runs; two runs of identical work differed by
up to 30%.
