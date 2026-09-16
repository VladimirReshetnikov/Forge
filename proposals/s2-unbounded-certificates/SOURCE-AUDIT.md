# Source audit and scope

Audit date: 15 September 2026, America/Los_Angeles.

## Revision anchors

| Repository | Observed head |
|---|---|
| VladimirReshetnikov/Forge | `58ea206bd7ad501b930add568151217bcc7f82a2` |
| VladimirReshetnikov/Leant | `6bf05ad78c467989e68290f2d08bbed40802d485` |
| VladimirReshetnikov/Djex | `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5` |

Heads were read through the connected GitHub interface. Forge's tree and subsequent commit metadata agreed on the same revision. The root Djex revision is not the same thing as Leant's pinned Djex dependency.

## What was inspected

Forge:

- README.md: overview, rounds, implementation/compilation distinctions, quantitative scope.
- recursive tree inventory: file organization and merged/archived separation.
- article/sections/15-conclusion.tex: merged capability inventory and next-milestone assessment.
- article/sections/10-quantitative.tex: full section; exact finite rational models, least-value caveats, explicit probabilistic-pushdown exclusions.
- article/sections/06-closure.tex: source lines 1–240; observable-space closure and opening of the ideal-closure discussion.
- docs/IDEAS-FROM-LEANT-DJEX.md: full review; existing verification-boundary and synthesis lessons.

Neighbors:

- Leant README.md: current overview, source-owned candidate verification, scoped acceptance and remaining priorities. Large connector output was partially truncated; no claim to have read every historical acceptance entry is made.
- Djex README.md: source lines 1–180; engines, typed candidate structures, current capability and priority summary.
- Latest commit metadata for Leant and Djex.

## Excluded as existing work

The report does not claim novelty for the obligation controller, generalization/induction, exact arithmetic certificate architecture, observable-space or ideal closure, finite covers, Kripke countermodels, noncommutative receipts, analytic ladders, finite-state Markov/game/coupling methods, nonprobabilistic pushdown summaries, source-owned typed graphs, or verification receipts. These are already described in the reviewed Forge baseline.

## Scope of the delta claim

The coverability extension is absent from the inspected merged capability inventory; the nonlinear recursive-probability extension directly addresses exclusions in the quantitative section. This is NOT an exhaustive textual absence claim across every original archived proposal. Classical Petri coverability and probabilistic polynomial-system algorithms are attributed to their literature, not claimed as newly invented mathematics.

No prior proposal files are bundled. No source code was pushed to any repository.

## Library discovery

Current Mathlib generated documentation was consulted for `Mathlib.Order.FixedPoints` and `Mathlib.Order.WellFoundedSet`. FLINT official indexed documentation was consulted for `fmpq_mat`, `fmpq_mpoly`, `fmpz_poly_factor`, and `qqbar`. Direct opening of some FLINT pages returned 403; their indexed official documentation supplied the stated API information. SMPT's official repository README supplied the model-checker recommendation.

These are documented implementation candidates, not installed dependencies or compiler-verified API pins. The bibliography gives direct primary-source references. No research PDF was used in place of its accessible HTML/abstract/TeX content.
