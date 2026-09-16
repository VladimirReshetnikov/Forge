# Run history

## Initial exploration

Implemented a breadth-first search over annihilator multiplicity vectors and a
single increasing-order baseline, with independent sparse certificate replay.
The initial accepted corpus produced the same 196/40/44/8/16 lane counts and
1,212-to-288 cofactor reduction. Its summary is retained as
`results/initial-bfs-summary.json`; those earlier certificates predated the new
minimum-receipt schema and are not used as the final replay corpus.

## Algorithmic refinement

Derived and checked the adjacent-exchange argument: increasing cofactor order
suffices for feasibility. Implemented `canonical_search` and exact negative-seed
obstructions. Derived the forced-multiplicity and monotone-zero-count theorems,
then implemented `optimal_ladder` and `check_minimality`. The old BFS remains an
oracle, not the recommended primary implementation.

## Accepted final experiment run

`results/accepted/` records all lanes and all minimum receipts. No failure was
recorded by that experiment run. It reports 624 targeted invalid mutations,
all rejected. The script writes partial records and failure text in a `finally`
block on an experiment exception, rather than silently losing the run.

## Unit and independent diagnostics

22 unittest methods passed. These include a 120-case random BFS comparison.
`oracle.py` passed 200 exhaustive-permutation comparisons, 200 BFS minimum
comparisons, and 200 SymPy derivative comparisons. A separate 100-digit Decimal
calculation lay inside 161 exact rational exponential enclosures.
These are finite diagnostics, not formal proofs.

## A rejected development display call

An exploratory command formatting worked examples passed a SymPy Rational to
`ExpPoly.step`, whose API accepts only Python integers and Fraction values.
It raised `TypeError: coefficients must be integers or Fractions`.
The display command was corrected to construct `Fraction(a, b)`. The checker and
its type boundary were not weakened. This was not a failed mathematical
certificate or a failure in the accepted experiment run.

## Reproduction and formatting

Final standard-library reproduction and PDF checks are summarized in
`results/VALIDATION.md`. Lean compilation and all comparisons to Lean tactics
remain NOT_RUN. Cosmetic code/docstring edits do not alter certificate semantics.
