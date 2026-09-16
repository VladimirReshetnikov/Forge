# Retained run history

## Preliminary successful corpus: run-01

`results/run-01/` records the first complete successful corpus: 16 universal
one-parameter families, together with the Boolean, matrix, random-source,
two-parameter and witness suites. It contains 96 valid bundles and 944 rejected
mutations. It was superseded, not contradicted, by the expanded final run.

Do not add these numbers to run-02. Most mathematical cases are shared.

## Initial unit-test errors

`results/unit-tests-initial.log` retains two errors in a 24-test unit run. The
tests passed raw characteristic coefficients `[1, 2, 1]` and `[1, -2, 1]` to
`signature_from_signs`, whose API accepts only signs in `{-1, 0, 1}`. The checker
correctly rejected the malformed inputs. The tests were changed to pass signs,
and a new regression confirms rejection of the raw-coefficient misuse.

`results/unit-tests.log` records the resulting 25-test successful suite.
No checker condition was loosened to obtain this result.

## Expanded final corpus: run-02

`results/run-02/` adds the positive-quintic family and two existential outer
problems, one with a witness only on algebraic boundary sections and one with
an impossible count. It records 99 valid bundles and 973 rejected mutations.
The 19 outer problems cover 113 cells, giving 16 true and 3 false expected
verdicts. A false verdict here is an expected semantic answer, not a failure.

`results/run-02/summary.json` contains the exact environment, elapsed time,
per-family dimensions, query counts, compact certificate sizes, and measurements.
`results/run-02-console.log` is the captured runner output.

## Standalone replay

`results/replay-run-02.json` records successful replay with `python -S` and an
import guard refusing SymPy, NumPy, FLINT and the producer. It rechecked all
99 bundles, 748 specialization/count comparisons, 973 mutations, 160 Boolean
fixtures at 4,800 sign assignments, and 90 matrix fixtures.

The producer and replay still share representation and selected admission/outer
routines. This is not complete implementation independence or formal verification.
The evidence is described more precisely in article Section 14.

## Timestamps and comparisons

Raw timestamps are UTC; the experiment date in America/Los_Angeles is
15 September 2026. These local experiments are not pooled with any Forge
repository run. No Lean execution or head-to-head tactic comparison occurred.
