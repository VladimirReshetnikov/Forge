# Benchmark notes

The final summary is `results/summary.json`. There are 520 records, 508 distinct
worker/problem pairs, 520 intentionally invalid mutations, five UNKNOWN controls,
and 24 unit-test methods. Do not add finite-prefix checks or inner unittest loops
to the record count. The 50 symbolic records each have 12 finite-prefix checks;
those are not independent proofs of their infinite-horizon claims.

Final outcomes:
- Reachability: 60 exact max certificates, 57 distinct inputs, 53 with a fractional value.
- Runtime: 50 uniform bounds, 49 distinct forward-with-self-loop inputs.
- Transport: 97 exact optima and 83 Hall obstructions, 173 distinct inputs.
- Bisimulation: 40 positives and 80 negatives, 120 distinct inputs; all negatives
  start with matching observations and contain nonempty deletion traces.
- Contraction: 40 local-bound certificates and 20 rate obstructions, 59 distinct inputs.
- Symbolic cost: 50 potentials, all distinct; jumps -1, 0, +1 and degree at most five.

A pilot corpus was recognized as too easy: reachability lacked rejecting sinks,
negative bisimulation could end at immediate observation mismatch, and symbolic
cases repeated too few parameters. The final generator fixes those issues. The
pilot summary is retained but is not part of the final replay corpus. It is not a
second independent experiment to be pooled with the final results.

All input sizes are tiny. Positive bisimulation cases are state relabelings,
contraction cases use reset/stay kernels and a discrete metric, and runtime cases
have forward transitions with optional self-loops. These are algorithmic checks,
not a representative user-problem benchmark or a scaling study.

The transport oracle enumerates integer contingency tables after scaling rational
marginals. Reachability uses bounded-polytope vertices and Cramer's rule. Bisimulation
uses partition refinement. Symbolic costs use explicit finite-distribution evolution
and exact telescoping. These are independent application algorithms but share the
Python runtime and standard-library Fraction arithmetic.

Mutation rejection is targeted, not comprehensive: target boundary values, unit
cost potentials, joint marginals (including an exact 1e-30 perturbation), Hall
strict deficits, witness counts, deletion indices, and potential boundary values.
A mathematically valid weakening of an upper bound is not counted as a defect.

Timings use perf_counter_ns, one local run, with oracle time excluded. No confidence
intervals, process-isolated microbenchmarks, or cross-machine performance claims
are made. Replay prohibits producer and oracle imports and runs with site packages
disabled. Unit tests also run under Python -O to ensure check conditions are not
implemented as removable assert statements.
