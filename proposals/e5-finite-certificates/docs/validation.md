# Validation ledger

The recorded run is in results/summary.json. Counts apply to this archive alone.

- 59 problem instances: 38 certificate successes, 17 concrete counterexamples,
  and 4 correctly reported bounded unknowns.
- 38 certificates replay in a checker that imports no search code or SymPy.
- 17 counterexamples replay using independent Fraction-based matrix/polynomial
  evaluation in the same checker module.
- `python -S prototype/checkers.py results/certificates results/counterexamples`:
  55 bundles accepted, site packages disabled.
- 818 individual coefficient/entry perturbations, all rejected. This is an
  exact finite mutation corpus, NOT evidence against all possible forgeries.
- 117 pytest items pass, including 60 internal random sparse-polynomial
  arithmetic differential trials. Test items, mutations, input instances,
  numerical observations and bundles are different units.
- Search timers run once. Checker timers are medians of five warm invocations.
  Parsing/process startup/import costs and Lean costs are NOT measured.
- NO Lean executable was available. All supplied Lean files are uncompiled
  source specimens. No kernel proof, axiom audit, live tactic, or head-to-head
  tactic comparison is claimed.

## Preserved development failures

1. diagnostic-01-invalid-fixture.log: a random matrix pair was labeled negative
   without a guarantee. Search correctly returned a certificate. The fixture
   generator was repaired to force a nonzero observed one-step output, and a
   separate noncommuting two-action fixture tests word orientation.
2. diagnostic-02-template-limit.log: the first binomial moment-3 expectation was
   too optimistic for r-degree <=4. The smaller-template UNKNOWN was retained as
   an explicit case; a separately named successful case permits r-degree <=6.
   The same controlled distinction is included for squared-binomial moment 2.
3. diagnostic-03-test-collection.log: a closing-bracket syntax error in the test
   decorator prevented collection; no tests were represented as passing.
4. diagnostic-04-overstrong-test-assertion.log: a test incorrectly required both
   recurrence coefficients to vanish at n=0. Only the leading coefficient needs
   to vanish; the other coefficient multiplies the zero initial sequence value.
   Removing that false auxiliary assertion preserves the actual nonuniqueness
   control (two different sequences satisfying the recurrence and first seed).

These diagnostics do not count as accepted runs. The final code and accepted
run are the reproducibility target. Earlier complete intermediate source trees
are not archived, so the failure logs are diagnostic records, not replay bundles.

## Resource boundary

Checker parsing rejects duplicate keys, floats, bool-as-integer, noncanonical
rationals, duplicate monomials, bad dimensions and excessive declared sizes.
Intermediate polynomial limits are checked, but neither search nor checker is a
hardened adversarial sandbox. SymPy calls are not preempted by internal budgets;
production needs process-level time/memory isolation. This prototype's scope is
exact mathematical certificates for well-formed research workloads.
