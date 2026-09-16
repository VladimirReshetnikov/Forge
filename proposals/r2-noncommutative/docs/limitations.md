# Deliberate limitations

The search and checking mathematics is explained in the article. The executable
scope is narrower than all mathematical extensions suggested there.

1. No Lean tactic, source reifier, reflected checker theorem, kernel acceptance,
   or integrated Forge benchmark was produced. The six Lean targets are NOT_RUN.
2. Homogeneous relation completeness is an uncapped theorem. Actual column,
   ambient dimension, matrix dimension, and replay budgets can return no result.
3. Inhomogeneous equality search is bounded. The quotient countermodel producer
   refuses inhomogeneous relations. A failed bounded search is UNKNOWN.
4. Algebra countermodels do not have to be self-adjoint, positive, or a requested
   fixed dimension. They refute only the universal-algebra problem schema.
5. The homogeneous Gram producer constructs exact squares; a negative Gram
   result does not produce a self-adjoint matrix countermodel or Lean negation.
6. General positivity search uses finitely many rays and capped support
   enumeration. No numerical SDP or general NC completion backend was invoked.
7. The finite-ray search and graph proposer use self-adjoint atom interpretations.
   The homogeneous Gram producer/checker also support paired star atoms.
8. The operator producer requires syntactic self-adjointness. Conditional
   self-adjointness must be proved separately, as in the CHSH worked derivation.
9. The trace SEARCH currently excludes equality relations. The trace CHECKER
   supports equality terms, for use by a future producer.
10. Incidence slicing happens after full column construction. The measured
    improvement is not a lazy-word enumeration result.
11. Only same-algebra words are implemented. Rectangular matrix shapes and
    noncentral coefficients are not silently erased or coerced.
12. Source-goal identity, opaque production receipts, cancellation, sandboxing,
    and hostile JSON hardening are integration requirements, not Python features.
13. Timings are single observations on deliberately small generated families.
    Metamorphic permutations and multiple obligations from one example are not
    independent theorem-proving benchmark successes.

The intended next milestone is a small, pinned, source-level Lean acceptance
suite, not an increase in generated Python example counts.
