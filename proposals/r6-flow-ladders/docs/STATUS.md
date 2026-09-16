# Capability status

## Implemented and executed

- Dense exact rational exponential-polynomial arithmetic.
- A separate sparse arithmetic implementation for certificate replay.
- Canonical increasing-order ladder feasibility.
- Binary-search minimum ladder construction in the input-spectrum,
  coefficient-positive-polynomial-terminal grammar.
- Exact grammar obstruction and minimum-zero-factor receipts.
- A bounded breadth-first reference search and a reverse-order ablation.
- Constant rational Metzler row synthesis for supplied residual vectors.
- Rational Taylor-tail exponential enclosures and interval propagation.
- Rational negative-point discovery and checking.
- Endpoint-plus-derivative-cover certificates of unique roots in supplied brackets.
- Search-free replay under `python -S`.
- Unit, mutation, random, exhaustive-small-instance, symbolic, and numeric checks.

## Mathematically proved in the article, not formalized here

- Scalar cofactor soundness and ladder soundness.
- Adjacent exchange, canonical completeness for the stated grammar.
- Forced nonzero multiplicities, monotone zero count, minimum length.
- The nonzero ladder's strict-positive-on-the-open-ray property.
- Positive-system invariance (including continuous variable matrices).
- Exact exponential-tail enclosure and interval-root soundness.

## Designed, not implemented

- A Lean reifier and a proof of equality to the original source expression.
- Reflected Lean checkers and their denotation soundness theorems.
- Kernel-checked acceptance of any Flow certificate.
- Automatic discovery of useful vector residual banks.
- Variable-matrix positive-system synthesis.
- General rational-anchor positivity, arbitrary elementary-function reification,
  symbolic parameters, and multidimensional analytic certificates.
- A computational real-number representation of a root from nested brackets.
- The actual `forge` tactic or its connection to this worker.
- A real Lean corpus comparison or any speedup against existing tactics.

`lean/FlowTargets.lean` contains proposition definitions only. No statement in it
has been proved by this package, and the file has not been compiled here.

The Python records distinguish language obstruction, point refutation, positive
certificate, root certificate, and unknown. They are not interchangeable.
