# Implementation status

## Executed

- Exact sparse rational arithmetic and Bernstein coefficient round trips.
- Finite-dictionary LP cone search; exact rational candidate reconstruction.
- Exact symmetric-pivot quadratic sum-of-squares decomposition.
- Exact cone identity, sign, and hypothesis-reference checking.
- Bernstein leaf checking and subdivision-domain coverage checking.
- Tiny typed structural-induction proof generation and replay.
- Recurrence-directed generalization of two accumulator parameters.
- Complete backward demand slicing of finite ground-Horn rules.
- Standalone JSON certificate replay with site packages disabled.
- Negative controls and certificate mutations; 1,680 assertions in total.
- Article compilation and visual PDF inspection.

## Generated but not compiled in Lean

- Direct cone and quadratic inequality proofs over the reals using Mathlib.
- Ordinary proofs of reverse/length accumulator specifications and an energy inequality.
- Proposed API data structures.
- Version-pinned Lake project and a compiler runner that reports actual status.

## Designed, not implemented

- Full Forge tactic and its user-facing syntax.
- Native Lean reification with interpretation theorems.
- Formal proof that the Python certificate checkers correspond to Lean semantics.
- Scoped, cross-engine obligation planner and native grind integration.
- Automatic induction-subject selection and dependent-context motive generalization.
- Invariant synthesis, symbolic witness synthesis, and quantified demand search.
- General SDP/SOS search and equality-ideal multipliers.
- Strict proof-producing SAT replay adapter and external-prover orchestration.
- Persistent theorem indices, learned ranking, concurrent workers, and proof-cost scheduling.
- Real Lean corpus evaluation or head-to-head comparison against grind.

The article distinguishes mathematical correctness arguments for certificate
formats from formal verification of an implementation of those formats.
