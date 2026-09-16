# Evidence and implementation status

## Implemented and executed

- Mixed strict/non-strict rational Fourier–Motzkin projection, exact feasibility, contradiction multipliers, multiple-output lifting, and rational parameter counterexamples.
- Independent projection checker: combination identities AND complete lower/upper-pair coverage.
- Hash-consed min/max witness DAG extraction, evaluation, and diagnostic Lean-style rendering.
- Noncommutative sparse word arithmetic, traced reduction, overlap and inclusion completion, and direct two-sided ideal replay.
- Rational exp/log/sin/cos bounds, arithmetic interval ASTs, exact coverage trees, symbolic differentiation, exact anchor evaluation, vanishing jets, and bounded automatic anchor/order selection.
- Independent analytic checker with separately implemented derivative rules and coefficient recurrences.
- Deterministic experiments, stored certificates, mutation controls, search-blocked independent replay, exact differential oracles, and a unit suite.
- Optional numerical sanity checks, outside acceptance.

## Mathematical arguments in the article

- Exact mixed one-variable projection and constructive lifting.
- Completeness of the unbounded rational-affine conjunction algorithm.
- Four-corner impossibility of an affine witness and validity of a max witness.
- Soundness of original-relation noncommutative identities.
- Elementary rational tail bounds, interval-tree soundness, and exact-jet nonnegativity.
- Robust completeness of idealized fair interval search for strictly positive admitted expressions on compact domains with domain margins.
- A future operator-exponential approximation target with an explicit norm remainder bound.

These are ordinary mathematical proofs in the report, not formalized Lean proofs.

## Written but not compiled

- `lean/CoreComposition.lean`: logical witness/contract composition specimens.
- `lean/SourceExamples.lean`: source-level corner-witness and associativity examples.
- `results/corner-witness-uncompiled.lean.txt`: presentation of an extracted witness DAG.

No Lean or Lake executable was available in this environment. None of these files is a kernel-acceptance receipt.

## Designed, not implemented

- A Lean tactic named `forge`, and its actual obligation-broker adapters.
- Source-to-AST reifiers and source-level interpretation proofs.
- Reflected Lean checkers and their soundness theorems.
- General Boolean or alternating-quantifier real synthesis.
- Integer use of the new real midpoint worker (intentionally not allowed).
- A GAP/GBNP producer adapter.
- Shared noncommutative proof DAG replay at production scale.
- Multivariate analytic certificates, full polynomial Taylor-model arithmetic, algebraic anchors, and range-reduction libraries.
- A normed-algebra series bridge for the operator approximation example.
- Actual integration into Leant or Djex.
- A corpus-level or head-to-head Lean tactic benchmark.
- Hostile-input hardening, process isolation, and complete resource accounting.

## Acceptance gates

The article gives lane-specific gates. An affine-only witness does not close the polyhedral gate; a hand-written source proof bypassing the checker does not validate analytic replay; a claimed Gröbner basis without an original-relation identity does not close noncommutative replay. Negative polyhedral receipts may be source-level refutations only with an exact parameter/premise bridge, not a lossy atom abstraction.
