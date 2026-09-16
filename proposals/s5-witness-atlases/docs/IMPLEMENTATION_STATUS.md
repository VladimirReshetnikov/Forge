# Implementation status

## Executed Python capabilities

Exact sparse source identities; derivative and pair Bézout receipts with expected
coverage; rational square-free projection; complete rational base root covers;
localized algebraic coefficients at selected roots of reducible polynomials;
exact exceptional-fibre specialization; degree drops, zero factors and repeated
roots; complete fibre root covers; Boolean sign tables; both quantifier folds;
free-parameter truth sets; root-index selector serialization; source-independent
standard-library replay; targeted corruptions; differential and metamorphic tests.

## Mathematical specification, not a formalization

The article supplies proofs of guard soundness, root persistence, sign-invariant
stacks, complete-atlas quantifier semantics, strategy extraction, and completeness
of the uncapped mathematical procedure. Python correctness is not proved in Lean.

## Not implemented

Lean polynomial reifier; reflected Lean arithmetic and Sturm checker; Lean
geometric proof; complete source-goal proof reconstruction; instantiated
CertificateSpec.sound; actual forge tactic hook; root-index-to-Lean elaboration;
Leant/Djex host loop; local covering optimization; polarity-directed certificate
slicing; FLINT/LibPoly backend; arbitrary algebraic towers; general multivariate CAD.

The two Lean composition specimens explicitly assume a cover and cellwise
correctness and were not compiled. No old Forge component was replaced or rerun.

## Resource behavior

Arithmetic refinement/node limits raise LimitExceeded. Other representation caps
reject the attempted input/certificate without a mathematical false verdict.
SymPy factorization is outside these counters. This is not hostile-input hardened.
