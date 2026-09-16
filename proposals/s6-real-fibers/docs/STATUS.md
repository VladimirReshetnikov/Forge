# Capability and evidence status

The final recorded corpus is `results/run-02`. The article's mathematical
proofs and this ledger refer to the admitted fragment, not arbitrary Lean goals.

| Component | Status | Acceptance still needed for Lean use |
| --- | --- | --- |
| Boolean sign-indicator compiler | Implemented and tested in Python | Reflected syntax, semantics, and compiler-correctness proof |
| Uniform monic triangular quotient | Implemented and tested in Python; mathematical proof in article | Monic tower normal forms, basis, source bridge, specialization theorems |
| Weighted trace matrix construction | Implemented and tested in Python | Checked normal-form/trace computations and finite-algebra bridge |
| Nonreduced Hermite signature theorem | Proved mathematically in article, not formalized here | Lean proof or integration of a suitable existing formalization |
| Newton characteristic-coefficient replay | Implemented and tested in Python | Reflected checker theorem and symmetric-real-rooted signature bridge |
| Uniform count circuits | Implemented and tested in Python | End-to-end soundness theorem against exact source semantics |
| Complete one-real-parameter closure | Implemented and tested in Python | Root-count, coverage, section-sign, sector-sign, and quantifier proofs |
| Concrete univariate algebraic witnesses | Implemented and tested in Python | Root existence/uniqueness, atom-sign replay, source-bound witness construction |
| Multi-parameter uniform circuits | Implemented; two families and 98 rational samples tested | Same count bridge; complete multidimensional closure is not supplied |
| General nonmonic / arbitrary ideal input | Proposed extension only | Certified strata and source-equivalent bases on all strata |
| Leant/Djex refined algebraic provider | Design only | Native provider integration with exact source and universe identity |
| `forge` tactic adapter / source reifier | Design only | Implementation and kernel-checked end-to-end tests |
| Lean benchmark against other tactics | Not run | Pinned comparable source corpus and reproducible Lean evaluation |

The existing Forge snapshot records some earlier core-only Lean elaborations.
That does not mean these newly delivered Python certificates were kernel-checked.
Conversely, this package's `NOT_RUN` status must not be used to erase the existing
repository's earlier elaboration evidence.

Python failure/unknown is not semantic falsity. A returned false outer verdict
has a different contract: replay completely covers the admitted source problem
and checks its quantified Boolean condition on every required cell.

The replay code has practical limits, not hostile-input security qualification.
Read `article/sections/03-algorithms.tex` and the experiment discussion for shared
representation, producer/checker separation, and untested integration boundaries.
