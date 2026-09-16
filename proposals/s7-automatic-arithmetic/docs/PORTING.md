# Lean port: proposed, not executed

No `.lean` scaffold is included merely to make the package look implemented. There was no Lean executable in the working environment, and neither reflection nor a tactic adapter was compiled. The article's Section 6 provides the detailed module contracts.

## Dependencies to inspect and pin

Use Mathlib's `Mathlib.Computability.DFA` and `Mathlib.Computability.NFA` as semantic foundations, plus Lean's exact integers and finite data. `NFA.toDFA_correct` supplies an existing language-level determinization theorem; a finite-table bridge is still required.

Sheng's `Aeacu2/Automata` has a `project_iff` theorem connecting corrected projection with existential number quantification. Its inspected commit pins Lean 4.23.0; the reviewed Forge baseline records Lean 4.34.0. Its leading-zero/digit-order conventions differ from this prototype's least-significant-first zero suffixes. Reuse requires a build/source audit and either matching encodings or a proved transport, not blind imports. Walnut is a potential proposer/differential oracle, not Lean proof evidence.

## Ordered acceptance gates

1. Prove binary encoding, zero suffixes, and carry invariants on the original natural-number semantics, including negative coefficients and floor division.
2. Prove exact tail ranks plus closed complement, subset semantics, and existential correctness. Compile the empty-input hidden-witness case and `forall x, exists y, y = 2*x+1`.
3. Reify real Lean expressions with proof bridges; replay the original alternating cut, division by 17 and the correct/incorrect coin thresholds. Inspect final theorem axioms; no `sorry` or new axiom.
4. Prove powers-of-two and popcount bridges; implement and verify the witness dynamic program and least-choice theorem; evaluate the large inputs within Lean.
5. Only then measure against native tactics on the original statements, using matched trust profiles and budgets. A bounded bit-vector substitute is not the same query.

Proposed modules: `Encoding`, `Table`, `Atoms`, `Receipts`, `Quantifiers`, `Check`, `Witness`, `Reify`, `Tactic` under `Forge/Automatic/`.

## Do not substitute near misses

A theorem about abstract words is not an original-Nat-query proof. An accepted Python certificate is not kernel verification. An accepted graph is not yet a synthesized executable Lean function. A witness tuple is not an alternating strategy. Signed coefficient arithmetic is not `Nat.sub`. A root statement read from the certificate is not the caller's expected goal. `native_decide` must not silently change a required trust policy.

## Next producer algorithms

The article specifies block existential projection (one tail closure and determinization per hidden block), support-based alphabet reduction with comap receipts, freshness-justified miniscoping, conditional minimization, bitmap subsets, and suffix-formula compilation for alternating strategies. They are not counted as executed features.
