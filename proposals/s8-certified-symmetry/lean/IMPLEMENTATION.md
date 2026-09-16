# Lean implementation status: NOT IMPLEMENTED / NOT RUN

No executable Lean tactic or reflected Lean checker is delivered, and no Lean compilation was attempted after confirming that no Lean executable was installed in the authoring environment. Python test results must not be upgraded to kernel acceptance.

The article's integration section specifies these proposed modules:

- `Forge/Symmetry/PermArray.lean`: decode to `Equiv.Perm (Fin n)` and prove composition/action compatibility.
- `WordDAG.lean`: original-generator membership by DAG induction.
- `Chain.lean`: checked orbit closure, Schreier residues, exact stabilizers, normal-form bijection, membership and nonmembership.
- `Image.lean`: point-orbit lower bounds and exhaustive coset-cover replay.
- `Families.lean`: exact S_n/A_n recognition, image rules, symbolic counting.
- `Counting.lean`: complete normal-form inventory and Mathlib Burnside instantiation, including singleton cycles.
- `Reynolds.lean`: connected-and-closed monomial orbit certificates, rational orbit averages, invariant-target cone equivalence.
- `Reify.lean`: exact source coordinate/action/hypothesis bridges.

First acceptance gate: compile and kernel-check exact order and both membership polarities for the full small corpus, while rejecting the incomplete S3 chain whose table product is internally correct.

Second gate: bind the finite array theorem to one original Lean source theorem, with generator equivariance evidence. Do not count a theorem about a different reified object as source-goal acceptance.

The public rolling Mathlib documentation was inspected, not compiled against a pinned revision. The concrete documented Burnside theorem is `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`. Mathlib's `Equiv.Perm.cycleType` omits fixed points; the adapter must add one-cycles. Pin and verify the eventual Lean/Mathlib build before relying on module names or theorem signatures.
