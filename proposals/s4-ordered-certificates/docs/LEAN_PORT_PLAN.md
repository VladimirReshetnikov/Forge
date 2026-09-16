# Lean port: required new work and acceptance gates

No Lean source is delivered as compiled in this package. Proposed module names
below are a work breakdown, not names of existing Forge modules or APIs.

## Keep the first trusted theorem independent of WQO search termination

`Forge/Ordered/Region.lean` should prove:

    check(model, certificate) = true ->
    forall state,
      (exists final, reaches(model, state, final) and bad(model, final))
      iff above_some_final_basis(certificate, state)

Split this proof into earlier-child DAG lower inclusion and all-transition
backward-closure upper inclusion. Require exact target coverage. The checker
must enumerate the full required transition/basis pair set itself.

## Arithmetic implementation sequence

1. Represent finite controls, dimensioned natural vectors and matrices.
2. Define the explicitly guarded update `x >= a; A(x-a)+b`.
3. Prove upward compatibility under the guard, without erasing natural monus.
4. Prove the exact diagonal predecessor rule.
5. Prove the coordinate clipping lemma using `A[j,i]*cap[i] >= demand[j]`.
6. Prove the integer partition constructors sound, first direct global coverage,
   then local-minimum coverage.
7. Prove executable replay acceptance implies the semantic premises.

## Queue implementation sequence

1. Finite alphabets as actual finite types; words as lists.
2. Prove preloss/action/postloss equivalence to the direct subsequence relations.
3. Prove exact single-symbol send, receive and tau predecessors.
4. Prove concrete trace replay respects deletion directions and FIFO head access.
5. Add the reliable-to-lossy *safety-only* simulation as a distinct bridge.

## Source bridges and permissions

Exact quotienting requires lifting abstract steps from every represented source
state, not merely proving that each quotient edge has some concrete realization.
A forward simulation plus inclusion of bad states is enough for safety transfer;
it is not enough to transfer abstract failures. Original-source concrete replay
can separately establish a failure. Preserve these three permission levels.

Begin with explicit models and user-supplied semantic bridge theorems. Add an
automatic source reifier only after this path has accepted the unchanged original
statements. Handle every inductive transition constructor and distinguish
simultaneous old-state updates from sequential assignments.

## Reuse available infrastructure

Target the reviewed Forge baseline first: Lean 4.34.0 and Mathlib
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`. Online Mathlib documentation confirms
WQO/finite-product/Higman infrastructure in `Mathlib.Order.WellFoundedSet` and
`Mathlib.Order.WellQuasiOrder`; exact imports at the pinned dependency must be
compiler-tested. The finite checker soundness theorem needs no WQO import.
Use existing Forge runtime/receipt and arithmetic routing rather than another
controller architecture.

## Acceptance conditions

- Original semaphore relation, unchanged initializer `(N,0,1)` with arbitrary
  natural `N`, and a source bridge are all covered by one compiled theorem.
- The broken-enter variant yields an independently replayed source execution.
- Dense-8 direct coverage is kernel-checked without materializing its local minima.
- FIFO send-loop and two-channel examples preserve actual source controls/channels.
- A reliable `ba` queue with only `recv a` is NOT refuted by the lossy witness.
- Exact-word targets, zero tests, negative coefficients and erased payload
  distinctions are refused or carry an explicit weaker semantic contract.
- Mutation corpus failures are enforced by the Lean checkers, not just Python.
- Check axiom inventories, exact original-goal binding and completion under the
  existing Forge acceptance policy. A postulated checker-soundness axiom or an
  easier restated theorem does not satisfy acceptance.

## Later work

Formalize WQO completeness separately, then implement sparse factorization,
dominance indexes and optional untrusted external producers. Benchmark source
reification, search, certificate size, kernel replay and residual solving
separately. Compare unchanged original statements with equal supplied-lemma
budgets; do not credit a model-equivalence theorem to only one side for free.
