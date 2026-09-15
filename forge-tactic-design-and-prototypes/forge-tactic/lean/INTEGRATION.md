# Lean integration status

`ReplayExamples.lean` is **uncompiled illustrative material**, not an implemented
`forge` tactic and not an executed comparison against `grind`. No Lean compiler
was available. The actual executed prototype is under `prototype/`.

The mathematical identities have been checked by the Python experiments. The
Lean script elaboration and theorem-name compatibility have NOT been tested.
Use a matching Mathlib project to check them, for example after placing this
file in that project's root:

```sh
lake env lean ReplayExamples.lean
```

The source inspection used Lean v4.34.0 for `Lean.Meta.Tactic.Grind.Action`.
The public manual and Mathlib documentation are mutable. Pin a complete matching
Lean/Mathlib/Aesop dependency set when implementing the design; the archive does
not pretend to supply a tested Lake manifest.

## Recommended first boundary

1. Isolate the original goal and run `grind` with its reserved budget.
2. On failure, create a fresh proof obligation for a candidate arithmetic bound
   or induction lemma. Never insert the candidate as a hypothesis of itself.
3. Replay a successful external certificate into a Lean expression. Check its
   type under the original telescope and reject unresolved proof metavariables.
4. Assert the proved lemma into the original goal and rerun the consumer tactic.
5. When this conservative bridge is stable, adapt the pinned Grind Action / GoalM
   interfaces for incremental propagation. Keep the internal adapter separate.
6. Audit final theorem axioms, replay the generated script in a clean process,
   and compare against both unchanged grind and a simple existing-tactic portfolio.

The proposed `forge`, `forge?`, and `forge replay` commands described in the
article do not exist in this archive. Their syntax is a design proposal.
