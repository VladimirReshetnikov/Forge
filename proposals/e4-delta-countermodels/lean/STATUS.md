# Lean evidence status: NOT COMPILED

No Lean, Lake, or Elan executable was available in the execution environment.
No Lean acceptance, kernel validation, or successful axiom audit is claimed.

- `Reachability.lean`: authored proof text for three generic induction bridges.
- `WorkedFold.lean`: authored relational fold proof illustrating one integration route.
- `GeneratedIdentities.lean`: 222 generated **local** polynomial identity
  obligations from the 37 positive machine certificates.

The generator is `../emit_lean.py`. The machine certificate has been replayed by
Python before emission, but that does not establish that the emitted Lean source
elaborates. The original-source-to-machine semantics bridge remains unimplemented.
Even successful compilation of all local identities would not complete that bridge.

Each file includes `#print axioms` directives for later auditing. No placeholder
axioms or `sorry` are supplied as substitutes for actual proofs. Their absence is
not itself a kernel check.

In an existing pinned Mathlib project, execute (with actual absolute paths):

```sh
lake env lean /absolute/path/to/Forge_Delta/lean/Reachability.lean
lake env lean /absolute/path/to/Forge_Delta/lean/WorkedFold.lean
lake env lean /absolute/path/to/Forge_Delta/lean/GeneratedIdentities.lean
```

Keep compiler logs and failures as separate evidence. The article's first
acceptance gate additionally requires composing identities with induction and
proving the original source theorem, plus the actual negative source execution.
