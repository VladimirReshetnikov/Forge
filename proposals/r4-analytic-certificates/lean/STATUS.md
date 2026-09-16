# Lean status

**Generated, not compiled.** There is no Lean executable in the execution
environment. No claim of successful elaboration, kernel checking, axiom auditing,
or a working `forge` tactic is made for these files.

`LadderBridge.lean` is a complete candidate proof of the integrating-factor
step, written against inspected Mathlib derivative/monotonicity APIs. Four
additional files are emitted from separately checked Python certificates.
They demonstrate proof construction without an external solver or a bespoke
trusted analytic oracle. They must be compiled and repaired, without changing
the statements, before being treated as proofs.

The emitted theorems state **nonnegativity**; some Python receipts certify
strict positivity as well. Those weaker candidate Lean conclusions are not
claimed to close the stronger source requests.

Intended baseline (reported by the audited Forge snapshot):
- Lean `leanprover/lean4:v4.34.0`
- Mathlib `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`

There is no claim that moving latest documentation and that pin have identical
module boundaries. Compile the bridge first in the pinned Mathlib project.
Place these files at the project root, then, for example:

```text
lake env lean -o LadderBridge.olean LadderBridge.lean
lake env lean taylor_04.lean
lake env lean entropy_positive_chart.lean
lake env lean log_lower_rational_chart.lean
lake env lean ghost_eps_1.lean
```

Every file requests an axiom inventory with `#print axioms`. The output must be
recorded when the files are actually compiled. Nothing in this archive supplies
that output or substitutes Python replay for it.
