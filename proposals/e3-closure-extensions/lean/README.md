# Lean status: NOT_RUN

`BridgeSpec.lean` is uncompiled source for generic fold-invariance and transport
lemmas. No Lean executable was available. It is not a tactic implementation,
not a proved sparse-polynomial checker, and not an executed kernel replay.
There are no `sorry` placeholders or added axioms in the specimen; that is a
textual observation, **not** a substitute for compilation or an axiom audit.

Intended validation in a suitable environment:

```
lean +leanprover/lean4:v4.34.0 BridgeSpec.lean
```

Or select that toolchain with elan and invoke `lean BridgeSpec.lean`.
Compilation, a trust-profile audit, source reification, concrete polynomial
replay, and the binomial semantic bridge remain future acceptance gates.
See the article's integration and roadmap sections for exact obligations.
