# Lean replay source -- exported, not compiled here

This directory contains **no implementation of the proposed `forge` tactic**.
It contains ordinary Lean/mathlib source generated from Python-checked exact
certificates: 9 inequality proofs and 49 recurrence-invariant proofs, plus a
generic induction lemma for iteration. Neither compilation nor Lean kernel
checking was performed in the authoring environment, which had no Lean/Lake
runtime. Syntax, theorem-name, or dependency integration fixes may be required.

The target is Lean 4.34.0 with the exact mathlib revision in lakefile.toml.
This pairing was read from the upstream toolchain/repository on September 14,
2026 (America/Los_Angeles); it is not a claim of a successful build.

With Lean/Lake and network access:

```sh
lake update
lake exe cache get
lake build
```

Then, from the parent directory:

```sh
python scripts/run_lean_comparisons.py --timeout 30
```

The comparison script uses the 9 successful certificate contexts as smoke tests
for existing tactics. It is not an unbiased benchmark and does not execute a
Forge tactic. Nonzero exits retain full compiler diagnostics and are not
silently classified as proof-search failures. Startup/import time is included.
The repository-scale controlled evaluation specified in the article remains to
be implemented.

No `sorry`, new axioms, or `native_decide` are used in the generated source.
That static property is not a substitute for compiling and auditing its proofs.
