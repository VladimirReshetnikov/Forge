# Lean replay targets — NOT COMPILED

No `lean` or `lake` executable was available in the execution environment. These
files are source-level integration targets; no theorem here is reported as
kernel-checked, no generated script is reported as successfully elaborated,
and there is no implemented `forge` tactic.

The baseline is copied from the reviewed Forge snapshot:
Lean v4.34.0; Mathlib `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`.
A `lake-manifest.json` is intentionally not fabricated. The project must resolve
and build its real dependencies before any compatibility claim is made.

In an environment with this toolchain and network access:

```sh
cd lean
lake update
lake exe cache get
lake build
lake env lean ForgeExtensions/Reachability.lean
lake env lean ForgeExtensions/ReplayExamples.lean
lake env lean ForgeExtensions/GeneratedNC.lean
```

Inspect all `#print axioms` output and the actual compiler return codes. Do not
insert `sorry`, add axioms, disable kernel checking, or weaken a theorem merely
to make a script compile. `GeneratedNC.lean` contains exact integer witnesses
emitted by `prototype/emit_lean.py`; rerunning that emitter is not verification.

`Reachability.lean` needs only Lean core; the two other modules need Mathlib.
`ReplayExamples.lean` supplies local identities and a generic telescoping lemma.
It does **not** prove the complete binomial-square summation theorem or connect
a JSON decoder to the kernel.
