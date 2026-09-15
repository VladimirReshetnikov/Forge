# Lean status

One canonical record. The nine proposals stated this nine different ways under
five filenames in two formats; those originals stay frozen under
`proposals/<slug>/results/`.

## The short version

**No proposal compiled any Lean.** All nine recorded `NOT_RUN` for the same
reason: no `lean` or `lake` executable in the authoring environment.
Consequently none performed a kernel check, an axiom audit, or any comparison
against a Lean tactic.

**This merge compiled three files.** The merge environment has `elan`, which
installed the pinned `leanprover/lean4:v4.34.0`. Three of the sixteen files in
the merged tree import nothing beyond Lean core and elaborate with no errors.

## What each run recorded

| Run | File | Field | Value |
| --- | --- | --- | --- |
| p1 | `results/status.json` | `lean_compiled` | `false` |
| p2 | — | — | in prose and `results.json` |
| p3 | `results/lean_status.json` | `status` | `NOT_RUN`, plus `comparison_to_grind: NOT_PERFORMED` |
| p4 | — | — | in prose and `experiments.json` |
| p5 | `results/lean_comparisons.json` | `status` | `not_run`, with pre-declared heartbeats and timeout |
| p6 | `results/ARTIFACT_STATUS.json` | `lean_examples_compiled` | `false` |
| p7 | `results/lean-status.json` | `status` | `not_run`, with the project path |
| p8 | `results/artifact_validation.json` | `lean_compilation` | `not executed` |
| p9 | `results/lean_status.json` | `status` | `NOT_RUN`, naming the file |

## What was compiled here

Lean version 4.34.0, x86\_64-w64-windows-gnu, commit `293d5d0c`. Recorded in
[`../results/lean-core-elaboration.json`](../results/lean-core-elaboration.json).

| File | Origin | Result |
| --- | --- | --- |
| `lean/Forge/Design/Runtime.lean` | p3 `DesignAPI.lean` | elaborated, no errors |
| `lean/Forge/Design/Contracts.lean` | p6 `Contracts.lean` | elaborated, no errors |
| `lean/Forge/Examples/Structural.lean` | p9 `Structural.lean` | elaborated, no errors |

Harness: `tools/check_lean.py --mode elaborate`. It also scans each file for a
`sorry` token independently of the exit code, because `lean` exits 0 on a file
whose declarations are admitted.

## What this does and does not show

**It shows** that the proposed runtime and scheduler contract, the
`CertificateSpec` soundness contract, and the Mathlib-free list proofs are
well-typed Lean 4.34.0 — not merely plausible-looking source. Three design
artefacts that had never met a compiler now have.

**It does not show** any of the following, and the distinction matters:

- It is not a transitive axiom audit. Elaboration succeeding says nothing about
  what the declarations depend on.
- It says nothing about the other thirteen files, which import Mathlib.
- It does not establish that any certificate checker is correct. The contracts
  are *types*; a type is not a proof that an implementation satisfies it.
- It is not a comparison against any Lean tactic. A hand-written example that
  type-checks proves that the example type-checks — not that automation could
  have found it.
- It is not evidence that a `forge` tactic works, because none exists.

## The remaining thirteen

They need a project with Mathlib built at the pinned revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`.

```bash
cd lean
lake update
lake exe cache get
lake build
```

Or against a Mathlib project you already have:

```bash
python tools/check_lean.py --mode lake --project /path/to/mathlib-project lean
```

Expect failures. These scripts were written against an inspected source tree,
never against a running compiler, and several were emitted programmatically by
a Python prototype that could not test its own output. The remedy for a failure
is to fix the script. It is not to insert `sorry`, and it is not to weaken a
positivity condition to make a check pass — one proposal recorded doing exactly
the opposite when a test disagreed with an exact calculation, and that is the
standard to hold.

## Version note

One proposal retrieved the Lean `sos` project's `lean-toolchain` and found it
specifying `v4.32.0-rc1`, against this project's `v4.34.0` baseline. These
projects do not form a build-compatible set by default. Resolve commits and
manifests together before attempting an integration.

No proposal supplied a `lake-manifest.json`, deliberately: none of them built
anything, and a manifest asserting otherwise would have been a fiction.
