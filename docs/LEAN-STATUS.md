# Lean status

One canonical record. The twenty-seven proposals stated this twenty-seven
different ways under some twenty filenames in several formats; those originals
stay frozen under `proposals/<slug>/results/` and `proposals/<slug>/lean/`.

## The short version

**No proposal compiled any Lean.** All twenty-seven recorded `NOT_RUN` for the
same reason: no `lean` or `lake` executable in the authoring environment.
Consequently none performed a kernel check, an axiom audit, or any comparison
against a Lean tactic. One of them — `r9` — responded by shipping no Lean at
all, saying it "deliberately contains no placeholder theorem files presented as
implemented proofs".

**This merge compiled eighteen files, and one of them failed.** The merge
environment has `elan`, which installed the pinned
`leanprover/lean4:v4.34.0`. Six of the twenty-one files in the merged tree, ten
of the twenty extension-round source files, and two of the third round's three
core-only files elaborate with no errors; eleven of the eighteen print `does not
depend on any axioms` for every theorem they expose.

The third round's remaining core-only file does **not** parse, and it is the
only delivered Lean in twenty-seven proposals that a compiler has contradicted
— because it is nearly the only delivered Lean a compiler has seen.

## What each run recorded

Design round:

| Run | File | Field | Value |
| --- | --- | --- | --- |
| p1 | `results/status.json` | `lean_compiled` | `false` |
| p2 | `results/results.json` | `lean_executed` | `false` |
| p3 | `results/lean_status.json` | `status` | `NOT_RUN`, plus `comparison_to_grind: NOT_PERFORMED` |
| p4 | — | — | in prose only; `experiments.json` carries no Lean field |
| p5 | `results/lean_comparisons.json` | `status` | `not_run`, with pre-declared heartbeats and timeout |
| p6 | `ARTIFACT_STATUS.json` (proposal root) | `lean_examples_compiled` | `false` |
| p7 | `results/lean-status.json` | `status` | `not_run`, with the project path |
| p8 | `results/artifact_validation.json` | `lean_compilation` | `not executed` |
| p9 | `results/lean_status.json` | `status` | `NOT_RUN`, naming the file |

Extension round:

| Run | File | Field | Value |
| --- | --- | --- | --- |
| e1 | `results/lean-status.json` | per-file `status` | `NOT_RUN`, "lake executable unavailable", plus `axiom_audit: NOT_RUN` |
| e2 | `results/summary.json` | `lean_status` | `NOT_RUN_NO_EXECUTABLE` |
| e3 | `results/run.json` | `lean_status` | `NOT_RUN: no Lean executable available` |
| e4 | `results/lean-generation.json` | `status` | `GENERATED_NOT_COMPILED`, 222 identity theorems, `original_source_semantics_bridge: false` |
| e5 | `results/summary.json` | `environment.lean_status` | `NOT_RUN: no Lean executable in this environment` |
| e6 | `results/status.json` | `lean_core_specimens` | `NOT_RUN`; replay targets `NOT_RUN`; integration `NOT_IMPLEMENTED` |
| e7 | `results/results.json` | `metadata.lean_available` | `false`, with `lean_kernel_checked: false` |
| e8 | `lean/status.json` | `status` | `NOT_RUN`, "Lean executable absent" |
| e9 | `results/artifact-qa.json` | `lean_compilation` | `NOT_RUN` |

e4's entry is the most precise of the twenty-seven and the one worth copying: it
distinguishes *generated* from *compiled*, counts what was generated, and
records separately that the bridge from the generated statements back to the
original source semantics does not exist.

## What was compiled here

Lean version 4.34.0, x86\_64-w64-windows-gnu, commit `293d5d0c`.

### The merged tree

Recorded in
[`../results/lean-core-elaboration.json`](../results/lean-core-elaboration.json).

| File | Origin | Result |
| --- | --- | --- |
| `lean/Forge/Design/Runtime.lean` | p3 `DesignAPI.lean` | elaborated, no errors |
| `lean/Forge/Design/Contracts.lean` | p6 `Contracts.lean` | elaborated, no errors |
| `lean/Forge/Examples/Structural.lean` | p9 `Structural.lean` | elaborated; two theorems depend on `propext` |

### The merged closure principles

Recorded in
[`../results/lean-closure-elaboration.json`](../results/lean-closure-elaboration.json).
These three files are the merge's own work rather than any one proposal's: the
ten core-only extension specimens between them contained six spellings of one
reachability theorem and five of one word-fold theorem. Those are proved once
here; the genuinely distinct lemmas are kept and attributed in each file's
header.

| File | Merged from | Result |
| --- | --- | --- |
| `lean/Forge/Closure/Principles.lean` | e1, e2, e3, e4, e5, e6, e7, e8, e9 | elaborated; 8 theorems, none with axiom dependencies |
| `lean/Forge/Closure/Covers.lean` | e8 `CoreSoundness.lean`, tree half | elaborated; 2 theorems, none with axiom dependencies |
| `lean/Forge/Closure/Indexing.lean` | e7 `Specimens.lean`, e8 `IndexingSketch.lean` | elaborated; 2 theorems, none with axiom dependencies |

### The third round

Recorded in
[`../results/lean-round-three-elaboration.json`](../results/lean-round-three-elaboration.json).
Of sixteen Lean sources, thirteen import Mathlib and one proposal ships none,
leaving three.

| File | Result |
| --- | --- |
| `r3/lean/CoreComposition.lean` | elaborated |
| `r7/lean/ForgeQ/Monotone.lean` | elaborated; `iterate_preserves_bound` has no axiom dependencies |
| `r8/lean/RankTelescoping.lean` | **failed**; ten errors |

**The failure, in full.** The file defines `prefix`, which is a reserved
command keyword in Lean 4. All ten errors cascade from that single identifier,
ending in `Unknown constant 'rank_telescoping'` because the theorem above it
never parsed. The mathematics is not wrong: renaming the definition on a
scratch copy makes both theorems elaborate, depending on `propext` and
`Quot.sound` by way of `omega` and `simp`.

The repair was tested outside the repository and is **not** applied to the
archived source. The proposals are frozen as delivered, and the fix belongs in
the merged tree if and when the lemma is adopted. Recording the failure, the
diagnosis and the tested repair together is what keeps a later reader from
mistaking "did not compile" for "is unsound" — or for "compiles".

### The extension proposals

Recorded in
[`../results/lean-extensions-elaboration.json`](../results/lean-extensions-elaboration.json).

| File | Result | Axioms printed |
| --- | --- | --- |
| `e1/lean/Core.lean` | elaborated | — |
| `e2/lean/ForgeExtensions/Reachability.lean` | elaborated | none, 1 theorem |
| `e3/lean/BridgeSpec.lean` | elaborated | — |
| `e4/lean/Reachability.lean` | elaborated | none, 3 theorems |
| `e5/lean/ForgeExtension/Core.lean` | elaborated | — |
| `e6/lean/ProofPrinciples.lean` | elaborated | none, 3 theorems |
| `e7/lean/Specimens.lean` | elaborated | none, 4 theorems |
| `e8/lean/CoreSoundness.lean` | elaborated | none, 3 theorems |
| `e8/lean/IndexingSketch.lean` | elaborated | none, 1 theorem |
| `e9/lean/WordSimulation.lean` | elaborated | none, 2 theorems |

Harness: `tools/check_lean.py --mode elaborate`. It also scans each file for a
`sorry` token independently of the exit code, because `lean` exits 0 on a file
whose declarations are admitted.

## What this does and does not show

**It shows** that the proposed runtime and scheduler contract, the
`CertificateSpec` soundness contract, the Mathlib-free list proofs, the merged
closure principles, and ten extension-round specimens — reachability invariants,
tree covers, fold indexing, ranked calls, word simulation — are well-typed Lean
4.34.0 rather than merely plausible-looking source. Sixteen artefacts that had
never met a compiler now have, and for ten of them the axiom inventory is
empty.

**It does not show** any of the following, and the distinctions matter:

- It is not a transitive axiom audit. Where no `#print axioms` line exists, the
  file's dependencies are simply unknown; where one does, it covers that
  declaration and not the file.
- It says nothing about the thirty-four Mathlib-dependent files across the
  three rounds. Nothing has ever checked them.
- **An uncompiled file is worth what its author's care is worth.** Twenty-six
  proposals ship `.lean` files carrying `#print axioms` commands that were
  never executed. Two of the three that were finally compiled were fine; one
  was not. Before this round there was no way to tell those cases apart, and
  for the thirty-four Mathlib-dependent files there still is not.
- It does not establish that any certificate checker is correct. The contracts
  are *types*; a type is not a proof that an implementation satisfies it.
- It is not a comparison against any Lean tactic. A hand-written example that
  type-checks proves that the example type-checks — not that automation could
  have found it.
- It is not evidence that a `forge` tactic works, because none exists.
- **It does not change what a file says.** `e8/lean/IndexingSketch.lean`
  elaborates, and its author marked it uncompiled *and* not a substitute for the
  original Church-encoded query. Both remain true: it type-checks, and it proves
  an equation between two ordinary-list definitions. The merged
  `Forge/Closure/Indexing.lean` inherits exactly that scope, and says so at the
  top of the file: `churchIndex_encode` is a theorem about `encode xs` for an
  actual finite list, not about every inhabitant of a Church-style type.

## The remaining Mathlib-dependent files

Thirteen in the merged tree, eight in the extension proposals, and thirteen in
the third round. They need a
project with Mathlib built at the pinned revision
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
never against a running compiler, and several were emitted programmatically by a
Python prototype that could not test its own output — e4 alone generated 222
local obligations this way. The remedy for a failure is to fix the script. It is
not to insert `sorry`, and it is not to weaken a positivity condition to make a
check pass — one proposal recorded doing exactly the opposite when a test
disagreed with an exact calculation, and that is the standard to hold.

## Version note

One proposal retrieved the Lean `sos` project's `lean-toolchain` and found it
specifying `v4.32.0-rc1`, against this project's `v4.34.0` baseline. These
projects do not form a build-compatible set by default. Resolve commits and
manifests together before attempting an integration. The extension round repeats
the warning for its own optional dependencies: `ore_algebra`, HolonomicFunctions
and `python-flint` are cited as designed backends, none was installed or
benchmarked, and none is asserted compatible with the pinned toolchain.

No proposal supplied a `lake-manifest.json`, deliberately: none of them built
anything, and a manifest asserting otherwise would have been a fiction. One
extension proposal states the rule explicitly — *no fabricated Lake manifest is
supplied*.
