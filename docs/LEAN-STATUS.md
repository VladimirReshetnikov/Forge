# Lean status

One canonical record. The thirty-six proposals stated this thirty-six different
ways under some twenty-five filenames in several formats; those originals stay
frozen under `proposals/<slug>/results/` and `proposals/<slug>/lean/`.

## The short version

**No proposal compiled any Lean.** All thirty-six recorded `NOT_RUN` for the
same reason: no `lean` or `lake` executable in the authoring environment.
Consequently none performed a kernel check, an axiom audit, or any comparison
against a Lean tactic. All three of those have now been done here — see **The
checker** below, which is now most of Gate 2 of the design. One of them — `r9` — responded by shipping no Lean at
all, saying it "deliberately contains no placeholder theorem files presented as
implemented proofs".

**Three of these files are now a checker rather than a specimen.** Until this
point every Lean file in this repository stated what a checker would have to
prove. `Forge/Checker/{Poly,Cone,Corpus}.lean` is one: a total `Bool`-valued
`Cert.check`, a proof `Cert.sound` that accepting implies the polynomial really
is nonnegative on the constrained set, and the prototype's own certificates run
through it and accepted by the Lean kernel. Core Lean only; `decide`, not
`native_decide`; `propext` and `Quot.sound` and nothing else.

`ForgeCore` also now **builds as a library** — nine modules with real imports —
rather than only elaborating file by file.

**This merge compiled thirty-nine files, and two others failed.** The merge
environment has `elan`, which installed the pinned `leanprover/lean4:v4.34.0`.
This repository holds 101 `.lean` files. **40 of them are Mathlib-free** — not
merely free of a direct `import Mathlib`, but free of one anywhere in their
dependency cone — and **39 of those 40 elaborate with no errors**. Twelve print
`does not depend on any axioms` for every theorem they expose.

Regenerate these figures with `python tools/lean_inventory.py` rather than
copying them; three counts on this page were wrong at some point today because
they had been derived by hand and carried forward.

| Where | Mathlib-free | Elaborate |
| --- | ---: | ---: |
| Merged tree (incl. `ForgeCore` and `AxiomAudit`) | 8 | 8 |
| **`Forge.Checker` (new)** | **14** | **14** |
| Design-round proposals `p1`–`p9` | 3 | 3 |
| Extension proposals `e1`–`e9` | 10 | 10 |
| Third round `r1`–`r9` | 3 | 2 |
| Fourth round `s1`–`s9` | 2 | 2 |
| **Total** | **40** | **39** |

The transitive reading matters and the earlier figures did not use it. They
counted 48 files as importing Mathlib directly and 11 as importing a sibling,
and filed the second group with the unchecked. But a file importing a sibling
that is itself Mathlib-free is Mathlib-free: `Forge/Checker/Cone.lean` imports
`Forge/Checker/Poly.lean` and nothing else. Transitively the split is 28
Mathlib-free, 58 Mathlib-dependent, 3 lakefiles.

The three design-round proposal files are a late correction: every round's scan
covered the merged tree and that round's own proposals, and no round went back
over `p1`–`p9`'s own `lean/` directories. `p3/DesignAPI.lean`,
`p6/Contracts.lean` and `p9/Structural.lean` import only `Lean` and all three
elaborate — while each carries a header saying it was not compiled, which was
true of its authoring environment and is false of this one.

**A broken file that prints a clean axiom line.** `r8`'s file exits 1 with ten
errors — and its last line of output is
`'ForgeAP.prefix_bounded' does not depend on any axioms`. Lean recovers from
parse errors and keeps going, so the `#print axioms` command on a declaration
that did elaborate still ran. Any tool that greps for that phrase without
checking the exit code reads this file as clean; this repository's own sweep
script did, counting 13 files where 12 elaborated, which is how the case was
found. **The figure quoted everywhere here is 12**, counting only files that
also compiled.

**Two files fail, not one.** `r8/RankTelescoping.lean` defines `prefix`, a
reserved keyword. And `r6/FlowTargets.lean` puts a module docstring above its
`import Mathlib`, which is a parse error in Lean 4 whether or not Mathlib is
present — verified by a four-line reproduction using `import Init`. `r6`'s was
missed by every earlier scan because it imports Mathlib and so sat in the
never-checked bucket.

**The candidate Lean shrank by a factor of thirty across four rounds.**

| Round | Source files | Lines |
| --- | ---: | ---: |
| Design `p1`–`p9` | 21 | 3,022 |
| Extension `e1`–`e9` | 20 | 3,144 |
| Third `r1`–`r9` | 16 | 755 |
| Fourth `s1`–`s9` | **2** | **98** |

It did not shrink because the proposals got smaller. `r9` argued that an
uncompiled theorem file is not evidence and shipped none; a compiler then found
that another round-three file did not parse. By round four, four proposals ship
no `lean/` directory at all and three ship one containing only an obligation
document — three of them saying, in nearly the same words, that the directory
"deliberately contains no `sorry`-based or uncompiled theorem file presented as
a completed implementation".

The third round's remaining core-only file does **not** parse, and it is the
only delivered Lean in thirty-six proposals that a compiler has contradicted
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

e4's entry is the most precise of the thirty-six and the one worth copying: it
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

### The checker

`Forge/Checker/` is the first thing in this repository that is a checker rather
than a description of one.

| File | Status |
| --- | --- |
| `Forge/Checker/Poly.lean` | elaborates; no axioms beyond `propext`, `Quot.sound` |
| `Forge/Checker/Cone.lean` | elaborates; `Cert.sound` proved |
| `Forge/Checker/Corpus.lean` | elaborates; generated, 3 real certificates accepted |
| `Forge/Checker/Bench.lean` | elaborates in 11.7 s; 36 generated problems, 6 of them negative controls |
| `Forge/Checker/Reify.lean` | elaborates; `eval_toPoly` proved (`propext` only) |
| `Forge/Checker/Tactic.lean`, `TacticTest.lean` | elaborate; `forge_cone`, `forge_reify`; review regressions pinned |
| `Forge/Checker/Oracle.lean`, `OracleTest.lean` | elaborate; `forge_cone?`; data-boundary tests need `python` |
| `Forge/Checker/Affine.lean`, `AffineCorpus.lean` | elaborate; `AffineCert.sound`, `check_iff` |
| `Forge/Checker/Farkas.lean` | elaborates; `FarkasCert.sound`; no prototype family |
| `Forge/Checker/Recurrence.lean`, `RecurrenceCorpus.lean` | elaborate; `RecCert.sound`, `InvCert.sound` |
| `AxiomAudit.lean` | elaborates, and FAILS if any `Forge.Checker` theorem leaks an axiom (593 theorems) |

The per-file status, the three adversarial reviews, and Gate 2 measured against
its own exit criteria are in
[`../lean/Forge/Checker/README.md`](../lean/Forge/Checker/README.md).

**What is proved.**

```lean
theorem Cert.sound (c : Cert) (p : Poly) (ineqs eqs : List Poly)
    (hcheck : c.check p ineqs eqs = true) (x : Env)
    (hge : ∀ g ∈ ineqs, 0 ≤ eval x g)
    (hz  : ∀ f ∈ eqs,   eval x f = 0) : 0 ≤ eval x p
```

The certificate asserts a polynomial *identity*, `D·p = Σ wᵢ(Π gₖ^eᵢₖ)qᵢ² + Σ hⱼfⱼ`
with `D > 0` and `wᵢ ≥ 0`. Identity is stronger than agreement at any finite set
of points, which is why the conclusion can quantify over every assignment.
Underneath, `Poly.lean` proves evaluation is a ring homomorphism and that
`isZero` decides identical vanishing.

**What is not proved.** Completeness — nothing says a certificate exists for any
given problem. And soundness is relative to `eval` being the right semantics for
`Poly`, which is a definition rather than a theorem; a reader should look at it.

**Scope.** `Env` assigns *integers* to variables, so this establishes
nonnegativity at integer points. The identity holds in every commutative ring;
lifting the conclusion to ℝ needs an ordered field and therefore Mathlib, and is
therefore exactly the kind of file this repository has never been able to check.

**Why core-only.** Because 58 of the 90 files here depend on Mathlib and none
of them has ever been checked by anything. A checker in that bucket would have
been one more uncompiled claim.

### The fourth round

Recorded in
[`../results/lean-round-four-elaboration.json`](../results/lean-round-four-elaboration.json).
Two files, both core-only, both elaborating.

| File | Result |
| --- | --- |
| `s3/lean/CounterLemmas.lean` | elaborated; depends on `propext`, `Classical.choice`, `Quot.sound` |
| `s5/lean/AtlasQuantifiers.lean` | elaborated; no axiom dependencies for either theorem |

**A defect in this repository's own scanner, found here.** The first run
reported `CounterLemmas.lean` as `elaborated_with_sorry`. That was wrong. The
scan in `tools/check_lean.py` tested `"sorry" in text` over the raw file, and
that file's only occurrence of the token is its own header sentence, *"There are
no sorry/admit placeholders"* — so the scan reported a defect on a file
declaring its own cleanliness.

`strip_lean_comments()` now removes Lean block and line comments before a
word-boundary search, using a depth counter because Lean block comments nest.
A token found only in prose is recorded as `sorry_token_in_comments_only`.

**The audit that became possible.** Re-scanning all 90 Lean files across the
four rounds and the merged tree: **none contains a real `sorry` or `sorryAx`.**
All 26 occurrences of the token are authors stating that there are none. That
is a better result than anyone claimed, and it could not have been established
before, because the unfixed scanner could not distinguish the two cases. The
earlier rounds' scans happened to be correct — none of the files they examined
contained the token at all — but that was luck, not design.

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
- It says nothing about the 58 files that depend on Mathlib. Nothing has ever
  checked any of them — and the one time this merge looked inside that bucket
  for a reason unrelated to Mathlib, it found `r6`'s file, which cannot parse.
- **An uncompiled file is worth what its author's care is worth.** Twenty-six
  proposals ship `.lean` files carrying `#print axioms` commands that were
  never executed. Two of the three that were finally compiled were fine; one
  was not. Before this round there was no way to tell those cases apart, and
  for the 58 Mathlib-dependent files there still is not.
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
