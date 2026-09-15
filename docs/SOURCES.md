# Sources and version policy

Merged from the five proposals that kept a source ledger — two in Markdown, two
in JSON, one embedded in a status file. The bibliography proper is
[`../article/references.tex`](../article/references.tex), which deduplicated
roughly 215 entries under about 100 keys down to 56.

No third-party source code, repository archive, or font file is redistributed
here. Cited works retain their own terms.

## The pinned baseline

| | |
| --- | --- |
| Lean | `v4.34.0`, released 14 September 2026, publication timestamp `2026-09-14T14:04:36Z` |
| Mathlib | revision `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`, whose own `lean-toolchain` specifies that Lean version |

The Mathlib revision was read on 14 September 2026 in America/Los\_Angeles; the
corresponding commit timestamp falls on 15 September in UTC. That is a timezone
artefact, not two revisions.

## Pinned versus mutable

This distinction is the most useful thing the source ledgers recorded, and it
is preserved here.

**Tag-pinned** — stable, re-fetchable, quotable:

| Source | Tag | Inspected blob SHA-1 |
| --- | --- | --- |
| `src/Init/Grind/Config.lean` | v4.34.0 | — |
| `src/Lean/Meta/Tactic/Grind/Types.lean` | v4.34.0 | — |
| `src/Lean/Meta/Tactic/Grind/Main.lean` | v4.34.0 | — |
| `src/Lean/Meta/Tactic/Grind/Action.lean` | v4.34.0 | `ad212d7c8ef8277b4be3650d43738ee98a32cbf5` |
| `src/Lean/Meta/Tactic/Grind/Finish.lean` | v4.34.0 | `6bae01e1c2c4772d0cabe99ff74437492ccebfc5` |
| `src/Lean/Meta/Tactic/Grind.lean` | v4.34.0 | `db642e7864020148fab27822bf83c445de83d02d` |
| `src/Lean/Meta/Tactic/Grind/Arith/CommRing/Types.lean` | v4.34.0 | — |
| `src/Lean/Meta/Native.lean` | v4.34.0 | — |
| Aesop README | — | `f75ec1f8bebcf6d857fc3954cf91cf99f323a758` |
| Duper README | — | `1859f7fa914fbd8151b274fd34e46f3a09ef1b2d` |
| lean-egg README | — | `0dbfa063b5a77c6e892eaa265f068437980812c1` |

**Mutable snapshots** — observed on 14 September 2026, and not stable:

- The Lean Language Reference at `/latest/` (grind, algebraic solver, linear
  arithmetic, linear integer arithmetic, E-matching, case analysis, tactic
  reference, validating proofs)
- Generated API documentation for `Lean.Meta.Tactic.Grind.Types` and
  `Lean.Elab.Tactic.BVDecide`
- Mathlib generated docs for `linarith`, `positivity`, `ring`,
  `linear_combination`
- `leanprover/sos` `main` (`SOS/Engine.lean`, `SOS/Core.lean`, `lean-toolchain`)
- `leanprover/lp`, `leanprover/hex-mv-poly`
- `leanprover-community/lean-auto`, `ufmg-smite/lean-smt`, `JOSHCLUNE/QuerySMT`,
  `JOSHCLUNE/LeanHammer`

> **A blob id is not a commit id.** One proposal recorded a GitHub file blob
> identifier, `f0355a372e08f69d863b94ee39541a8b96d300e5`, for a
> development-branch excerpt of `Grind/Main.lean` and flagged it explicitly as a
> blob rather than a repository commit. Both are opaque hex strings; only one
> identifies a tree state.

## What was observed, not tested

Everything above is a **source observation**. No proposal ran a Lean
executable; this merge elaborated three core-only files and nothing more. In
particular:

- Statements about what `grind` does come from reading its documentation and
  source, not from running it.
- Statements about the `sos` and `lp` projects' interfaces come from reading
  their repositories.
- No proposal established that any two of these projects build together.
- The `sos` project's retrieved `lean-toolchain` specified `v4.32.0-rc1`,
  against this project's `v4.34.0` baseline. Pin a mutually compatible set
  before integrating; do not assume that every project's moving `main` builds
  against the same release.

## Findings worth carrying forward

Three source observations materially shaped the merged article.

**An SOS tactic already exists.** `leanprover/sos` implements an end-to-end
nonlinear-real-arithmetic tactic after Harrison's procedure — reification,
search, rational reconstruction, certificate-based proof construction, and a
witness replay interface, with degree deepening and constraint-product bounds
already in its configuration. Two of the nine proposals found this; the other
seven proposed building the same thing. "Add an SOS tactic to Lean" is
therefore not a contribution.

**Verified linear programming already exists.** `leanprover/lp` splits into
core data, pure verification, tactics, and backend packages, documents a
certified maximisation tactic and a supported quantified rational-affine
fragment, and documents its own native-backend trust distinction. Much of the
affine-witness machinery has a home already.

**Native evaluation adds axioms per computation.** Since Lean 4.29.0, native
computations used by relevant tactics may be represented by per-computation
axioms rather than a single historical constant. `Lean.Meta.Native`'s
`nativeEqTrue` compiles and evaluates a closed Boolean expression and then
introduces a fresh axiom asserting it equals true. A blacklist naming only
`Lean.trustCompiler` is therefore insufficient, and the current behaviour must
be audited against the pinned implementation rather than inherited from a design
thread.

## Provenance of prior art

The design reuses established ideas and says so. Sum-of-squares certificate
reconstruction, equality saturation, e-graph-guided inductive lemma discovery,
rippling, counterexample-guided inductive synthesis, DPLL(T), SMT proof
reconstruction, and AND/OR tactic search are all prior art, cited in the
article's bibliography. The claimed contribution is the integration: a shared,
scope-aware proof-obligation planner that makes structural synthesis, witness
search, theorem instantiation, and existing nonlinear reasoning cooperate.
