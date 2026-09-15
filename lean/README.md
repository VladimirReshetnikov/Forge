# Lean sources

Merged from the nine proposals' `lean/` directories. Every file carries a header
recording which proposal it came from and why that version was chosen over the
others; [`INTEGRATION.md`](INTEGRATION.md) has the module plan and the inspected
`grind` API surface.

## Status, precisely

| | |
| --- | --- |
| `ForgeCore` | **Elaborates.** Verified against `leanprover/lean4:v4.34.0`; see [`../results/lean-core-elaboration.json`](../results/lean-core-elaboration.json). |
| `Forge` | **Not compiled.** Every file imports Mathlib and needs a built project. |
| A `forge` tactic | **Does not exist.** Nothing here implements one. |

None of the nine proposals compiled any Lean at all — each recorded `NOT_RUN`
with the same reason, no toolchain in the authoring environment. The
`ForgeCore` result above is the only compilation evidence this project has, and
it covers three of the sixteen files.

Successful elaboration is not a transitive axiom audit, and it is not a
comparison against any tactic. A hand-written example that type-checks proves
that the example type-checks.

## Layout

```
lean-toolchain            leanprover/lean4:v4.34.0
lakefile.toml             two libraries; Mathlib pinned at 1cf325a0…

ForgeCore.lean            core-Lean-only root — the part that compiles
Forge.lean                full root — needs Mathlib

Forge/Design/             proposed data contracts (core Lean only)
  Runtime.lean              obligations, candidates, scope keys, budgets,
                            failure kinds, engine replies
  Contracts.lean            CertificateSpec with an explicit `sound` field,
                            Proven, CheckedOutcome, FactHandle

Forge/Generated/          proof scripts emitted by the Python prototypes
  SOS.lean                  9 cone certificates, incl. an equality-ideal case
  SOSExtra.lean             9 further cone certificates over disjoint problems
  Bernstein.lean            a 32-leaf subdivision tree (~1100 lines, unique)
  Induction.lean            accumulator invariants, powers 0–8
  Invariants.lean           orbit/orbit_invariant framework + 49 instances
  Witnesses.lean            hidden quadratic, power sums, affine witness

Forge/Examples/           hand-written specimens of the target proof shapes
  Structural.lean           list algebra, Mathlib-free  ← compiles
  Basic.lean                three small certificate targets
  Arithmetic.lean           box/discriminant/division/difference-logic
  CrossTheory.lean          the p ≤ 0 + sq_nonneg ⟹ p = 0 ⟹ congrArg squeeze
  Lattice.lean              Bézout witness family and a parity obstruction
  Residue.lean              modular residue witness and quadratic specimens
  Accumulator.lean          accumulator specs, incl. an inequality invariant
  Mixed.lean                mixed obstruction and a list-fold invariant
```

## What was dropped, and why

Five proposals independently redefined append, reverse and a reverse
accumulator, and proved the same four to six facts about them, differing only in
naming (`cat`/`app`, `revAux`/`reverseAcc`/`qrev`/`revAcc`). One version is kept
— the Mathlib-free one, because it is the only one that can be checked without a
built Mathlib — and the genuinely different neighbours are kept alongside it:
the Mathlib-`List.reverse` formulation and the accumulator *inequality* in
`Accumulator.lean`, the residue witness in `Residue.lean`, the integer list-fold
in `Mixed.lean`.

Similarly, the power-sum proofs appeared three times; the accumulator-general
form is kept and the `a = 0` specialisation dropped, since it is an instance of
it. The `x(1-x)y(1-y) ≥ 0` family appeared in five files under four emitter
styles; the redundant re-emissions are gone, the distinct problems retained.

Namespaces are left exactly as their authors wrote them (`ForgeExamples`,
`ForgeReplay`, `ForgeArtifacts`, `ForgeSpecimens`, `ForgeDesign`,
`ForgeContracts`). They do not collide, and renaming them would mean editing
proof scripts that have never been compiled — a bad trade.

## Building

Core only, no Mathlib needed:

```bash
python tools/check_lean.py --mode elaborate lean/Forge/Design lean/Forge/Examples/Structural.lean
```

Everything, in a project with Mathlib built:

```bash
cd lean
lake update
lake exe cache get
lake build
```

`lake update` will resolve Mathlib at the pinned revision. Expect this to take a
long time on a cold cache, and expect failures: these scripts were written
against an inspected source tree, never against a running compiler.

To check individual files against a Mathlib project you already have:

```bash
python tools/check_lean.py --mode lake --project /path/to/mathlib-project lean
```

Fix a failure by fixing the script. A failing proof is not a licence to replace
it with `sorry` — and note that `lean` exits 0 on a file whose declarations are
admitted, which is why the harness scans for the token independently of the exit
code.
