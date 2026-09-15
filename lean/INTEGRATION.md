# Lean integration notes

Merged from the integration notes of two proposals, plus the Lean API findings
recorded by four others. Everything here is a **proposal**. No adapter has been
written and no interface below has been compiled against.

The article's Section 8 is the long form; this file is the operational summary.

## The inspected `grind` surface

All of this was read from the Lean v4.34.0 source tree. Two proposals inspected
it independently and found overlapping but differently-detailed surfaces; both
are recorded, because the disagreement is informative.

### Entry points (`Lean/Meta/Tactic/Grind/Main.lean`, tag `v4.34.0`)

| Symbol | What it does |
| --- | --- |
| `Lean.Meta.Grind.Params` | carries extensions, extra theorems, extra facts, simplification data, configuration |
| `assertExtra` | introduces supplied proof facts, via `addNewRawFact` |
| `mkGoalCore` | initialises a goal and its solver states |
| `mkDefaultParams` | default parameter construction |
| `Result` | failure information, diagnostics, counters |

### State (`Lean/Meta/Tactic/Grind/Types.lean`, tag `v4.34.0`)

`GrindM`, `GoalM`, opaque solver-extension state, and a `SavedState` holding both
Meta and grind state, whose restore operation restores both.

### Solver extensions

`registerSolverExtension` in the `Lean.Meta.Grind` namespace, with
`SolverExtension.setMethods` taking callbacks:

```
internalize   -- collect supported expressions as they enter
newEq         -- a new equality joined two classes
newDiseq      -- a new disequality
mbtc          -- model-based theory combination hook
action        -- the cheap propagation path
check         -- the expensive path; bounded certificate search goes here
checkInv      -- internal data-structure invariants
```

Registration is initialisation-time and extension state is per goal. The API
also distinguishes `Solvers.mkActionCore` from the wrapper that drains pending
facts.

One proposal called these "real integration points, not hypothetical hooks";
another declined to assume any stable public API exists. Both readings are worth
holding at once: the symbols are real, their stability across releases is not
promised.

> `checkInv` checks data-structure bookkeeping. It is not the mathematical
> soundness argument for a certificate. Do not conflate the two.

## Three constraints that shape the adapter

**1. `extraFacts` into a fresh run is not resumption.** A true incremental
adapter must preserve the goal state and all relevant solver and context state,
and must add facts through the normal internalisation and propagation path.
Otherwise an equality exists in one table while being invisible to another
solver.

**2. `SavedState` is necessary but not sufficient.** Forge introduces clause
database views, demand queues, proof dependencies, and branch-local plugin
state. Restoring a Lean metavariable snapshot alone does not roll those back.
Forge needs its own rollback layer on top.

**3. All version-specific internals live in one module.** For example
`Forge.Bridge.GrindV434`. Theory adapters and the outer scheduler target Forge's
own records, not a few dozen evolving internal modules. A Lean upgrade should
break one file.

## Proposed adapter surface

```
GrindAdapter.open           (snapshot, options)      -> session
GrindAdapter.seed           (session, checkedProofs) -> session
GrindAdapter.advance        (session, workQuota)     -> localResult
GrindAdapter.exportRelevant (session, demand)        -> checkedSummary
GrindAdapter.snapshot       (session)                -> resumableState
GrindAdapter.restore        (resumableState)         -> session
```

Unit-test seeded facts, case-split rollback, proof extraction, metavariable
changes, and equality propagation through every enabled local theory. Until that
is reliable, restarting a local tactic with explicit checked facts beats a fast
but incoherent shared state.

## Module plan

| Module | Responsibility | Acceptance contract |
| --- | --- | --- |
| `Forge.Core` | scoped expression, fact, and obligation graph | no unproved facts; valid dependency scopes |
| `Forge.Bridge` | version-specific extension hooks | restorable state; exact expression and proof transport |
| `Forge.Demand` | retrieval, instantiation, tabling | every application elaborates; acyclic proof parents |
| `Forge.Reify` | typed polynomial representation | denotation equality for each reified term |
| `Forge.Arithmetic` | cone, box, lattice certificate checking | proved checker soundness, or explicit reconstruction |
| `Forge.Structural` | recursor selection and generalisation | refinement through an actual induction theorem |
| `Forge.Synth` | invariants and existential candidates | base/step identities or witness spec discharged |
| `Forge.Backend` | SAT, SMT, SOS, LP, superposition adapters | supported translation and proof rules; no raw oracle acceptance |
| `Forge.Replay` | proof minimisation and audit | exact original goal, no metavariables, approved axioms |

The core modules depend only on Lean and a small shared representation;
Mathlib-specific reifiers sit behind separate imports. The point of that split is
**replay-only builds**: a numerical solver can be absent on the machine checking
a finished proof.

## A conservative acceptance boundary

Six steps, in order. Do not reorder them.

1. Restore the recorded original goal context and instantiate the selected
   proof's metavariables. Reject any unresolved term or universe metavariable.
2. Infer and check the proof's type against the **exact original target**, using
   only legitimate definitional equality or recorded proof transports.
3. Inspect the transitive declaration dependencies. Reject `sorryAx`, temporary
   admitted hypotheses, unapproved native assertions, and any axiom outside the
   declared policy. Existing project axioms are *reported*, never quietly
   relabelled as part of the kernel.
4. Confirm every guard and side condition is discharged, not merely recorded.
5. Validate the assembled declaration through Lean's normal checking path.
6. For reproducibility, replay the exported proof in a clean pinned workspace
   with the original pre-theorem environment.

Type inference inside a running metaprogram is useful but is not the audit: an
expression can type-check because an imported axiom states the desired result,
and a tactic can appear to close a metavariable while its suggested script
leaves a hint unproved.

## Trust profiles

Two profiles, named and never merged in reporting.

**Kernel-only.** Ordinary proof terms or kernel-reduced checker theorems.
`decide +kernel` is a supported reduction path.

**Native-checked.** `native_decide`, `decide +native`, and `bv_decide` rely on
native code generation and associated trusted results. This is opt-in, and the
active profile must be visible in the trace and the output metadata.

Two implementation details:

- Native evaluation in recent Lean can introduce a **separate generated axiom
  per computation** (see `Lean.Meta.Native`, `nativeEqTrue`). A blacklist naming
  only an older constant such as `Lean.trustCompiler` is therefore insufficient.
- Caching an LRAT file for `bv_check` does **not** by itself establish a
  kernel-only replay profile.

A whitelist may admit the project's chosen standard axioms — propositional
extensionality, choice, quotient soundness — while excluding `sorryAx` and
unapproved native-computation axioms.

## Version compatibility

Pinned here: Lean `v4.34.0`, Mathlib `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`
(whose own `lean-toolchain` specifies that Lean version).

**Not pinned, and not compatible by default:** one proposal retrieved the Lean
`sos` project's `lean-toolchain` and found it specifying `v4.32.0-rc1`. These
projects do not form a build-compatible set on the day a release appears.
Resolve commits and manifests together before attempting an integration, and do
not assume that every project's moving `main` builds against the same release.

No proposal supplied a `lake-manifest.json`, deliberately: none of them ever
built anything, and a manifest asserting otherwise would be a fiction.
