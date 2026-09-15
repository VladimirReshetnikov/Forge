# Integration contract (design, not an implemented Lean package)

The research baseline is the documentation/source inspected on 2026-09-14,
when Lean v4.34.0 was the latest release. No Lean executable was available in
the authoring container. `ReplayExamples.lean` has NOT been compiled. It has no
`sorry`, no new axioms, and no claim that it implements `forge`.

Proposed modules, in implementation order:

| Module | Concrete implementation and acceptance boundary |
|---|---|
| `Forge/FrontEnd.lean` | Elaborate `forge`, `forge?`, and `forge only [...]`; save original metavariable context and options; run an untouched baseline lane. |
| `Forge/ProofGraph.lean` | Scoped AND/OR obligations with explicit proof builders, local context fingerprints, and acyclic certificate dependencies. |
| `Forge/Structural.lean` | Read equation theorems and recursors; rank induction variables; compute dependency-closed parameter generalizations; invoke Lean's induction machinery. |
| `Forge/LemmaSearch.lean` | Typed equation schemas, anti-unification of stuck subterms, bounded synthesis, local counterexample filters; admit only independently proved lemmas. |
| `Forge/Witness.lean` | Scope-correct affine/residue witness synthesis; build `Exists.intro`, discharge side conditions. |
| `Forge/Poly/Syntax.lean` | Reified rational polynomial language plus a proved evaluation relation to the user's expression. |
| `Forge/Poly/Certificate.lean` | Sparse identity checker and soundness theorem for cone/ideal and Bernstein tree certificates. |
| `Forge/GrindAdapter.lean` | Register a solver extension at initialization, maintain per-goal state, and publish checked facts. |
| `Forge/Boolean/Replay.lean` | Certified atom mapping, CNF conversion, theory clauses and resolution/LRAT replay. |
| `Forge/Export.lean` | Deterministic replay script and minimized dependency list; kernel/axiom audit. |

The current API inspected exposes `Lean.Meta.Grind.registerSolverExtension`,
`SolverExtension.setMethods`, and callbacks `internalize`, `newEq`, `newDiseq`,
`mbtc`, `action`, `check`, `checkInv`. Registration must occur during initialization.
`Solvers.mkActionCore` does not drain pending facts; the wrapper `Solvers.mkAction`
does. These are integration points to pin and compile-test, not a promise of API
stability. Changing the entire CDCL branch engine is NOT accomplished by merely
registering one solver extension; initially run a standalone certificate-producing
Boolean lane and import its proved consequences.

An external solver's `sat`, `unsat`, polynomial identity, or synthesized witness
is never a Lean proof. Reification equivalence, local assumptions, binder scopes,
and all side conditions must be reconstructed. Python checkers are testing assets,
not additions to Lean's trusted computing base.

For maximal assurance, use ordinary proof terms/kernel-reduced checker theorems
and audit `#print axioms`. Since Lean 4.29, native evaluation can introduce
per-computation axioms rather than the old single `Lean.trustCompiler` name;
audit the actual pinned version, not just a blacklist for one old constant.
