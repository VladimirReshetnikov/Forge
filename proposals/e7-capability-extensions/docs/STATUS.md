# Evidence status and next acceptance gates

## Executed in this package

| Component | Evidence | Scope |
| --- | --- | --- |
| Pullback-stable space | `results/results.json`, exact certificate replay | Rational polynomial maps, bounded degree; affine differential corpus |
| Target ideal completion | Same, plus optional SymPy validation | Unguarded polynomial transition systems; finite generators/degree/resource budgets |
| Continuation synthesis | Same, symbolic final replay and direct-reference tests | Explicit indexing sketch, finite grammar, encoded finite lists |
| Cyclic descent | Same, independent rank replay | Supplied affine call graphs; not full proof construction |
| Acceptance replayer | `results/standalone-replay.txt` | Standard-library Python, no search imports |
| Portable tests | `results/unit-tests.txt` | 29 methods; overlaps with certificate counts |
| CAS comparison | `results/sympy-validation.json` | SymPy 1.14.0, search validation only |

## Not executed

`lean/Specimens.lean` has NOT_COMPILED status. No Lean executable was available.
No Mathlib source reifier, certificate-to-Expr lowering, tactic integration,
original Leant behavioral-query rerun, or production Djex modification is present.
No solved-goal gain or runtime improvement over existing Lean tactics is claimed.

## Integration gates, in recommended order

1. Compile the proof specimens under Lean v4.34.0, retain exact output, and audit
   their axioms. Compilation failures must be repaired rather than bypassed.
2. In the pinned Mathlib project, reify one polynomial fixture and prove evaluation
   preservation. Lower a stored action certificate to an actual theorem, reject
   the recorded wrong-target and missing-transition mutations, and measure the
   complete elaboration/kernel path.
3. Lower polynomial-multiplier certificates and exact orbit counterexamples.
   Replay source guards before treating an encoded orbit as a source counterexample.
4. Implement the finite continuation-local lane behind a checked fold theorem.
   Rerun the EXACT original Leant indexing query and controls, with its recorded
   source binders, providers, observations, and budgets. Easier signatures or
   the prototype's own fixtures do not close that acceptance gate.
5. Compile a tagged cyclic obligation family with explicit local constructors
   into ordinary well-founded induction. Check all call edges and scope/transport
   obligations. A standalone ranking or SCT diagnostic does not close a Lean goal.

The article supplies proposed module names and interfaces. These names are design
suggestions, not references to implemented Forge modules.
