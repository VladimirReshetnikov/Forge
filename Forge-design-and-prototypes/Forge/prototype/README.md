# Forge algorithm prototypes

These are **executed Python prototypes**, not a complete Lean tactic. They have
not been checked by the Lean kernel. The intended Lean baseline inspected for
the design is Lean 4.34.0 (September 14, 2026); no Lean process was run here.

## Reproduce

The recorded environment uses Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0.
From this directory, in a virtual environment:

```sh
python -m pip install -r requirements.txt
python -m unittest discover -s tests -v
python run_experiments.py --output ../results
python -S replay_certificates.py ../results/certificates
```

The final command intentionally disables third-party package loading. All 215
stored certificates replay using the standard library alone. Search is a
separate process: SciPy's HiGHS LP backend proposes witnesses and square weights;
exact rational arithmetic validates every accepted proposal.

## What is implemented

`forge_proto/induction.py` is a small typed first-order list language with exact
rewrite-trace replay and structural induction. The induction tail is a rigid
constant; only generalized parameters are match variables. Four seed theorem
**statements** are supplied, and their proofs are searched and checked. The
accumulator parameter is detected from the recursive call. Its generalized
right-hand side is genuinely enumerated from a typed grammar and filtered on
49 concrete input pairs before symbolic induction. The first successful
candidate is candidate 32. This is not full e-graph-guided lemma discovery.

`recurrence.py` searches rational polynomial closed forms for additive
recurrences, uses exact failed step identities to produce counterexamples, and
checks the base and step identities. Degree-bounded failure is not falsity.

`witness.py` jointly synthesizes affine source-level witnesses and Farkas
multipliers. The result proves a universally quantified implication over
rationals/reals. It does not support integer witnesses, strict constraints, or
general quantified SMT problems.

`positivity.py` has a finite-dictionary nonnegative-square LP search, an exact
square-certificate checker, and exact Bernstein subdivision with full partition
replay. The square dictionary is deliberately limited; it is not an SDP solver
and is not a replacement for the existing Lean `sos` project.

`poly.py` is a sparse exact rational polynomial substrate. `linear.py` separates
exact elimination from floating-point LP proposals. Search may fail to recover
a rational certificate even when one exists; no tolerance-based proof acceptance
is used.

## Evidence and scope

The committed run contains 31 passing unittest methods (many perform multiple
seeded trials), 215 accepted certificate cases, and a search-free replay log.
The cases are constructed micro-experiments and regression tests, not a random
sample of Lean goals or a head-to-head comparison with `grind`.

The benchmark explicitly reports that the 40 SOS cases are generated from the
same finite dictionary used by the solver. All successful measurements must be
read with that restriction. Timings are local Python search-plus-check timings,
not predicted Lean performance.

Certificate JSON files contain both the stated problem and its certificate.
The actual checker functions take the problem separately. A production prover
must obtain that problem from its trusted reifier, not allow an external solver
to replace the original Lean goal with a different problem.

## Deliberate exclusions

No general Lean elaborator, dependent-type reifier, E-matching engine, MBQI engine,
proof-state scheduler, persistent e-graph, branch-context transport, external
SMT proof importer, or end-to-end Forge tactic is implemented here. Those are
specified in the article, with explicit interfaces and implementation stages.

The illustrative Lean file in `../lean` has no `sorry`, but **was not compiled**.
It is not included in any passing-test count.
