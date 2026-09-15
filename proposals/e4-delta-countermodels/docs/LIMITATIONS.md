# Deliberate scope and remaining risks

## Mathematics

Machine semantics: finite control, fixed rational registers, arbitrary fresh
rational payloads, simultaneous polynomial updates, fixed rational initial
state, polynomial zero outputs. A one-time initialization edge supports certain
universally quantified polynomial initial states within the same IR.

There are no numerical guards, integer/natural division semantics, rounded
floating-point operations, or general heaps. Synchronous product machines
require both sides to consume the same input in the same alignment.

The decision theorem is for state-affine updates and bounded-degree goals with
unbounded exact resources. General nonlinear updates may produce an infinite
observable space. `x'=x^2`, initial 0, goal x=0 is intentionally unknown at the
configured degree cap despite being true.

Kripke results concern IPC derivability only. They do not prove a negated Lean
formula, and do not exclude classical proofs. Unknown is never interpreted as
false or as a proof of noninhabitation.

## Implementation

Search and replay share a schema and Python runtime, not polynomial arithmetic.
The checker uses standard-library Fraction arithmetic; it is not formally
verified. Search uses SymPy 1.14.0. The test corpus is synthetic and intentionally
mechanism-oriented; no held-out Lean benchmark was run.

Default search limits: degree 12, 96 generators per node, 4,000 coefficient
obligations, 2,048 terms per candidate coefficient, and 20,000 grid points during
counterexample construction. The input and checker have separate bounds,
including degree/exponent 64 and 4,096-bit rational components. These can cause
an otherwise solvable problem to return unknown. A certificate rejected by
independent replay is not released as accepted evidence; it is reported unknown.

These are not complete wall-clock/memory bounds. Expansion can be expensive
before a degree or work check, and large exact arithmetic can be expensive.
Use process isolation before untrusted-input deployment. No hostile-input
hardening or complete parser-security audit is claimed.

## Lean and application integration

The local Lean obligations are uncompiled. No source-to-machine reifier,
reflected Lean polynomial checker, finite-Kripke-to-Lean soundness bridge, Forge
runtime plugin, or Leant dispatcher was implemented. No tactic-performance
gain is established. See the staged gates in the article and MERGE_PLAN.md.
