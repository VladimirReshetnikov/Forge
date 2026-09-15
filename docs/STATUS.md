# Implementation status

Merged from the nine proposals' status files, which appeared under seven
different names in two formats. The three-bucket model below is taken from the
clearest of them.

Machine-readable twin: [`status.json`](status.json).

## Executed

Implemented in Python and actually run, in at least one of the nine runs.
Section 9 of the article says which run, with what result, and under what
caveat.

- Exact sparse rational polynomial arithmetic, with canonical-form enforcement
  and float rejection
- Exact quadratic decomposition by symmetric pivoting / Schur complement
- Finite polynomial-cone search: LP proposal, exact rational repair, independent
  identity check
- Equality-ideal multipliers with unrestricted sign
- Bernstein box subdivision with checked coverage trees, in three split policies
- Square-factor and Sturm certificates for univariate intervals *(one run only)*
- Polynomial recurrence synthesis, direct-solve and CEGIS variants
- Accumulator-invariant synthesis, including the state-machine formulation
- Affine witness synthesis with Farkas multipliers *(one run only)*
- Integer-lattice witness extraction with divisibility obstructions *(one run
  only)*
- Finite-residue witness synthesis *(one run only)*
- Polynomial witness synthesis certified by cone certificates *(one run only)*
- Demand-directed ground Horn reasoning, propositional and first-order
- Typed equational prover with structural-induction trace replay
- Accumulator generalisation and bounded lemma synthesis
- Proof-logging CDCL(T) over integer difference logic, in two certificate
  formats
- Standard-library-only replay of every stored certificate
- Lean source emission for cone, Bernstein, induction and witness certificates
- Mutation, corruption, differential and negative-control test suites

## Generated but not compiled

Produced as Lean source, never checked by a compiler — with one exception.

- Cone certificate replays (two emitter styles, 18 theorems)
- A 32-leaf Bernstein subdivision replay
- Accumulator-invariant replays, powers 0–8
- The orbit/orbit_invariant framework and 49 instances
- Power-sum and affine-witness replays
- Hand-written arithmetic, lattice, residue, cross-theory and mixed specimens

**The exception.** Three files import nothing beyond Lean core and now
elaborate against `leanprover/lean4:v4.34.0`: the runtime contract, the
certificate-soundness contract, and the Mathlib-free structural proofs. See
[`LEAN-STATUS.md`](LEAN-STATUS.md).

## Designed, not implemented

Specified in the article, in some cases in considerable detail, and built by
nobody.

- The `forge` tactic and its user-facing syntax
- The obligation graph and scheduler against real Lean snapshots
- The `grind` adapter, incremental or otherwise
- A dependent-type-aware reifier, and any proof that a reified problem
  corresponds to a Lean expression
- Reflected Lean checkers for any certificate family, and their soundness
  theorems
- A Lean formalisation of the Sturm root-count theorem — without which the
  univariate worker cannot be trusted in Lean
- General quantifier instantiation, E-matching, and model-guided instantiation
- Higher-order and dependent-type witness synthesis
- External SMT / ATP proof reconstruction with residual-obligation handling
- A semidefinite backend with exact rational recovery
- Certified product envelopes (specified, never coded)
- Bounded equality saturation over real Lean expressions
- The axiom-policy audit
- A real Lean corpus evaluation, or any head-to-head comparison against `grind`

## What is explicitly not claimed

- No Lean tactic named `forge` exists.
- No certificate anywhere has been checked by Lean's kernel.
- No comparison against `grind`, Aesop, `nlinarith`, LeanHammer, or any other
  tactic was performed by anyone.
- No speedup, solved-goal gain, or success-rate claim is made.
- The Python checkers are not formally verified, and several share
  representation code with the searches they audit.
- Neither the checkers nor the decoders are hardened against hostile input.
- The nine runs' counts are not comparable and were never pooled.
- A bounded search returning nothing means **unknown**, never that a statement
  is false.
