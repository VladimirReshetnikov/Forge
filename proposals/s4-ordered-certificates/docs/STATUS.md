# Capability and evidence status

## Implemented and executed

- Guarded natural-resource transitions `x >= a; x' = A(x-a)+b`, finite control,
  nonnegative integer matrices; resets, transfers, merges and duplication.
- Exact diagonal predecessor rules and finite integer-box predecessor enumeration.
- A clipping-bound lemma justified in the article and checked using multiplication
  inequalities in Python.
- Local-minimum box coverage certificates.
- Finite-alphabet, multi-channel lossy FIFO send/receive/tau predecessor rules.
- Eager backward antichain search with immutable earlier-child derivation DAGs.
- Global-antichain-aware closure separation and direct global-region box receipts.
- Independently written Python region and concrete-trace replay.
- Complete original transition/basis coverage checks and exact original-model binding.
- Explicit-model CLI with independent replay required before acceptance.
- Differential oracles, mutation controls, cutoff controls and isolated replay.

## Proved mathematically in the article; not formally verified

- Exact-region certificate soundness from two independently checked inclusions.
- Finite witness plans for all states above each accepted basis node.
- Resource monotonicity, clipping, diagonal rules and integer partition soundness.
- Lossy FIFO predecessor laws and explicit loss witnesses.
- Termination/completeness of the idealized eager and separation algorithms under
  WQO and no operational cutoffs.
- Uniqueness of the resulting minimal unsafe basis for the supported partial orders.

## Designed, not implemented

- Lean reflected checkers and their kernel-checked soundness theorems.
- The actual Forge worker registration, tactic invocation, and obligation routing.
- Source-to-model reification, equivalences and simulations.
- Anonymous-population count quotients and original-source witness lifting.
- External Z3/TAPAAL/LoLA integration.
- Constraint-component factorization and indexed dominance data structures.
- A combined counter-plus-channel worker.

## Explicitly not measured or claimed

No Lean compilation or kernel replay, no tactic named `forge` delivered here,
no speedup against `grind`, no external solver comparison, no end-to-end source
proof success rate, and no claim that short tests cover all infinite runs.

The independent Python checker shares the mathematical specification with the
producer, but no producer code. It is not formally verified or security audited.
Results in this archive are not pooled with historical Forge/Leant/Djex counts.
