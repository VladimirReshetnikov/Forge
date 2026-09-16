# Evidence ledger

## Implemented and executed

All use exact rational arithmetic and the Python standard library only.

| Worker | Search | Independent oracle | Full-run result |
|---|---|---|---|
| Parity | Recursive Zielonka + rank extraction | Enumerate positional strategies and eventual cycles | 884/884 agree |
| Transport | Edmonds–Karp, residual completion, cut | Enumerate weighted Hall subsets | 400/400 agree |
| Expected time | Trap fixed point, exact maximizing policy iteration | Enumerate policies, graph nontermination test, Cramer's rule | 180/180 agree |
| Simulation | Ordered fixed-point pair deletion using transport | Enumerate all subrelations and Hall tests | 100/100 agree |

Fourteen focused regressions pass. Rejected invalid mutations by family are
1,128 parity, 723 transport, 180 expected time, and 86 simulation. Mutations are
purposefully invalid changes, not unrestricted random mutations.

All full-run records replay with `forge_ap.search` and `tests` imports actively
forbidden, with Python site packages disabled. Search and checking still share
input representations and Python arithmetic; this is not formal independence.

## Supplied but NOT_RUN in Lean

- `lean/RankTelescoping.lean`: natural prefix-sum rank arithmetic.
- `lean/CouplingAlgebra.lean`: finite rational marginal identities.

No compiler execution, no accepted declaration receipt, no axiom inventory.
The specimens do not implement the full certificate theorems.

## Designed, not implemented

- Boolean Lean checkers and their complete soundness theorems.
- Original Lean expression -> exact model bridges.
- ProbabilityMassFunction interpretation, infinite-play/expectation bridges.
- Actual Forge worker registration, cancellation, scope and snapshot plumbing.
- Oink, Spot, Storm/stormpy adapters.
- Symbolic polynomial drift synthesis.
- Min-cost transport duals and Wasserstein-style contraction certificates.
- Incremental simulation flow repair and sparse certificate encodings.
- Policy compression to source-level programs.
- A Lean theorem corpus evaluation against any baseline.

## Not claimed

No novel invention of parity games, couplings, policy iteration, or simulation.
No exhaustive audit of every historical file in Forge. No Lean tactic named
`forge` is installed by this archive. No tactic speedup, theorem solve rate,
benchmark superiority, or security-hardening claim is made.
