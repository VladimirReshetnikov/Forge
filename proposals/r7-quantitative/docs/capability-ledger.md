# Capability ledger

| Capability | Implemented / executed | Paper theorem | Still missing |
|---|---|---|---|
| Exact max reachability | Policy enumeration, exact solves, independent checker, vertex oracle | Upper Bellman vector plus selected policy and exit rank; existence of proper optimal policy | Lean checker, source normalization bridge, native tactic |
| Uniform runtime | Exact candidate potentials and all-action checks; forward-family oracle | Bound for every history-dependent randomized scheduler | General-cost finite-MDP producer, Lean infinite-horizon bridge |
| Coupling and transport | Exact residual search, marginal/dual checker, Hall negatives; integer-table oracle | Weak-duality optimality and Hall soundness | Lean witness construction and finite-source reflection |
| Strong bisimulation | Sequential Hall deletions, positive joints, partition oracle | Greatest-relation result and scoped negative certificates | Lean deletion theorem and controller integration |
| Affine distance bound | All-pairs exact transport; metric/rate checker; TV oracle | All-horizon mixture recurrence | PMF lifting and goal transport in Lean |
| Polynomial cost | Negative-drift triangular solve and independent Horner checker | Infinite-state upper bound by finite-prefix telescoping | Lean stopped-walk semantics and analytic limit theorem |
| Lean foundations | Candidate source only; attempts record NOT_RUN | Explicit paper proofs supplied | Actual compilation, all source bridges and certificate soundness theorems |

No benchmark here compares Lean theorem-solving coverage or speed. “Accepted”
means the Python checker accepted finite obligations; it does not mean Lean's
kernel accepted the original proposition.

Completeness scopes: unbounded finite-policy enumeration decides finite rational
maximum reachability; exact finite transport decides support feasibility and
computes a named-cost optimum; complete finite bisimulation refinement decides
strong bisimulation; all-pairs transport decides the fixed metric/rate/error
local condition. Runtime search is not advertised as complete on arbitrary
models. Polynomial identity synthesis is complete for its normalized degree
space when mean jump is nonzero; its positivity vocabulary is incomplete.
Operational budgets can produce UNKNOWN in every producer.
