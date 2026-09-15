# Recorded experiment data

`summary.json` contains aggregate counts. `cone.csv`, `bernstein.csv`,
`invariants.csv`, and `horn.csv` contain individual observations.
`environment.json` describes the actual Python environment.
`pytest.txt` records 260 passing tests from the final source state.

The cone comparison changes the finite candidate dictionary (affine binomial
squares and inequality products), not the LP backend. The Bernstein comparison
changes subdivision, not the polynomial or checker. These workloads are
constructed to exercise the mechanisms; they are not a held-out Lean corpus.

The Horn `early_goal` variant stops at the first known goal, unlike `full_closure`.
All variants receive the same rules and facts. The `index_seconds` field is the
common reverse-index construction time; `query_seconds` excludes it and
`cold_total_seconds` includes it. Initial-fact handling still costs time in the
demand variant. Large timing fluctuations should not be interpreted as speedup
evidence: these are single warmed runs, not repeated statistical benchmarks.

The two JSON certificates are exports of successful in-process certificates.
The prototype deliberately does not include an audited hostile-input JSON
parser. Each replay checker takes its original problem independently.

No Lean tactic, Lean kernel check, or `grind` execution is represented in these
numbers. See the article for the full comparative evaluation still required.
