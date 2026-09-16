# Evidence status

Prepared 15 September 2026.

| Component | Status | Important qualification |
|---|---|---|
| Pushdown summary search and replay | EXECUTED | Exact normalized finite-control/finite-alphabet model; no bound on stack height |
| Regular-target compiler | EXECUTED | 100 complete source/compiled comparisons; no Lean correspondence proof |
| Büchi search and both rank checkers | EXECUTED | Total finite turn-based arenas only |
| Exact chain search and both checkers | EXECUTED | Fixed rational finite stochastic matrices; exact values on AS-absorbing cases |
| Standalone stored-certificate replay | EXECUTED | 28,566 records; no search modules imported |
| Named unit tests | EXECUTED | 36 tests, including positive controls and invalid inputs/certificates |
| Mathematical soundness arguments | WRITTEN | In the article; not mechanically verified or independently peer-reviewed |
| Lean checker implementation | NOT_IMPLEMENTED | No Lean executable was available; no compiled Lean artifacts |
| Source reifiers and source bridges | SPECIFIED | Contracts and proof obligations only |
| Generalized Büchi monitor | SPECIFIED | Concrete product construction and proof argument; not an API feature |
| MDPs, parity games, arbitrary temporal logic | NOT_IMPLEMENTED | Discussed only as extensions with additional obligations |
| Tactic comparison or speedup | NOT_RUN | No baseline tactic was executed |

## Independence

Replay does not call search and does not import a search module. It uses local
closure/rank/residual checks rather than repeating the search algorithm.
Independent reference computations include concrete BFS, positional-policy
and cycle enumeration, Cramer's rule/Laplace determinants, acyclic dynamic
programming, analytic geometric values, and enumeration of closed subsets.

Shared elements remain: input dataclasses, the JSON codec, Python, and Fraction.
The decoder is not hardened against hostile inputs. Tests do not prove checker
correctness. Correct replay is not an authoritative Lean theorem.

## Counts and scope

Model cases: 881 pushdown, 22,300 games, 770 chains.
Stored records: 28,566 (games can have both a winning and a losing region).
Game start-state checks during generation: 67,260.

39 general pushdown cases have no independent complete concrete-oracle answer;
the oracle reports truncation, not false. In the arbitrary four-state chain
suite, the independent oracle checks AS classification, not every exact value.

No existing repository result has been relabelled as a result of this package.
No upstream repository was modified. The source audit was read-only.
