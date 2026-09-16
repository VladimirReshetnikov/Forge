# `forge-auto-1`: semantic contract

The authoritative executable checks are in `prototype/checker.py`; the article proves the specified mathematical receipt rules, not that Python implementation.

## Query and values

A query has exactly `context` (ordered, distinct names) and `formula`. All quantified variables range over natural numbers. Atomic linear expressions use integer coefficients and integer evaluation. The checker must receive the expected query from its caller, separately from the certificate, and compare it with both the bundle query and the root judgment.

Words are least-significant-bit first. Track `i` is bit `i` in each encoded letter. Track value is the sum of its digit at position `j` times `2**j`. Empty words represent all-zero tuples; zero suffixes do not change values.

## Formula keys

- `eq`, `le`: `op`, `coeff`, `rhs`.
- `cong`: the same plus a positive integer `modulus`.
- `parity`: `op`, `var`, integer `value` 0 or 1 (popcount parity, not numeric evenness).
- `pow2`: `op`, `var`; zero is excluded.
- `bitand`, `bitxor`: `op`, `vars`, with exactly three variable names.
- `const`: `op`, Boolean `value`.
- `not`: `op`, `arg`.
- `and`, `or`, `iff`: `op`, `left`, `right`.
- `exists`: `op`, fresh `var`, `arg`; binds the last context track.

Universals expand as `not exists not`. Active binder shadowing is rejected; sibling scopes may reuse names. Fresh names for least graphs must not collide with the surrounding context or become captured.

## DFA

Exactly `k`, `start`, `trans`, `final`. The nonempty state set is indexed by rows. Each transition row has `2**k` valid target indices. Finals are Booleans. Missing transitions do not mean rejection: they make the certificate malformed. Genuine integer types are required; Python Boolean/integer equality is not sufficient.

## Nodes

Every node has `kind`, `ctx`, `formula`, `dfa`. Child references must be smaller than the node index.

| Kind | Additional receipt |
|---|---|
| atom | `labels`: exact carries, residue pairs, or digit states |
| not | `child`; unchanged transitions and complemented final flags |
| product | `left`, `right`, `pairs`; exact synchronous pair equations |
| quotient | `child`, `mapping`; total map preserving start, step, acceptance |
| exists | `child`, `subsets`, `tail_rank`, `tail_choice` |

For an existential source, a non-null rank marks states with a zero-visible tail to an original final. All original finals must be marked; zero rank implies original final; positive rank supplies a hidden bit leading to a smaller non-null rank; every unmarked state's two zero-visible successors must remain unmarked. Thus the marked set is exact, not merely an underapproximation. Subsets have canonical sorted members and exact hidden-bit union transitions. A subset accepts iff it meets the marked set.

## Root and verdict

A bundle has `schema`, `query`, `nodes`, `root`, `verdict`. An `unknown` status is not evidence and is rejected.

- `valid`: `invariant` contains the start, consists only of accepting states, and is closed under every transition.
- `counterexample`: `word` leads to a rejecting state and `values` is exactly its decoded free tuple.

A closed false sentence has an empty free tuple. Counterexamples are not quantified adversary strategies. Shortest-word production is not numerical minimization and is not checked for shortestness.

## Witness record

`inputs`, `witness`, `word`, `trace`. The caller supplies an already verified relation machine and expected inputs. The checker verifies every state transition, final acceptance, and tuple decoding. Leastness follows only when that machine was verified against the *least-graph formula*, not from an arbitrary accepting run.

## Limits

Producer defaults: 8 tracks, 8,192 states/machine, 4,096 nodes, 2,000,000 cumulative transition cells. Checker: 8 tracks, 20,000 states/machine, 4,096 nodes, 2,000,000 cells, formula-depth limit 128; CLI certificate-byte limit 100,000,000. These are research safeguards, not comprehensive denial-of-service protection; coefficient bit size, parser allocations and total OS resource budgets need further hardening.
