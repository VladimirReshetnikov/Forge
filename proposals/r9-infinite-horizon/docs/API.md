# Python API

The package is under `prototype/forge_horizon`. Running scripts inside `prototype/`
sets the import path automatically. For interactive/library use add `prototype/`
to `PYTHONPATH`. No pip installation is needed.

## Models

`PDS(n, alphabet, rules, start, stack, finals)`:
`Rule(p, a, q, rhs)` replaces the first stack symbol `a` with `rhs`, length 0–2.
Empty stacks cannot transition. The query asks for empty stack at a final control.

`Game(owner, edges, accepting)`:
owner 0 is protagonist, 1 antagonist. Edges are nonempty, duplicate-free rows.
The query asks for infinitely many accepting visits, not one visit.

`Chain(matrix, terminal, payoff, cost, start=0)`:
all numerical fields must contain `fractions.Fraction`; terminal payoffs are in
[0,1], nonterminal payoffs zero; costs are nonnegative, terminal costs zero;
every terminal is absorbing and every row sums to one exactly.

## Search and replay

`pushdown.solve(p) -> certificate`

`pushdown.compile_regular_target(p, delta, initial, accepting) -> compiled_pds`
reads the stack top to bottom. `initial[q]` chooses the target DFA's start by
source control. This target replaces `p.finals`; it does not intersect them.
The compiler is tested, not formally verified.

`games.solve(g) -> {"winning": cert, "losing": cert, "stats": ...}`
returns both regions, which may be empty. Pass a start in the chosen region to
`check_game`. A positive policy selects at owner-0 vertices, negative at owner-1.

`markov.solve(c) -> certificate`
returns `mc_absorb` or `mc_trap`. Exact values on AS-absorbing inputs are expected
time, expected accumulated cost, and expected terminal payoff. The last is an
ordinary event probability only for an indicator payoff. A negative result includes
a positive lower bound on nontermination probability, not its exact value in general.

Replay:
`check_pds(p, cert)`, `check_game(g, cert, start)`, `check_chain(c, cert)`.
These functions return recomputed result dictionaries or raise on invalid input.
They receive the original model independently of the certificate's claims.
Unexpected malformed shapes may raise ordinary Python exceptions: this is not a
hardened decoder or service interface.

## Transport

Fractions serialize as `{"rational": [numerator, positive_denominator]}`.
`codec.loads` rejects duplicate keys, imposes a 50-million-character limit and
100,000-bit numerator/denominator limits, and reconstructs exact fractions.
These coarse limits do not provide comprehensive memory/CPU/recursion protection.

A stored result's `expected` field is only a regression oracle: the semantic
checker computes the conclusion from `problem`, `certificate`, and game `start`.
`verify.py` compares it afterward and checks that search modules are absent.
