# Evidence and reproducibility

`results/summary.json` records the main seeded experiment; `equivalence-summary.json`
records a separate paired-program generator. The integer seeds are labels for
these exact generators, not links to any similarly numbered Forge experiment.

Main corpus: 7 named nets plus 60 generated conservative nets (20 with 2 places,
40 with 3). Random transition totals are preserved, so complete forward BFS is
finite from each marking. All initial vectors of total <= 6 are queried, giving
3,920 comparisons with no oracle cutoff. The stored CSV records every query.
These are small structural tests, not industrial Petri-net benchmarks.

A separate scalar formula check covers c,p,b in 0..5 and m in 0..12, producing
2,808 checks. It is test evidence, not the proof of the predecessor theorem.

For 1,000 random words, producer summaries use natural (demand,return), the
checker uses (demand,signed effect), and direct firing serves as a third small
oracle. 7,000 word queries and 2,000 expanded small-power queries agree.

Parameter certificates are exact for all natural parameters because their cap
argument is proved in the article. The 6,700 random large-parameter checks and
2,278 scalar spot checks are diagnostics, not the basis of that theorem.
Two additional named parameter/scalar examples explain why corpus counts exceed
the main random parameter block by two each.

The separate equivalence suite uses seed 20260916 (a seed, not a run date): 120
random pairs, 62 equal and 58 separated; 1,298 concrete comparisons; one extra
10^100-vs-one-step symbolic equivalence. Equality observes endpoints and enabled
input domains, NOT trace labels, intermediate states, fairness or step count.

`replay-log.txt`: 423 records checked under `python -S`, with neither producer nor
model imported. The checker still shares its Python runtime and mathematical
specification with the producer; it is not a kernel proof or fully independent
formal verification. Corpus categories are not aggregated as solved Lean goals.

`unit-tests.txt`: 68 tests, including malformed input and false-claim controls.
`mutation-results.json`: eight separately stored deliberate invalid mutations.
The latter overlap mechanisms covered by unit tests; they are not additional
independent classes of validation. No random-mutant rejection percentage is claimed.

`unknown-controls.json`: four bounded/no-witness controls return UNKNOWN, never
False, termination, or global safety. `cli-smoke.txt` exercises the public CLI.

No third-party search or numerical libraries are required. No network is used
by the code. No kernel checking or head-to-head tactic comparison was performed.

The acceleration block uses seed 41027: 24 small productive nets with matching
plain/accelerated frontiers, plus three huge-threshold ablations. Its 27 extra
frontier records bring the frontier total to 94 and the whole replay total to
423. Main-suite timings/counts are unchanged and should not be conflated with
this extra block. See ACCELERATION.md for the exact shortcut and its scope.
