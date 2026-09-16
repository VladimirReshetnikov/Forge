# Source audit and novelty boundary

Read date: 2026-09-15. Connector branch-ref results identified commits, not merely
unverified filenames or inferred version tags.

| Repository | Read snapshot |
|---|---|
| Forge | c98e47c5f804e92880fc1d0e378c1b95832b685c |
| Leant | 6bf05ad78c467989e68290f2d08bbed40802d485 |
| Djex | e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5 |

The targeted Forge review used the README and recursive repository tree,
`article/sections/B-provenance.tex`, `02-baseline.tex` (opening 250 lines),
`07-nonlinear.tex` (opening 220 lines), `06-closure.tex` (principal linear,
ideal, and Ore sections, especially ranges 1–580 and 680–915), and the opening
210 lines of `docs/IDEAS-FROM-LEANT-DJEX.md`. Some connector outputs were
truncated; no exhaustive reading of all frozen submissions is claimed.
Leant and Djex were reviewed through their current README entry documents,
not through a complete code audit or runtime build.

Existing mechanisms deliberately excluded from the claimed contribution:
commutative polynomial ideals, tracked multipliers as an architectural idea,
scalar quadratic LDL, observable closure, polynomial invariant closure,
finite-algebra covers, telescoping, specialized Ore transport, and the already
merged receipt/status/source-ownership architecture.

Proposed delta: general two-sided free-word contexts; exact incidence slicing;
a degree-complete homogeneous fragment and constructive finite rational matrix
countermodels; arbitrary-even-degree homogeneous word Gram factors; constrained
adjoint-square receipts; a relation-graph ray proposer; and separate trace
commutator receipts. These are additions to the inspected merged mechanisms,
not global claims of new mathematics or proof that no archived paragraph ever
mentions a related concept.

Mathlib already has `noncomm_ring`, with explicit hypothesis/simplification
support. Bare noncommutative normalization is not a new contribution. None of
the worked examples is presented as a demonstrated failure of existing tactics.
The final bibliography gives primary documentation and original research sources.

The repository baseline records later elaboration of 16 core-only Lean files.
Older statements that none of the original proposals could run Lean must not
be substituted for that current status. This package has its own NOT_RUN Lean
status; it does not inherit the baseline's elaboration results.
