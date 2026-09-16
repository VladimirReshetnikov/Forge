# Repository audit and non-duplication boundary

Inspected September 15, 2026.

## Source identities

| Repository | Inspected commit |
|---|---|
| VladimirReshetnikov/Forge | c98e47c5f804e92880fc1d0e378c1b95832b685c |
| VladimirReshetnikov/Leant | 6bf05ad78c467989e68290f2d08bbed40802d485 |
| VladimirReshetnikov/Djex | e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5 |

The Leant report mentions its native Djex dependency `e237e866`; that dependency
is not equated with the separately inspected current Djex HEAD.

## Forge material read

- `README.md`
- `docs/STATUS.md`
- `article/sections/07-nonlinear.tex`
- `article/sections/06-closure.tex`
- `article/sections/12-conclusion.tex`
- Repository tree metadata identifying the merged source, prototypes, and
  historical proposals.

The GitHub connector retrieved these sources at the pinned commit. The audit
was not an execution of Forge's suites or a line-by-line reading of every
historical proposal. An incomplete repository code-search response was not
used as proof that a concept was absent.

## Existing capabilities not claimed as contributions

Polynomial cones and SOS; exact quadratic positivity; Bernstein subdivision;
univariate/Sturm certificates; invariant and accumulator synthesis; affine,
lattice, residue, and polynomial witnesses; structural induction; CDCL and Horn
reasoning; discrete observable-space and ideal closure; finite-algebra covers;
telescoping and Ore transport; finite countermodels; generic proof-replay and
source-identity architecture.

The inspected Forge status reports an unimplemented `forge` tactic, 16 elaborated
core-only Lean files, and no certificate-checker kernel proof or tactic comparison.
It would be inaccurate to say that no Lean source anywhere in that repository
had ever compiled.

## Actual delta developed here

1. Ordered constant-coefficient differential ladders for inequalities on rays.
2. Ascending-order dominance, eliminating permutation search in the fixed factor
   class.
3. Auxiliary-factor enrichment with a monotonicity theorem and an interior-zero
   obstruction.
4. Total exact eventual-sign construction with an explicit rational cutoff.
5. Rational-anchor enclosures and concrete source/chart/strictness contracts.
6. Executable prototypes, independent derivative calculations, recorded receipts,
   and uncompiled Lean source emission for this analytic family.

The reference compact cover is support machinery, not a new interval method.
No global priority claim is made for the underlying classical mathematics.

## Neighbouring projects

Read the indexing-composition diagnostics in Leant and Djex, at the commits
above. The original bounded Int-indexing acceptance remains absent there.
The actionable lesson used here is that a changed domain or weaker conclusion
is not acceptance of the original query. Tests enforce this specific analogue.

## External library review

- Mathlib official derivative/monotonicity and exponential-derivative API docs.
- `peti12352/lean-interval-bounds`, README blob
  `8c6b01fafe0e511d194f60a4997432eb7f7134c4`.
- `alerad/leancert`, README blob
  `8a65c45afc1763a36d5d406692779daff401b92f`.

The last two are concrete reuse candidates, not installed or benchmarked
libraries in this environment. LeanCert's documented kernel/native choice is
preserved explicitly; its default is not described as strict kernel-only proof.
The bibliography gives source links and notes where documentation is moving
rather than a pinned build.
