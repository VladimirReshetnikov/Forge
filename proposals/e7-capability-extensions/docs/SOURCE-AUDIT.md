# Source-relative audit

Snapshot date: 15 September 2026. Full revisions are in `revisions.json`.
The article bibliography provides exact source URLs and primary literature.

## Reviewed source boundary

The GitHub connector was used for repository inspection, including Forge's
README, tree inventory, structural-search section (in ranges), provenance
appendix, integration section, `docs/IDEAS-FROM-LEANT-DJEX.md`, and runtime
contract. Leant's README and the complete indexing-diagnostics addition in its
current commit were inspected. Djex's tree inventory and canonical rank-N
rules were inspected. The pinned Mathlib `MvPolynomial/Eval.lean` was also read
to anchor the proposed algebra bridge in actual declarations.

This is a focused algorithmic audit of the merged design, not an assertion that
every line of all nine frozen proposals or all neighboring implementation files
was independently reviewed. A missing keyword result is not used as evidence
that a whole repository lacks a feature. The contribution table is grounded in
the documented boundaries and explicit limitations of the inspected sections.

## Material deliberately not repeated as a contribution

- The existing obligation controller, trust profiles, evidence receipts, rollback,
  worker separation, and scope-sensitive identities.
- Induction generalization, demand-driven lemma invention, ordinary tabling,
  arithmetic CEGIS, affine/lattice/residue witnesses, and nonlinear certificates.
- Rank-N or function-valued Church carriers by themselves; Djex and Leant already
  support relevant fragments.
- Generic advice to use a solver only as a proposer and verify its output.

The article refers to that infrastructure only where needed to explain an
extension's inputs, outputs, or acceptance gate.

## Deltas grounded in the sources

| Existing statement | Extension here |
| --- | --- |
| Forge's state-machine prototype checks conservation; general coupled preservation is noted as bilinear. | Compute the greatest stable vector subspace without guessing action matrices jointly; alternatively close a target-generated ideal and derive polynomial multipliers. |
| Leant can find function-valued folds and the indexing step separately, but the original bounded composition query remains unaccepted. | Derive algebra contracts from the residual specification, filter local grammar holes, and perform a compatibility join before assembly. |
| Forge's tabling rejects circular proof dependencies, while induction planning chooses an ordinary induction scheme. | Treat a cyclic graph as an untrusted proof plan; synthesize descent and lower its typed local constructors through well-founded induction. |

These are proposed capabilities relative to the reviewed design, not claims of
new mathematics. The article explicitly credits established refinement synthesis,
polynomial invariant analysis, and cyclic-proof research, including relevant
2026 work. The Python implementations are new code for this package.

## Version and evidence distinctions

Leant's reported Djex dependency `e237e866` is NOT the standalone Djex head
`e8778f4e...` inspected separately. Neither was built in this run. The original
Leant diagnostic's candidate 219 is an ordinal in a separate larger-context
experiment, not an established internal ordinal in the original fold search.
Our finite sketch is not a substitute for that original query.

Forge's README records successful elaboration of three core files. This package
has no Lean elaboration receipt of its own. Those statuses are intentionally
kept separate.

## Concrete libraries

The article gives targeted roles for the pinned Lean/Mathlib API, Python-FLINT
rational linear algebra, Singular change-of-generators facilities, SymPy as a
differential oracle, and optional synthesis/constraint solvers. Only SymPy was
actually exercised as an external library here. Recommending a library does not
claim its adapter has been implemented or tested.
