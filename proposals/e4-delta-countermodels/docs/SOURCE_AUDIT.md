# Focused repository audit

## Pinned references

Forge: `674521027d968d59f7b83220ed52304a85cb55e2`
Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`
Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`

Principal reviewed Forge sources were README, the recursive repository tree,
`article/sections/05-structural.tex`, `article/sections/B-provenance.tex`,
`docs/STATUS.md`, `docs/IDEAS-FROM-LEANT-DJEX.md`, and
`lean/Forge/Design/Runtime.lean`. Leant's pinned `docs/behavioral-synthesis.md`
provided the concrete assertion-checking route. Djex's pinned
`djinn/src-core/Djinn/Internal/LJTFormula.hs` provided the actual formula/atom
representation. The bibliography contains pinned source URLs.

This is not a line-by-line audit of all nine frozen proposal directories or all
Leant/Djex implementations. A GitHub code search returned incomplete results;
it was not treated as proof of absence. A first guessed Djex source path was
unavailable; the actual path was then resolved from the repository tree.

## Exclusions: not claimed as new

The outer obligation controller, acceptance boundary, exact source identity,
certificate-first design, generic invariant synthesis, polynomial cones,
Bernstein/Sturm arithmetic, affine/lattice/residue witnesses, demand-directed
Horn reasoning, and the idea of certifying LJT negative results already appear
in the reviewed material. The package does not reimplement that controller or
repackage these topics as discoveries.

## Actual increment

The reviewed state-machine invariant implementation requires conservation.
The general multiple-invariant formulation acknowledges the bilinear joint
search problem. This package replaces simultaneous guessing with goal-directed
linear closure under payload-coefficient pullbacks. It adds finite control,
arbitrary fresh inputs, a state-affine decision theorem, original-generator
provenance with exact separating-grid trace construction, and executable
search-independent certificates.

The Kripke worker implements a semantic negative certificate rather than an
unsuccessful-search-tree log. Its object-logic scope is narrower than arbitrary
Lean uninhabitance. A source-level translation-completeness theorem is not supplied.

The conceptual mathematics has established precedents (Karr, observable spaces,
register automata, Kripke semantics). No claim of first invention in the
literature is made. Code and proofs in this package are a concrete proposed
Forge increment, not a new installed Forge capability.
