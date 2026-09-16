# Source and review ledger

Repository snapshots, read via the GitHub connector:

- Forge: `c98e47c5f804e92880fc1d0e378c1b95832b685c`
- Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`
- Canonical Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`

Forge material inspected: root README and tree, docs/STATUS.md,
docs/IDEAS-FROM-LEANT-DJEX.md, merged structural and closure material,
lean/Forge/Closure/Covers.lean. Some long tool previews were truncated; the review
is not a line-by-line audit of every frozen proposal. A GitHub code-search query
for `multilinear` reported `incomplete_results: true`; its empty result is not
used to claim exhaustive absence.

The specific baseline already has generic arbitrary-carrier binary-tree cover
induction, unrestricted-word observable closure, finite-carrier covers,
polynomial-ideal closure, and considerable architecture/authority machinery.
This package does not claim any of those as new. Its proposed delta is the
several-child multilinear span constructor, exact CFG matrix restriction,
sibling-conditioned observable quotient, and delivered source/checker evidence.

Forge baseline reports Lean v4.34.0 and Mathlib
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`. These dependencies were not built here.
Leant's inspected diagnostic identifies native Djex dependency `e237e866`, which
is not the same identity as the canonical Djex repository HEAD above.

## Primary external references

- Ines Marušić and James Worrell, *Complexity of Equivalence and Learning for
  Multiplicity Tree Automata*, JMLR 16(76):2465–2500, 2015.
  https://www.jmlr.org/papers/volume16/marusic15a/marusic15a.pdf
  The accessible text supplies the established multilinear/automata background,
  DAG-witness facts, and the distinction between field-operation complexity and
  bit complexity. Screenshot requests failed; no claim depends on unseen figures.
- https://lean-lang.org/doc/reference/latest/The--grind--tactic/
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Multilinear/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/ContextFreeGrammar.html
- https://flintlib.org/doc/fmpq_mat.html
  The FLINT search-indexed official documentation was accessible, while a direct
  open failed. Only the documented rational-matrix representation and canonical
  arithmetic design are used; no FLINT benchmark or installation is claimed.

Current generated Mathlib documentation was inspected for the named interfaces;
compatibility with the pinned Forge target requires actual Lean compilation.

## Canonical diagnostic permalinks

https://github.com/VladimirReshetnikov/Leant/blob/6bf05ad78c467989e68290f2d08bbed40802d485/docs/reports/2026-09-14-indexing-composition-diagnostics.md

https://github.com/VladimirReshetnikov/Djex/blob/e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5/docs/reports/2026-09-14-indexing-composition-diagnostics.md

No original indexing/universe-query acceptance is claimed for this package.
