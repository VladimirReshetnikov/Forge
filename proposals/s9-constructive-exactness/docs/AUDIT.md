# Source audit and scope

Audit date: September 15, 2026. No repository modifications were made.

| Repository | Inspected revision |
|---|---|
| VladimirReshetnikov/Forge | `58ea206bd7ad501b930add568151217bcc7f82a2` |
| VladimirReshetnikov/Leant | `6bf05ad78c467989e68290f2d08bbed40802d485` |
| VladimirReshetnikov/Djex | `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5` |

## Directly inspected material

Forge: README; recursive tree inventory; `docs/STATUS.md`;
`docs/IDEAS-FROM-LEANT-DJEX.md` (opening review and its integration principles);
`article/sections/05-structural.tex` (opening 240 source lines);
`article/sections/15-conclusion.tex` (complete).
Leant and Djex: READMEs, current branch revision metadata.

The merged status register and conclusion summarize 27 original proposals.
This was a targeted review, not a line-by-line inspection of all archived proposals.
Repository searches for homology and Smith returned no results; absence of indexed
hits was NOT treated as proof of absence.

## Reused, not claimed as a new contribution

Integer lattice solving and divisibility obstructions; finite quotients and
commuting diagrams; source-owned typed candidates; negative-evidence discipline;
resource-limited UNKNOWN; certificate replay separated from search. Forge already
contains these ideas. Smith reduction and algebraic cancellation are classical.

## Proposed addition relative to the reviewed capability register

Compatible integral cycle/boundary coordinates; constructive homology
presentations and induced maps; explicit chain reductions with retained f/g/h;
whole-diagram homotopy synthesis; matrix-adjoint non-homotopy receipts; checked
positive witness lifting through reductions. These are one specific worker and
source fragment, not a replacement architecture or a claim of mathematical priority.

## External primary material inspected

- SymPy 1.14.0 source: `sympy/polys/matrices/normalforms.py`, tag `sympy-1.14.0`,
  particularly `smith_normal_decomp`. The actual prototype ran with SymPy 1.14.0.
- Official SymPy DomainMatrix documentation.
- Official Mathlib documentation for `Mathlib.Algebra.Homology.Homotopy` and
  `Mathlib.LinearAlgebra.Matrix.ToLin`. API names were inspected, not compiled.
- Official SageMath integer-matrix documentation: `smith_form` returns D,U,V.
  The Sage alternative was not executed.
- Emil Skoldberg, “Morse theory from an algebraic viewpoint,” Transactions of the
  AMS 358(1), 115–129 (2006), institutional publication record, DOI
  `10.1090/S0002-9947-05-04079-1`. No theorem of mathematical novelty is claimed.

All source links are in the article bibliography. No third-party source trees,
fonts, or compiler binaries are redistributed.
