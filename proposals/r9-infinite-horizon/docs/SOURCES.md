# Sources and audit boundary

Inspected 15 September 2026. The article contains the conventional bibliography.
Only newly written code and documentation are redistributed in this package.

## Forge (pinned)

Commit: `c98e47c5f804e92880fc1d0e378c1b95832b685c`.

- README: https://github.com/VladimirReshetnikov/Forge/blob/c98e47c5f804e92880fc1d0e378c1b95832b685c/README.md
- Published capability/provenance ledger: https://github.com/VladimirReshetnikov/Forge/blob/c98e47c5f804e92880fc1d0e378c1b95832b685c/article/sections/B-provenance.tex
- Conclusion and declared gaps: https://github.com/VladimirReshetnikov/Forge/blob/c98e47c5f804e92880fc1d0e378c1b95832b685c/article/sections/12-conclusion.tex
- Leant/Djex integration review: https://github.com/VladimirReshetnikov/Forge/blob/c98e47c5f804e92880fc1d0e378c1b95832b685c/docs/IDEAS-FROM-LEANT-DJEX.md

GitHub connector reads supplied the published material. The recursive tree was
also inspected, and targeted searches for pushdown/probabilistic topics returned
no results. These searches are not proofs of absence. An attempted container git
clone failed because the host could not be resolved; it was not an exhaustive
local-file audit. The novelty claim is relative to the inspected merged design
and its capability/provenance ledger, not every file in all frozen proposals.

## Neighboring synthesis projects

- Leant README: https://github.com/VladimirReshetnikov/Leant/blob/main/README.md
- Djex README: https://github.com/VladimirReshetnikov/Djex/blob/main/README.md
  Inspected README blob `12fec0edf075937f2eb42125e800845a480d4b76`, first 140 lines.

These were interface/status reads, not live synthesis runs or a full code review.
No dependency pin, acceptance result or open synthesis problem from those projects
is claimed as an experimental result of this package.

## Classical algorithms

Arnaud Carayol and Matthew Hague, *Saturation algorithms for model-checking
pushdown systems*, EPTCS 151 (2014), 1–24. DOI 10.4204/EPTCS.151.1.
https://arxiv.org/abs/1405.5593

Krishnendu Chatterjee and Monika Henzinger, *An O(n²) Time Algorithm for Alternating
Büchi Games*, IST-2011-0009, 11 July 2011.
https://research-explorer.ista.ac.at/download/5379/5504/IST-2011-0009_IST-2011-0009.pdf
The prototype uses the classical repeated-attractor algorithm discussed in the
preliminaries, with a deliberately simpler scan implementation. It does not
implement the paper's O(n²) algorithm.

## Lean and candidate libraries

- Lean grind reference: https://lean-lang.org/doc/reference/latest/The--grind--tactic/
- Mathlib DFA source, inspected at Forge's named Mathlib pin:
  https://github.com/leanprover-community/mathlib4/blob/1cf325a0cf67aca2b04d76b5380ff6a9e410aefa/Mathlib/Computability/DFA.lean
- Mathlib PMF documentation:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Basic.html
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Monad.html
- Mathlib kernel documentation:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Defs.html
- Mathlib index, including Ionescu–Tulcea trajectory modules:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib
- FLINT rational matrix documentation:
  https://flintlib.org/doc/fmpq_mat.html
  The official search result verified the `fmpq_mat_solve` synopsis; direct page
  fetches returned an error. No FLINT installation or API execution was performed.
- Storm official usage documentation:
  https://www.stormchecker.org/documentation/usage/running-storm.html
  Exact-preserving model transport matters: the floating explicit transition-file
  route is not equivalent to exact symbolic-model inputs.
- Spot official description: https://spot.lre.epita.fr/

Except for the explicitly pinned DFA source read, these are documented candidate
integration points, not a tested import set. None is a dependency of the delivered
Python experiment. There is no claim of novel invention of the classical kernels.
