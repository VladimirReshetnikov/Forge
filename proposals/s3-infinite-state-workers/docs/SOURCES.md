# Source ledger

Inspected baseline identities (15 September 2026):

| Repository | Full revision |
|---|---|
| Forge | `58ea206bd7ad501b930add568151217bcc7f82a2` |
| Leant | `6bf05ad78c467989e68290f2d08bbed40802d485` |
| Djex | `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5` |

Forge baseline: Lean v4.34.0; Mathlib
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`.
Leant's reported native Djex dependency is `e237e866`, distinct from the separate
Djex repository head above.

Main Forge inspection paths: README.md; article/sections/06-closure.tex;
article/sections/15-conclusion.tex; article/sections/B-provenance.tex;
lean/Forge/Design/Contracts.lean; lean/Forge/Design/Runtime.lean;
lean/Forge/Closure/Covers.lean. Leant's current commit data supplied the
indexing-composition diagnostic report; Djex's README supplied current synthesis
scope and embedding entry points.

The audit used actual connector-fetched content. Empty code-search responses
were not evidence of absence, because a known positive term also returned no
matches. No exhaustive line-by-line audit of every archived proposal is claimed.

Primary mathematical and software sources, with clickable references and DOIs,
are in `article/references.tex` and the compiled article. They include Abdulla
et al. (2000), Finkel/Schnoebelen (2001), Bojanczyk/Klin/Lasota (2014), Mathlib's
WQO documentation, MinCoverPetri, RaLib, and the 2024 weighted-register-automata
paper. The specialized constructions in the article are proved directly;
classical foundations are attributed rather than claimed as new mathematics.

External applications were researched, not installed or executed. In particular,
MinCoverPetri's documented 127/omega convention requires a numeric-range adapter,
and RaLib's learned models require independent source correspondence proofs.
